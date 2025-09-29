import copy

from enum import Enum

from veripy.abstract_domains.abstract_domain_handler import AbstractDomainHandler
from veripy.interpreter.expr_cons import LinearConstraint, LinearExpr, Op

##
## Elina Python Imports
##
from elina_abstract0 import *
from elina_dimension import *
from elina_lincons0 import *
from elina_tcons import *
from elina_texpr0 import *
from elina_scalar import *
from opt_oct import *
from opt_zones import *

class ElinaDomain(Enum):
    """
    Class to list all possible supported domains from the ELINA library.
    """
    OCT = "oct"
    ZONES = "zones"

    @classmethod
    def from_value(cls, value):
        for item in cls:
            if item.value == value:
                return item
        raise ValueError(f"{value} is not a valid {cls.__name__}")

class ElinaState:
    """
    Class to capture the state during the abstract interpretation analysis.
    """
    def __init__(self, elina_obj, var_dim_map):
        super().__init__()
        self.elina_obj = elina_obj
        self.var_dim_map = var_dim_map

class ElinaDomainHandler(AbstractDomainHandler[ElinaState]):
    ##
    ## Helper functions
    ##
    def _get_elina_man(self, elina_domain):
        if elina_domain == ElinaDomain.OCT:
            return opt_oct_manager_alloc()
        elif elina_domain == ElinaDomain.ZONES:
            return opt_zones_manager_alloc()
        else:
            raise ValueError(f"No manager defined for elina domain {elina_domain}")

    def __init__(self, domain_name, use_elina_linexprs = False):
        self.elina_domain = ElinaDomain.from_value(domain_name)
        self.elina_man = self._get_elina_man(self.elina_domain)
        self.use_elina_linexprs = use_elina_linexprs

    def _use_elina_linexprs(self):
        # Use elina linexpr if the flag is set and the domain is not Zones
        # (Elina zones do not support linear expressions)
        return self.use_elina_linexprs and self.elina_domain != ElinaDomain.ZONES

    def _get_dimensions(self, state:ElinaState):
        dim = elina_abstract0_dimension(self.elina_man, state.elina_obj)
        assert(dim.realdim == 0) # We currently only handle integer vars
        return dim.intdim

    def _add_dimension(self, state:ElinaState, dims):
        if dims <= 0:
            return

        # Create the dimchange object and add the dimension
        dimchange = elina_dimchange_alloc(dims, 0)
        for i in range(dims):
            dimchange.contents.dim[i] = self._get_dimensions(state)

        state.elina_obj = elina_abstract0_add_dimensions(self.elina_man, False, state.elina_obj, dimchange, False)

        elina_dimchange_free(dimchange)

    def _get_var_dim(self, state:ElinaState, var):
        if var in state.var_dim_map:
            # Easier case when the variable is already present in the state
            return ElinaDim(state.var_dim_map[var])
        
        # If the var is not there, then add the dimension and update the mapping
        new_dim = len(state.var_dim_map)
        self._add_dimension(state, 1)
        state.var_dim_map[var] = new_dim

        return ElinaDim(new_dim)

    def _merge_state_environments(self, state1:ElinaState, state2:ElinaState):
        """
        When calling operations like join on two states, we need to first
        "merge" the environments, i.e. make the variables common and in the
        same order in both the states.
        """
        def get_reorder_permutation(all_vars, old_var_dim_map, new_var_dim_map):
            perm = elina_dimperm_alloc(len(all_vars))
            dim_already_assigned = set()
            dim_places_assigned = set()
            
            for var, dim in old_var_dim_map.items():
                # Map the old dim of var to new position as in new_var_dim_map
                new_ind = new_var_dim_map[var]
                perm.contents.dim[dim] = new_ind
                dim_already_assigned.add(dim)
                dim_places_assigned.add(new_ind)

            # For the unassigned dimension, find the non-assigned indices
            counter = 0
            for i in range(len(all_vars)):
                if i in dim_already_assigned:
                    continue
                
                while (counter in dim_places_assigned):
                    counter += 1
            
                perm.contents.dim[i] = counter
                counter += 1
                
            return perm

        # Collect all possible variables
        all_vars = set()
        for v in state1.var_dim_map:
            all_vars.add(v)
        for v in state2.var_dim_map:
            all_vars.add(v)

        # Add the extra dimensions
        self._add_dimension(state1, len(all_vars) - len(state1.var_dim_map))
        self._add_dimension(state2, len(all_vars) - len(state2.var_dim_map))
        
        # Create a fresh map
        new_var_dim_map = dict()
        for i, var in enumerate(all_vars):
            new_var_dim_map[var] = i

        # Get the permutations to reorder and align variable dimensions
        perm_1 = get_reorder_permutation(all_vars, state1.var_dim_map, new_var_dim_map)
        perm_2 = get_reorder_permutation(all_vars, state2.var_dim_map, new_var_dim_map)

        # Update state1
        state1.elina_obj = elina_abstract0_permute_dimensions(self.elina_man, False, state1.elina_obj, perm_1)
        state1.var_dim_map = new_var_dim_map

        # Update state2
        state2.elina_obj = elina_abstract0_permute_dimensions(self.elina_man, False, state2.elina_obj, perm_2)
        state2.var_dim_map = new_var_dim_map

        return new_var_dim_map

    def _linexpr_to_elina_linexpr(self, linexpr:LinearExpr, var_dim_map, multiplier = 1):
        # Create the empty linexpr
        size = len(linexpr.coeffs)
        elina_linexpr = elina_linexpr0_alloc(ElinaLinexprDiscr.ELINA_LINEXPR_SPARSE, size)

        # Populate with the (v, c) pairs
        for i, (var, coeff_val) in enumerate(linexpr.coeffs.items()):
            linterm = pointer(elina_linexpr.contents.p.linterm[i])
            linterm.contents.dim = ElinaDim(var_dim_map[var])
            coeff = pointer(linterm.contents.coeff)
            elina_scalar_set_double(coeff.contents.val.scalar, multiplier * coeff_val)
        
        # Set the constant
        cst = pointer(elina_linexpr.contents.cst)
        elina_scalar_set_int(cst.contents.val.scalar, multiplier * linexpr.offset)

        return elina_linexpr
    
    def _lincons_to_elina_lincons_array(self, lincons:LinearConstraint, var_dim_map):
        multiplier = 1
        op = lincons.op

        if op == Op.LE:
            multiplier = -1
            op = Op.GE
        elif op == Op.LT:
            multiplier = -1
            op = Op.GT

        op_to_elina_op_map = {
            Op.EQ : ElinaConstyp.ELINA_CONS_EQ,
            Op.GE : ElinaConstyp.ELINA_CONS_SUPEQ,
            Op.GT : ElinaConstyp.ELINA_CONS_SUP,
            Op.NE : ElinaConstyp.ELINA_CONS_DISEQ
        }

        elina_lincons_arr = elina_lincons0_array_make(1)
        elina_lincons_arr.p[0].linexpr0 = self._linexpr_to_elina_linexpr(lincons.expr, var_dim_map, multiplier)
        elina_lincons_arr.p[0].constyp = op_to_elina_op_map[op]

        return elina_lincons_arr

    def _elina_lincons_array_to_tcons_array(self, elina_lincons_array):
        tcons_arr = elina_tcons0_array_make(elina_lincons_array.size)

        for i in range(elina_lincons_array.size):
            tcons_arr.p[i].texpr0 = elina_texpr0_from_linexpr0(elina_lincons_array.p[i].linexpr0)
            tcons_arr.p[i].constyp = elina_lincons_array.p[i].constyp
            tcons_arr.p[i].scalar = elina_lincons_array.p[i].scalar

        return tcons_arr

    ##
    ## Main functions
    ##
    def get_init_state(self, init_state_config) -> ElinaState:
        if init_state_config is None:
            return ElinaState(elina_abstract0_top(self.elina_man, 0, 0), dict())

        # We do not handle init_state_config yet!!
        assert(False)

    def print_state(self, state:ElinaState):
        print("-------------------------------------------")
        lincons_arr = elina_abstract0_to_lincons_array(self.elina_man, state.elina_obj)
        elina_lincons0_array_print(lincons_arr, None)
        print(state.var_dim_map)
        print("-------------------------------------------")

    def copy_state(self, state:ElinaState) -> ElinaState:
        return ElinaState(elina_abstract0_copy(self.elina_man, state.elina_obj), copy.deepcopy(state.var_dim_map))

    def are_states_equal(self, state1:ElinaState, state2:ElinaState) -> bool:
        return elina_abstract0_is_eq(self.elina_man, state1.elina_obj, state2.elina_obj) and state1.var_dim_map == state2.var_dim_map

    def assign_linexpr(self, state:ElinaState, var, linexpr:LinearExpr):
        # Get the dimension for the variable
        dim = self._get_var_dim(state, var)

        # Get the elina linexpr from the parsed linexpr
        elina_linexpr = self._linexpr_to_elina_linexpr(linexpr, state.var_dim_map)

        if self._use_elina_linexprs():
            state.elina_obj = elina_abstract0_assign_linexpr_array(self.elina_man, False, state.elina_obj,
                                                                   dim, elina_linexpr,
                                                                   1, None)
        else:
            # Get the elina texpr from the elina linexpr
            elina_texpr = elina_texpr0_from_linexpr0(elina_linexpr)

            state.elina_obj = elina_abstract0_assign_texpr_array(self.elina_man, False, state.elina_obj,
                                                                 dim, elina_texpr,
                                                                 1, None)

    def meet_lincons(self, state:ElinaState, lincons:LinearConstraint):
        # Get the elina lincons array from the parsed lincons
        elina_lincons_array = self._lincons_to_elina_lincons_array(lincons, state.var_dim_map)

        if self._use_elina_linexprs():
            # Take the meet with the elina lincons array
            state.elina_obj = elina_abstract0_meet_lincons_array(self.elina_man, False, state.elina_obj, elina_lincons_array)
        else:
            # Get elina tcons array from elina lincons array
            elina_tcons_array = self._elina_lincons_array_to_tcons_array(elina_lincons_array)

            # Take the meet with the elina tcons array
            state.elina_obj = elina_abstract0_meet_tcons_array(self.elina_man, False, state.elina_obj, elina_tcons_array)

    def join(self, state1:ElinaState, state2:ElinaState) -> ElinaState:
        new_var_dim_map = self._merge_state_environments(state1, state2)
        assert(state1.var_dim_map == state2.var_dim_map)

        return ElinaState(elina_abstract0_join(self.elina_man, False, state1.elina_obj, state2.elina_obj),
                                               new_var_dim_map)

    def widen(self, state1:ElinaState, state2:ElinaState) -> ElinaState:
        new_var_dim_map = self._merge_state_environments(state1, state2)
        assert(state1.var_dim_map == state2.var_dim_map)

        return ElinaState(elina_abstract0_widening(self.elina_man, state1.elina_obj, state2.elina_obj),
                                                   new_var_dim_map)