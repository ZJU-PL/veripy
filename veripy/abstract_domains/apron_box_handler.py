import copy

from veripy.abstract_domains.abstract_domain_handler import AbstractDomainHandler
from veripy.interpreter.expr_cons import LinearConstraint, LinearExpr, Op

from apronpy.box import PyBox, PyBoxDManager
from apronpy.coeff import PyDoubleScalarCoeff
from apronpy.environment import PyEnvironment
from apronpy.interval import PyDoubleInterval
from apronpy.lincons0 import ConsTyp
from apronpy.lincons1 import PyLincons1, PyLincons1Array
from apronpy.linexpr1 import PyLinexpr1
from apronpy.var import PyVar


class BoxState:
    def __init__(self, box, var_set):
        super().__init__()
        self.box = box
        self.var_set = var_set

class ApronBoxDomain(AbstractDomainHandler[BoxState]):
    ##
    ## Helper functions
    ##
    def _add_var(self, state, var):
        pyvar = PyVar(var)

        # If var already there, then return
        if pyvar in state.box.environment:
            return state
        
        state.box.environment = state.box.environment.add(real_vars=[pyvar])
        state.box = state.box.forget([pyvar])
        state.var_set.add(var)

        return state

    def _linexpr_to_apron_linexpr(self, env, linexpr:LinearExpr):
        expr = PyLinexpr1(env)

        for var, coeff in linexpr.coeffs.items():
            pyvar = PyVar(var)
            expr.set_coeff(pyvar, PyDoubleScalarCoeff(coeff))
        
        expr.set_cst(PyDoubleScalarCoeff(linexpr.offset))

        return expr

    def _lincons_to_apron_lincons_array(self, env, lincons:LinearConstraint):
        expr = PyLinexpr1(env)

        is_neg = False
        op = lincons.op

        if op == Op.LE:
            is_neg = True
            op = Op.GE
        elif op == Op.LT:
            is_neg = True
            op = Op.GT
    
        for var, coeff in lincons.expr.coeffs.items():
            pyvar = PyVar(var)
            expr.set_coeff(pyvar, PyDoubleScalarCoeff(coeff * (-1 if is_neg else 1)))
        
        expr.set_cst(PyDoubleScalarCoeff(lincons.expr.offset * (-1 if is_neg else 1)))

        op_to_apron_op_map = {
            Op.EQ : ConsTyp.AP_CONS_EQ,
            Op.GE : ConsTyp.AP_CONS_SUPEQ,
            Op.GT : ConsTyp.AP_CONS_SUP,
            Op.NE : ConsTyp.AP_CONS_DISEQ
        }

        return PyLincons1Array([PyLincons1(op_to_apron_op_map[op], expr)])

    def _merge_state_environments(self, state1:BoxState, state2:BoxState):
        box1 = state1.box
        box2 = state2.box
        all_vars = list(set(state1.var_set) | set(state2.var_set))

        all_pyvars = [PyVar(v) for v in all_vars]
        box1.environment = box1.environment.add(real_vars=[v for v in all_pyvars if v not in box1.environment])
        box2.environment = box2.environment.add(real_vars=[v for v in all_pyvars if v not in box2.environment])

    ##
    ## Main functions
    ##
    def get_init_state(self, init_state_config) -> BoxState:
        if init_state_config is None:
            return BoxState(PyBox.top(PyBoxDManager(), PyEnvironment()), set())

        state = BoxState(PyBox.top(PyBoxDManager(), PyEnvironment()), set())
        for var, bounds in init_state_config.items():
            state = self._add_var(state, var)
            new_box = PyBox(state.box.manager, state.box.environment, variables=[PyVar(var)], intervals=[PyDoubleInterval(bounds[0], bounds[1])])
            state.box = state.box.meet(new_box)

        return state

    def print_state(self, state:BoxState):
        print(" | ".join(f"{v} -> {state.box.bound_variable(PyVar(v))}" for v in state.var_set))

    def copy_state(self, state:BoxState):
        return copy.deepcopy(state)

    def are_states_equal(self, state1:BoxState, state2:BoxState):
        if state1.var_set != state2.var_set:
            return False

        for k in state1.var_set:
            if state1.box.bound_variable(PyVar(k)) != state2.box.bound_variable(PyVar(k)):
                return False

        return True

    def assign_linexpr(self, state:BoxState, var, linexpr:LinearExpr):
        expr = self._linexpr_to_apron_linexpr(state.box.environment, linexpr)
        state = self._add_var(state, var)
        state.box = state.box.assign(PyVar(var), expr)

    def meet_lincons(self, state, lincons:LinearConstraint):
        cons_arr = self._lincons_to_apron_lincons_array(state.box.environment, lincons)
        state.box = state.box.meet(cons_arr)

    def join(self, state1:BoxState, state2:BoxState):
        # Merge state environments
        self._merge_state_environments(state1, state2)

        # Now join safely
        box1 = state1.box
        box2 = state2.box
        all_vars = list(set(state1.var_set) | set(state2.var_set))
        joined_box = box1.join(box2)

        return BoxState(joined_box, set(all_vars))

    def widen(self, state1:BoxState, state2:BoxState):
        # Merge state environments
        self._merge_state_environments(state1, state2)

        # Now widen safely
        box1 = state1.box
        box2 = state2.box
        all_vars = list(set(state1.var_set) | set(state2.var_set))
        widened_box = box1.widening(box2)

        return BoxState(widened_box, set(all_vars))