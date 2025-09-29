import ast
from dataclasses import dataclass

from veripy.abstract_domains.abstract_domain_handler import AbstractDomainHandler
from veripy.interpreter.expr_cons import LinearConstraint, LinearExpr, Op
from veripy.interpreter.parser import parse_cons, parse_expr
from veripy.utils import get_function_ast, read_code_from_file


@dataclass
class AbstractInterpreterConfig:
    # Required fields
    domain_handler: AbstractDomainHandler
    
    # Optional fields
    widening_delay: int = 3 # Number of widening free iterations

class AbstractInterpreter(ast.NodeVisitor):
    def __init__(self, config:AbstractInterpreterConfig):
        super().__init__()
        self.config = config
        self._init_state = None
        self._curr_state = None

    def execute(self, code_filename, function_name, init_state_config = None):
        # Parse code and get function
        code = read_code_from_file(code_filename)
        func_ast = get_function_ast(code, function_name)

        return self.execute_on_ast(func_ast, init_state_config)

    def execute_on_ast(self, code_ast, init_state_config = None):
        # Set initial and current state
        self._init_state = self.config.domain_handler.get_init_state(init_state_config)
        self._curr_state = self._init_state

        self.visit(code_ast)

        return self._curr_state
    
    def visit_FunctionDef(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def visit_arg(self, node):
        # Ignore argument nodes completely for now
        pass

    def visit_Assign(self, node):
        var = node.targets[0].id
        expr = parse_expr(node.value)
        if isinstance(expr, LinearExpr):
            self.config.domain_handler.assign_linexpr(self._curr_state, var, expr)

    def visit_While(self, node: ast.While):
        condition = parse_cons(node.test)

        if not isinstance(condition, LinearConstraint):
            raise NotImplementedError("Non-linear cons: " + condition)

        invariant = self.config.domain_handler.copy_state(self._curr_state)
        itr_ctr = 0

        while True:
            # Meet with condition and execute loop body
            self.config.domain_handler.meet_lincons(self._curr_state, condition)
            self.visit(node.body)
            itr_ctr += 1

            # Join with current invariant (and widen if after the widening delay) to get the new invariant
            new_invariant = self.config.domain_handler.join(invariant, self._curr_state)
            if itr_ctr > self.config.widening_delay:
                new_invariant = self.config.domain_handler.widen(invariant, new_invariant)

            if self.config.domain_handler.are_states_equal(invariant, new_invariant):
                # If the new invariant is same as old, we have converged and can break
                break
            else:
                invariant = self.config.domain_handler.copy_state(new_invariant)
                self._curr_state = new_invariant

        # After the invariant is found, the state is (Inv and !B)
        self._curr_state = invariant
        condition.op = Op.negate(condition.op)
        self.config.domain_handler.meet_lincons(self._curr_state, condition)

    def visit_If(self, node):
        condition = parse_cons(node.test)

        if not isinstance(condition, LinearConstraint):
            raise NotImplementedError("Non-linear cons: " + condition)
        
        if_cond_copy = self.config.domain_handler.copy_state(self._curr_state)
        else_cond_copy = self.config.domain_handler.copy_state(self._curr_state)

        # If branch
        self.config.domain_handler.meet_lincons(if_cond_copy, condition)
        self._curr_state = if_cond_copy
        self.visit(node.body)
        if_cond_copy = self.config.domain_handler.copy_state(self._curr_state)

        # Else branch
        condition.op = Op.negate(condition.op)
        self.config.domain_handler.meet_lincons(else_cond_copy, condition)
        self._curr_state = else_cond_copy
        self.visit(node.orelse)
        else_cond_copy = self.config.domain_handler.copy_state(self._curr_state)

        # Join
        self._curr_state = self.config.domain_handler.join(if_cond_copy, else_cond_copy)

    def visit_list(self, node):
        return [self.visit(elt) for elt in node]

    ##
    ## generic_visit is unimplemented so that we know what happens exactly.
    ## The other functions that call generic_visit are set on purpose.
    ##
    def generic_visit(self, node):
        raise NotImplementedError(f"Visit to node type {type(node)} not implemented.")
    
    def visit_Module(self, node: ast.Module):
        return super().generic_visit(node)

    def visit_FunctionDef(self, node: ast.Module):
        return super().generic_visit(node)

    def visit_arguments(self, node: ast.Module):
        return super().generic_visit(node)