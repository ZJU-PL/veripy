from abc import ABC, abstractmethod
from typing import TypeVar, Generic
from veripy.interpreter.expr_cons import LinearConstraint, LinearExpr

# Declare a type variable representing your abstract state type
StateT = TypeVar('AbstractState')

class AbstractDomainHandler(ABC, Generic[StateT]):
    @abstractmethod
    def get_init_state(self, init_state_config) -> StateT:
        pass

    @abstractmethod
    def print_state(self, state:StateT):
        pass

    @abstractmethod
    def copy_state(self, state:StateT) -> StateT:
        pass

    @abstractmethod
    def are_states_equal(self, state1:StateT, state2:StateT) -> bool:
        pass

    @abstractmethod
    def assign_linexpr(self, state:StateT, var, linexpr:LinearExpr):
        pass

    @abstractmethod
    def meet_lincons(self, state:StateT, lincons:LinearConstraint):
        pass

    @abstractmethod
    def join(self, state1:StateT, state2:StateT) -> StateT:
        pass

    @abstractmethod
    def widen(self, state1:StateT, state2:StateT) -> StateT:
        pass