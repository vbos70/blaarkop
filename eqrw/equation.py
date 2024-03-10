from z3 import ExprRef, is_eq, is_expr
from eqrw import EQRWException

class EquationException(EQRWException): pass

class Equation:

    def __init__(self, eq=None, lhs=None, rhs=None):
        if eq is None:
            eq1 = lhs == rhs
        else:
            eq1 = eq
        if not is_eq(eq1):
            if eq is not None:
                raise EquationException(f"z3 equation expected, got non-equation: {eq}")
            else:
                raise EquationException(f"'{lhs} == {rhs}' shall be a z3 equation, but it is Python expression '{eq1}' of type {type(eq1)}")
        self.eq = eq1

    def __hash__(self):
        return hash(self.eq)    

    def __eq__(self, other):
        return self.eq == other.eq
        
    def lhs(self):
        return self.eq.arg(0)
    
    def rhs(self):
        return self.eq.arg(1)
    
    def __str__(self):
        return str(self.eq)
    
