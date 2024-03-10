from z3 import *
from eqrw import *
from equation import Equation

class TheoryException(EQRWException): pass

class Theory(set):

    def __init__(self, name, equations):

        eqs = []
        errors = []
        for e in equations:
            if isinstance(e, Equation):
                eqs.append(e)
            elif isinstance(e, Expr) and is_eq(e):
                eqs.append(Equation(e))
            else:
                errors.append(e)
        if len(errors)>0:
            raise TheoryException("Not all elements in equations are Equation or 'z3 eq' objects:\n    " +
                                  "\n    ".join(str(e) for e in errors))
        super().__init__(eqs)
        self.name = name
    
    def __str__(self):
        return self.name
    
    def __or__(self, other):
        return Theory(f'({self.name}|{other.name})', super().__or__(other))
    
    def __getitem__(self, i):
        return list(self)[i]
    
    def __getattr__(self, a):
        if a[:2] == 'EQ':
            return self[int(a[2:])]
        else:
            raise AttributeError(f'Theory object has no attribute called {a}')
