from z3 import *
from eqrw import *
from equation import Equation
from itertools import chain

class TheoryException(EQRWException): pass

class Theory:

    def __init__(self, name, equations, *subths):

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
        for th in subths:
            if not isinstance(th, Theory):
                raise TheoryException(f"Theory expected, got: {th} : {type(th)}")
            
        self.equations = eqs
        self.name = name
        self.subths = subths # the sub-theories


    def __str__(self):
        if len(self.subths) == 0:
            return self.name
        return self.name + "(" + ",".join(tuple(str(t) for t in self.subths)) + ")"
    

    def __len__(self):
        r = len(self.equations)
        for t in self.subths:
            r += len(t)
        return r
    
    def __or__(self, other):
        return Theory(f'union', [], self, other)
    
    def __getitem__(self, i):
        return list(self)[i]
    
    def __getattr__(self, a):
        for sth in self.subths:
            if a == sth.name:
                return sth
        raise AttributeError(f'Theory object {self.name} has no attribute called {a}')
        
    def __iter__(self):
        return chain(self.equations, chain.from_iterable(self.subths))
    
