from utils import merge
from eqrw import *
from equation import Equation
from theory import Theory

class EqProofException(EQRWException): pass

class EqProof():
    def __init__(self, e: Expr):
        ''' Create an equational proof starting with `Expr` `e`.
        Since `e` is the initial step of the proof, its justification is set to `None`.

        If `e` is not of type `Expr`, an `EqProofException` is raised.
        '''
        if not isinstance(e, Expr):
            raise EqProofException(f"Expected e : Expr, got e : {type(e)}")
        
        self.step = [e]
        self.justification = [None]
        

    def step_is_valid(self, i=None):
        ''' Checks if step `i` in this proof is valid, meaning it can be proven by z3.

        Returns `True` if z3 can prove step `i`, `False` otherwise.

        If no `i` is given (`i==None`), the last step of the proof is checked.

        An `EqProofException` is raised if `i<0` or `i>=len(self)`. 
        '''
        if i is None:
            i = len(self.step)-1
        if i < 0:
            raise EqProofException(f"step index shall be at least 0, got {i}")
        if not i < len(self.step):
            raise EqProofException(f"step index shall less than the len(self): {len(self.step)}, got {i}")
        if i == 0:
            return True
        return z3_prove(self.step[i-1] == self.step[i], self.justification[i])
    

    def _extend_(self, e, cs):
        equations = []
        for c in cs:
            if type(c) == Theory:
                equations.extend(c)
            elif type(c) == Equation:
                equations.append(c)
            else:
                if not (isinstance(c, Expr) and is_eq(c)):
                    raise EqProofException(f"Equation expected, got {c} : {type(c)}")
                equations.append(Equation(c))

        if not z3_prove(self.step[-1] == e, [c.eq for c in equations]):
            raise EqProofException(f"Cannot proof {self.step[-1]} == {e} from {cs}")
        self.step.append(e)
        self.justification.append(cs)


    def __iadd__(self, other):
        '''Extends this proof by z3 expression `e` and justification `*cs`.

        Returns `self`.

        Raises a `ProofException` if z3 cannot prove `e` with the justification `*cs`.
        '''
        if type(other) is not tuple:
            other = (other,)
        self._extend_(other[0], other[1:])
        return self

    def add(self, e, *cs):
        '''This is equivalent to `self.__iadd__(tuple([e] + cs))`.'''
        self._extend_(e, cs)


    def append(self, e, *cs):
        '''This is equivalent to `self.__iadd__(tuple([e] + cs))`.'''
        self._extend_(e, cs)

    def eq_proof_str(self, indent = 0):
        return "\n".join(merge(((" " * indent)+ "  " + str(e) for e in self.step), 
                               ((" " * indent)+"= {" + ", ".join(str(c) for c in cs) + "}" for cs in self.justification[1:]),
                               fillvalue=''))

    def __getitem__(self, i):
        if type(i) == slice:
            result = EqProof(self[i.start])
            result.step = self.step[i]
            result.justification = self.justification[i]
            return result
        return EqProof(self.step[i])
    
    def __len__(self):
        return len(self.step)

