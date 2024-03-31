from utils import *
from itertools import chain
from process import *
from eqrw import z3_prove


class Theory(AttrDict):
    """Theories represent equational theories with Python dictionaries. 
    Theories have variables, atoms, and axioms."""


    def __init__(self, **kws):
        ''' Create a Theory with the given variables, atoms, and axioms.

        If `kws["variables"]` exists, it shall be a lis of `process.Var` objects 
        representing the theory's variables. Otherwise, the theory has no variables. 

        If `kws["atoms"]` exists, it shall be a list of `process.Atom` objects
        representing the theory's atoms. Otherwise, the theory has no atoms.

        Any other element `kws["ax"]` shall be a `process.Equality` object
        representing an process equality axioms with name "ax".

        `Theory` objects are `AttrDict` objetcs and as such allow attribute acess 
        notation to look up values. If `t : Theory`, then

            t.ax == t['ax']  # provided that ax is not a real attribute/method of Theory. 
        '''
        self._variables = None
        if 'variables' in kws:
            self._variables = kws['variables']
            del kws['variables']
        
        self._atoms = None
        if 'atoms' in kws:
            self._atoms = kws['atoms']
            del kws['atoms']
                
        super().__init__(**kws)


    def variables(self):
        '''Returns a list of all variables in this `Theory`.'''
        if self._variables is None:
            vs = []
            for eq in self.values():
                for v in chain(eq.lhs.vars(), eq.rhs.vars()):
                    if v not in vs:
                        vs.append(v)
            self._variables = vs
        return self._variables

    def var_names(self):
        '''compute list of process variables names'''
        return [v.name for v in self.variables()]


    def atoms(self):
        '''Returns a list of all atoms in this `Theory`.'''
        if self._atoms is None:
            ats = []
            for eq in self.values():
                for a in chain(eq.lhs.atoms(), eq.rhs.atoms()):
                    if a not in ats:
                        ats.append(a)
            self._atoms = ats
        return self._atoms


    def atom_names(self):
        '''compute list of process atoms names'''
        return [a.name for a in self.atoms()]

    def __str__(self):
        result = []
        vs = self.var_names()
        if len(vs)>0:
            result.append(f"# Variables\n{', '.join(vs)}")
        ats = self.atom_names()
        if len(ats)>0:
            result.append(f"# Atoms\n{', '.join(ats)}")
        result.append("# Axioms")
        result.extend(f'{ax}: {self[ax]}' for ax in self)
 
        return "\n".join(result)
        

class EqProofException(Exception): pass

class EqProof():
    def __init__(self, e: CoreProcess):
        ''' Create an equational proof starting with `CoreProcess` `e`.
        Since `e` is the initial step of the proof, its justification is set to `None`.

        If `e` is not of type `CoreProcess`, an `EqProofException` is raised.
        '''
        if not isinstance(e, CoreProcess):
            raise EqProofException(f"Expected e : Process, got e : {type(e)}")
        
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
        return z3_prove(self.step[i-1].z3expr == self.step[i].z3expr, [eq.z3expr for eq in self.justification[i]])
    

    def _extend_(self, e, cs):
        '''Extends this proof by Process `e` and justification `*cs`.

        Returns `self`.

        Raises a `ProofException` if z3 cannot prove `e` with the justification `*cs`.
        '''
        equations = []
        variables = []
        for c in cs:
            if type(c) == Theory:
                equations.extend(c.values())
                variables.extend(c.variables())
            elif type(c) == ProcessEquality:
                equations.append(c)
                variables.extend(v for v in c.lhs.vars())
                variables.extend(v for v in c.rhs.vars())
            else:
                raise EqProofException(f"Equation expected, got {c} : {type(c)}")

        z3variables = list(set(v.z3expr for v in variables))
        z3equations = [ForAll(z3variables, e.z3expr) for e in equations]
        step = self.step[-1] == e

        if not z3_prove(step.z3expr, z3equations):
            raise EqProofException(f"Cannot proof {self.step[-1]} == {e} from {', '.join(str(eq) for eq in equations)}")
        self.step.append(e)
        self.justification.append(cs)
        return self


    def __iadd__(self, other):
        '''This defines the in-place `+=` operator for EqProof objects.

        The effect is equal to `self._extend_(other[0], other[1:]).
        '''
        if type(other) is not tuple:
            other = (other,)
        return self._extend_(other[0], other[1:])


    def add(self, e, *cs):
        '''This is equivalent to `self.__iadd__(tuple([e] + cs))`.'''
        return self._extend_(e, cs)


    def append(self, e, *cs):
        '''This is equivalent to `self.__iadd__(tuple([e] + cs))`.'''
        return self._extend_(e, cs)

    def eq_proof_str(self, indent = 0):
        return "\n".join(merge(((" " * indent)+ "  " + str(e) for e in self.step), 
                               ((" " * indent)+"= {" + ", ".join(str(c) for c in cs if not isinstance(c, Theory)) + "}" for cs in self.justification[1:]),
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

    def __str__(self):
        return self.eq_proof_str()