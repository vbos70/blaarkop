from utils import *
from itertools import chain
from process import *
import time

params = AttrDict()

def solver():
    global params
    return params.solver()

def reset_solver():
    global params
    params.solver = z3.Solver()

def set_timeout_ms(t):
    '''Sets the timeout of proof check steps to t milliseconds.'''
    global params
    params.PROOF_TIMEOUT = t
    z3.set_param(timeout=params.PROOF_TIMEOUT)
    params.solver = z3.Solver()

def set_timeout(t):
    '''Sets the timeout of proof check steps to t seconds.'''
    set_timeout_ms(t * 1000)

def timeout_ms():
    '''Returns the timeout of proof step checks in milliseconds.'''
    global params
    return params.PROOF_TIMEOUT

def timeout():
    '''Returns the timeout of proof step checks in seconds.'''
    return timeout_ms() / 1000

if 'solver' not in params:
    set_timeout(2 * 60) # 2 minutes timeout
    reset_solver()


class ProofException(Exception): pass
class ProofTimeoutException(ProofException): pass


def z3_prove(formula, *eqs):
    ''' Returns True if `formula` can be proven by `solver` 
    using the equations in `*eqs` and the built in z3 laws / axioms.
    Returns False otherwise.
    '''
    global params
    s = params.solver
    s.push()
    s.add(*eqs)
    t0 = time.time()
    result = not (s.check(z3.Not(formula)) == z3.sat)
    t1 = time.time() 
    s.pop()
    if t1 - t0 > timeout():
        raise ProofTimeoutException(f"Timeout expired for proof step: {timeout()}s < {t1-t0}s")
    return result



class Theory(AttrDict):
    """Theories represent equational theories with Python dictionaries. 
    Theories have variables, atoms, and axioms."""


    def __init__(self, **kws):
        ''' Create a Theory with the given variables, atoms, and axioms.

        If `kws["variables"]` exists, it shall be a lis of `process.Var` objects 
        representing the theory's variables. Otherwise, the theory has no variables. 

        If `kws["consts"]` exists, it shall be a list of `process.Const` objects
        representing the theory's constants. Otherwise, the theory has no constants.

        Any other element `kws["ax"]` shall be a `process.Equality` object
        representing an process equality axioms with name "ax".

        `Theory` objects are `AttrDict` objetcs and as such allow attribute acess 
        notation to look up values. If `t : Theory`, then

            t.ax == t['ax']  # provided that ax is not a real attribute/method of Theory. 
        '''
        self._variables = None
        if 'variables' in kws:
            raise ProofException("Theory 'variables' are computed automatically and shall not be provided.")
        
        self._constants = None
        if 'constants' in kws:
            raise ProofException("Theory 'constants' are computed automatically and shall not be provided.")
                
        super().__init__(**kws)


    def __add__(self, other):
        t = Theory(**self)
        t.update(other)
        return t
    


    def compute_variables(self):
        return unique(v for eq in self.values()
                      for v in chain (eq.lhs.vars(), eq.rhs.vars()))

    def variables(self):
        '''Returns a list of all variables in this `Theory`.'''
        if self._variables is None:
            self._variables = list(self.compute_variables())
        return self._variables

    def var_names(self):
        '''compute list of process variables names'''
        return [v.name for v in self.variables()]


    def compute_constants(self):
        return unique(c for eq in self.values()
                      for c in chain (eq.lhs.consts(), eq.rhs.consts()))

    def constants(self):
        '''Returns a list of all atoms in this `Theory`.'''
        if self._constants is None:
            self._constants = list(self.compute_constants())
        return self._constants


    def constant_names(self):
        '''compute list of process atoms names'''
        return [a.name for a in self.constants()]

    def __str__(self):
        result = []
        vs = self.var_names()
        if len(vs)>0:
            result.append(f"# Variables\n{', '.join(vs)}")
        ats = self.constant_names()
        if len(ats)>0:
            result.append(f"# Atoms\n{', '.join(ats)}")
        result.append("# Axioms")
        result.extend(f'{ax}: {self[ax]}' for ax in self)
 
        return "\n".join(result)
        

class EqProof():
    def __init__(self, e: Process):
        ''' Create an equational proof starting with `Processcess` `e`.
        Since `e` is the initial step of the proof, its justification is set to `None`.

        If `e` is not of type `Processcess`, an `ProofException` is raised.
        '''
        if not isinstance(e, Process):
            raise ProofException(f"Expected e : Process, got e : {type(e)}")
        
        self.step = [e]
        self.justification = [None]
        

    def verify_step(self, lhs, rhs, *cs):

        equations = []
        variables = []
        action_variables = []
        for c in cs:
            if type(c) == ProcessEquality:
                equations.append(c)
                variables.extend(c.lhs.vars())
                variables.extend(c.rhs.vars())
                variables.extend(c.lhs.actionvars())
                variables.extend(c.rhs.actionvars())

            else:
                raise ProofException(f"ProcessEquality expected, got {c} : {type(c)}")

        z3variables = list(set(v.z3expr for v in variables))
        z3eqs = [z3.ForAll(z3variables, e.z3expr) for e in equations]

        


        try:
            if z3_prove(lhs.z3expr == rhs.z3expr, *z3eqs):
                return True
        except ProofTimeoutException as e:
            raise ProofException(f"<ProofTimeoutError>: Cannot proof {lhs} == {rhs} within {timeout()}s from {', '.join(str(eq) for eq in equations)}") from e
        raise ProofException(f"<ProofError>: Cannot proof {lhs} == {rhs} from {', '.join(str(eq) for eq in equations)}")


    def step_is_valid(self, i=None):
        ''' Checks if step `i` in this proof is valid, meaning it can be proven by z3.

        Returns `True` if z3 can prove step `i`, `False` otherwise.

        If no `i` is given (`i==None`), the last step of the proof is checked.

        An `ProofException` is raised if `i<0` or `i>=len(self)`. 
        '''
        if i is None:
            i = len(self.step)-1
        if i < 0:
            raise ProofException(f"step index shall be at least 0, got {i}")
        if not i < len(self.step):
            raise ProofException(f"step index shall less than the len(self): {len(self.step)}, got {i}")
        if i == 0:
            return True
        return self.verify_step(self.step[i-1], self.step[i], self.justification[i])
    

    def _extend_(self, e, equations):
        '''Extends this proof by Process `e` and justification `equations`.

        Returns `self`.

        Raises a `ProofException` if z3 cannot prove `e` with the justification `equations`.
        '''
        self.verify_step(self.step[-1], e, *equations)
        self.step.append(e)
        self.justification.append(equations)
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

    # def __getitem__(self, i):
    #     if type(i) == slice:
    #         result = EqProof(self[i.start])
    #         result.step = self.step[i]
    #         result.justification = self.justification[i]
    #         return result
    #     return EqProof(self.step[i])
    
    def __len__(self):
        return len(self.step)

    def __str__(self):
        return self.eq_proof_str()