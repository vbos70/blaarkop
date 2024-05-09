from utils import *
from itertools import chain
from process import *
import time


class Prover:

    def __init__(self):
        self.params = AttrDict()
        self.set_timeout(2 * 60) # 2 minutes timeout
        self.facts = []

    def solver(self):
        return self.params.solver()

    def reset_solver(self):
        self.params.solver = z3.Solver()

    def set_timeout_ms(self, t):
        '''Sets the timeout of proof check steps to t milliseconds.'''
        self.params.PROOF_TIMEOUT = t
        z3.set_param(timeout=self.params.PROOF_TIMEOUT)
        self.reset_solver()

    def set_timeout(self, t):
        '''Sets the timeout of proof check steps to t seconds.'''
        self.set_timeout_ms(t * 1000)

    def timeout_ms(self):
        '''Returns the timeout of proof step checks in milliseconds.'''
        return self.params.PROOF_TIMEOUT

    def timeout(self):
        '''Returns the timeout of proof step checks in seconds.'''
        return self.timeout_ms() / 1000


    class ProofException(Exception): pass
    class ProofTimeoutException(ProofException): pass

    def add_fact(self, f):
        self.facts.append(f)

    def prove(self, formula, *eqs):
        ''' Returns True if `formula` can be proven by `solver` 
        using the equations in `*eqs` and the built in z3 laws / axioms.
        Returns False otherwise.
        '''
        s = self.params.solver
        s.push()
        for f in self.facts:
            s.add(f.z3Expr)
        s.add(*(e.z3Expr for e in eqs))
        t0 = time.time()
        result = not (s.check(z3.Not(formula.z3Expr)) == z3.sat)
        t1 = time.time() 
        s.pop()
        if t1 - t0 > self.timeout():
            raise ProofTimeoutException(f"Timeout expired for proof step: {self.timeout()}s < {t1-t0}s")
        return result

