from T1_eqt import *
from eqrw import *

class NIProof:

    def __init__(self, v, lhs, rhs):
        self.v = v
        self.eq0 = (lhs, rhs)
        self.base = Proof(substitute(lhs, (self.v, zero)), substitute(rhs, (self.v, zero)))
        v0 = self.v0 = Const(str(v) + '0', Nat)
        self.step = Proof(substitute(lhs, (self.v, succ(v0))), substitute(rhs, (self.v, succ(v0))))
        self.ih = substitute(lhs, (self.v, v0)) == substitute(rhs, (self.v, v0))

    def is_complete(self):
        return self.base.is_complete() and self.step.is_complete()
    
    def theorem(self):
        return self.lhs() == self.rhs()
    
    def lhs(self):
        return self.eq0[0]
    
    def rhs(self):
        return self.eq0[1]

    def __str__(self):
        result = [f'Theorem: {self.lhs()} == {self.rhs()}',
                  'Proof:' if self.is_complete() else 'Partial proof:']
        result += [f'Base: {self.base}']
        result += [f'IH: {self.ih}']
        result += [f'Step: {self.step}']
        return "\n".join(result)

