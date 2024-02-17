from eqrw import *
from z3 import *
from test_framework import test, run_tests, test_print

S = DeclareSort('S')

zero = Const('zero', S)
succ = Function('succ', S, S)
add = Function('add', S, S, S)
mul = Function('mul', S, S, S)

x, y = Consts('x y', S)
PA1 = ForAll(x,      add(x, zero) == x)
PA2 = ForAll([x, y], add(x, succ(y)) == succ(add(x, y)))
PA3 = ForAll(x,      mul(x, zero) == zero)
PA4 = ForAll([x, y], mul(x, succ(y)) == add(x, mul(x, y)))


class NIProof:

    def __init__(self, v, lhs, rhs):
        self.v = v
        self.eq0 = (lhs, rhs)
        self.base = Proof(substitute(lhs, (self.v, zero)), substitute(rhs, (self.v, zero)))
        v0 = self.v0 = Const(str(v) + '0', S)
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

@test
def ex2_2_9():
    p = Proof(add(succ(zero), succ(zero)), succ(succ(zero)))
    p += succ(add(succ(zero), zero)), PA2
    p += succ(succ(zero)), PA1
    assert p.is_complete()
    #test_print(p)

@test
def prop2_2_7():

    # Proof of add(zero, p) == p
    # base_eqs: p == zero
    # step_eqs: p == succ(p0),add(zero, p0) == p0

    # base
    p = Const('p', S)
    pr_base = Proof(add(zero, p), p)
    pr_base += add(zero, zero), p == zero  # base
    pr_base += zero,            PA1
    pr_base += p,               p == zero  # base
    assert pr_base.is_complete()

    # induction step, first introduce p0
    p0 = Const('p0', S)
    pr_succ = Proof(add(zero,p), p)
    pr_succ += add(zero, succ(p0)), p == succ(p0)        # IHp
    pr_succ += succ(add(zero, p0)), PA2
    pr_succ += succ(p0),            add(zero, p0) == p0  # IHp0
    pr_succ += p,                   p == succ(p0)        # IHp
    assert pr_succ.is_complete()

@test
def inductive_proof():
    p = Const('p', S)

    ip = NIProof(p, add(zero, p), p)
    assert not ip.is_complete()
    
    ip.base += zero, PA1
    assert ip.base.is_complete()
    assert not ip.is_complete()
    
    ip.step += succ(add(zero, ip.v0)), PA2
    ip.step += succ(ip.v0),            ip.ih
    assert ip.step.is_complete()
    
    assert ip.is_complete()
    print(ip)


run_tests(new_suppress_test_output=False)
