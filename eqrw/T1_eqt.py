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

@test
def ex2_2_9():
    p = Proof(add(succ(zero), succ(zero)), succ(succ(zero)))
    p += succ(add(succ(zero), zero)), PA2
    p += succ(succ(zero)), PA1
    assert p.is_complete()
    #test_print(p)

@test
def prop2_2_7():

    # base case: p == zero 
    p = Const('p', S)
    pr_base = Proof(add(zero, p), p)
    pr_base += add(zero, zero), p == zero
    pr_base += zero,            PA1
    pr_base += p,               p == zero
    assert pr_base.is_complete()

    # induction: p == succ(p0) and add(zero, p0) == p0
    p0 = Const('p0', S)
    pr_succ = Proof(add(zero,p), p)
    pr_succ += add(zero, succ(p0)), p == succ(p0)
    pr_succ += succ(add(zero, p0)), PA2
    pr_succ += succ(p0),            add(zero, p0) == p0
    pr_succ += p,                   p == succ(p0)
    assert pr_succ.is_complete()


run_tests()
