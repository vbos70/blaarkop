from T1_eqt import *
from test_framework import *
from eqrw import *

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
    p = Const('p', Nat)
    pr_base = Proof(add(zero, p), p)
    pr_base += add(zero, zero), p == zero  # base
    pr_base += zero,            PA1
    pr_base += p,               p == zero  # base
    assert pr_base.is_complete()

    # induction step, first introduce p0
    p0 = Const('p0', Nat)
    pr_succ = Proof(add(zero,p), p)
    pr_succ += add(zero, succ(p0)), p == succ(p0)        # IHp
    pr_succ += succ(add(zero, p0)), PA2
    pr_succ += succ(p0),            add(zero, p0) == p0  # IHp0
    pr_succ += p,                   p == succ(p0)        # IHp
    assert pr_succ.is_complete()


if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)
