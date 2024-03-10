from T1_natural_induction import *
from test_framework import *

@test
def inductive_proof():

    p = Const('p', Nat)
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


if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)
