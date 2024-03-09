from T2_eqt import *
from test_framework import *
from eqrw import *

@test
def ex():
    n = Const('n', S)
    p = Proof(exp(n, succ(zero)), n)
    p += mul(exp(n, zero), n), PA6
    p += mul(succ(zero), n), PA5
    p += n, [mul(succ(zero),n) == n]
    assert p.is_complete()
    test_print(p)


if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)
