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
    test_print(p)

run_tests()
