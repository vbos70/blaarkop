from z3 import *
from equation import Equation
from theory import *
from test_framework import test, run_tests, test_summary, test_print

@test
def test_Theory():
    a, b, c = Ints('a b c')

    T1 = Theory('T1', [a == 1, b==10])
    T2 = Theory('T2', [b == 10, c == 2])

    assert len(T1) == 2
    assert len(T2) == 2
    assert T1.name == 'T1'
    assert T2.name == 'T2'

    T1_T2 = T1 | T2
    assert T1_T2.name == 'union'
    assert str(T1_T2) == 'union(T1,T2)', str(T1_T2)
    assert len(T1_T2) == 4

    assert str(T1_T2.T1[1])  == str(b==10)
    assert str(T1_T2.T1[0]) == str(a == 1)

    assert str(T1_T2[0]) == str(T1[0])
    assert str(T1_T2[1]) == str(T1[1])
    assert str(T1_T2[2]) == str(T2[0])
    assert str(T1_T2[3]) == str(T2[1])

    assert str(T1_T2[0]) == str(T1_T2.T1[0])
    assert str(T1_T2[1]) == str(T1_T2.T1[1])
    assert str(T1_T2[2]) == str(T1_T2.T2[0])
    assert str(T1_T2[3]) == str(T1_T2.T2[1])

if __name__ == '__main__':
    run_tests(print_summary_only=True, new_suppress_test_output=False)
    print(test_summary())

