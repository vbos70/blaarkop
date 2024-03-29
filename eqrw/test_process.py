from test_framework import *
from process import *

@test
def test_1():        
    p0 = empty
    test_print(p0)

    p1 = delta
    test_print(p1)

    pAll = const_process('@A')
    test_print(pAll)

    p = p0 + p1
    test_print(p)

    q = p0 * p1
    test_print(q)

    test_print(p * q)



def actions(*acts):
    return tuple(Action(x) for x in acts)

@test
def test_2():
    a,b,c = actions(*'abc')

    assert str(a) == 'a'


    p = a*b*c*empty
    assert str(p) == 'a * b * c * empty', f"Error: {str(p)} != a * b * c * empty" 

if __name__ == '__main__':
    run_tests(print_summary_only=False, new_suppress_test_output=True)
    print(test_summary())

