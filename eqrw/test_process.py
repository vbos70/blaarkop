from test_framework import *
from process import *

@test
def test_1():

    zero, one = consts('zero, one')
    p0 = zero
    test_print(p0)

    p1 = one
    test_print(p1)

    pAll = Action('@A')
    test_print(pAll)

    p = p0 + p1
    test_print(p)

    q = p0 * p1
    test_print(q)

    test_print(p * q)

    e = Encap(zero, zero * one)

@test
def test_2():
    zero, one = consts('zero, one')
    a,b,c = actions('abc')

    assert str(a) == 'a'


    p = a*b*c*one
    assert str(p) == 'a * b * c * one', f"Error: {str(p)} != a * b * c * one" 

    p = a * (b * c)
    assert str(p) == 'a * (b * c)'

    z = Encap(a+b, p)
    assert str(z) == 'Encap(a + b, a * (b * c))', str(z)

    z = Hide(a+b, p)
    assert str(z) == 'Hide(a + b, a * (b * c))', str(z)


@test
def test_eq():
    zero, one = consts('zero, one')
    a,b,c = actions('abc')
    p = a*b*c*one
    eq = p == a*b*c*one
    assert str(eq) == str(p) + ' == ' + str(p)
    
    
if __name__ == '__main__':
    run_tests(print_summary_only=False, new_suppress_test_output=True)
    print(test_summary())

