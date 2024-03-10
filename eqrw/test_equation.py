from test_framework import *
from equation import *
from z3 import *

@test
def test_Equation():
    i, j = Ints('i j')

    eq1 = Equation(i == j)
    assert eq1.lhs() == i
    assert eq1.rhs() == j

    eq2 = Equation(lhs = i+1, rhs = j - 10)
    assert eq2.lhs() == i+1
    assert eq2.rhs() == j-10

    ee = None
    try:
        _ = Equation()
    except EquationException as r:
        ee = r
    finally:
        assert type(ee) == EquationException, "EquationException was not raised" if ee is None else f"Unexpected exception raised: {ee}"
    
    ee = None
    try:
        _ = Equation(10 == 100)
    except EquationException as r:
        ee = r
    finally:
        assert type(ee) == EquationException, "EquationException was not raised" if ee is None else f"Unexpected exception raised: {ee}"

    try:
        _ = Equation(i+10)
    except EquationException as ee:
        assert str(ee) == f"z3 equation expected, got non-equation: {i+10}"

    try:
        _ = Equation(lhs=IntVal(10), rhs=11-1)
    except EquationException as ee:
        assert str(ee) == f"z3 equatiopn expected, got non-equation: {i+10}"

if __name__ == '__main__':
    run_tests(print_summary_only=True, new_suppress_test_output=True)
    print(test_summary())
