from test_framework import *
from process import *
from process_theory import *

@test
def test_process_theory1():
    x, y, z = vars('x, y, z')

    zero, one = atoms('zero, one')

    TH1 = Theory(
        variables = [x,y,z],

        atoms = [zero, one],

        AX1 = zero * x == zero,
        AX2 = one * x == x,
        AX3 = x * one == x,
        AX4 = x + zero == x,
        AX5 = x + y == y + x,
        AX6 = x + x == x,
        AX7 = (x + y) + x == x + (y + z),
        AX8 = (x * y) * z == x * (y * z),
        AX9 = (x + y) * z == x * z + y * z
        )
    
    # Attributre access for axioms:
    assert TH1.AX1 == TH1['AX1']
    assert TH1.AX2 != TH1['AX1']
    assert len(TH1.variables()) == 3
    assert len(TH1.atoms()) == 2
    test_print(TH1)


@test
def test_proof():
    x, y, z = vars('x, y, z')

    zero, one = atoms('zero, one')

    TH1 = Theory(
        variables = [x,y,z],

        atoms = [zero, one],

        AX1 = zero * x == zero,
        AX2 = one * x == x,
        AX3 = x * one == x,
        AX4 = x + zero == x,
        AX5 = x + y == y + x,
        AX6 = x + x == x,
        AX7 = (x + y) + x == x + (y + z),
        AX8 = (x * y) * z == x * (y * z),
        AX9 = (x + y) * z == x * z + y * z
        )

    prf = EqProof(zero * one)
    prf += zero, TH1.AX1

    test_print(prf.eq_proof_str())

    prf = EqProof(zero * one * one)
    prf += zero * one, TH1.AX1
    prf += zero, TH1.AX1

    test_print(prf.eq_proof_str())



if __name__ == '__main__':
    run_tests(print_summary_only=False, new_suppress_test_output=False)
    print(test_summary())

