from test_framework import *
from process import *
from process_theory import *

@test
def test_process_theory1():
    x, y, z = vars('x, y, z')

    zero, one = consts('zero, one')

    TH1 = Theory(
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
    assert len(TH1.variables()) == 3, f'{len(TH1.variables())} != 3'
    assert len(TH1.constants()) == 2
    #test_print(TH1)

@test
def test_process_theory2():
    x, y, z = vars('x, y, z')

    zero, one = consts('zero, one')

    TH1 = Theory(
        AX1 = zero * x == zero,
        AX2 = one * x == x)
    
    TH2 = TH1 + Theory(
        AX3 = x * one == x,
        AX4 = x + zero == x,
        AX5 = x + y == y + x)
    
    TH3 = Theory(
        AX6 = x + x == x,
        AX7 = (x + y) + x == x + (y + z),
        AX8 = (x * y) * z == x * (y * z),
        AX9 = (x + y) * z == x * z + y * z
        ) + TH2
    
    # Attributre access for axioms:
    assert TH3.AX1 == TH3['AX1']
    assert TH3.AX2 != TH3['AX1']
    assert len(TH3.variables()) == 3, f'{len(TH3.variables())} != 3'
    assert len(TH3.constants()) == 2
    #test_print(TH1)


    TH4 = TH3 + Theory(
        AX6 = y + y == y,
        )
    assert str(TH4.AX6) == 'y + y == y'
    assert str(TH3.AX6) == 'x + x == x'
@test
def test_proof():
    x, y, z = vars('x, y, z')

    zero, one = consts('zero, one')

    TH1 = Theory(
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

    #test_print(prf.eq_proof_str())

    prf = EqProof(zero * one * one)
    prf += zero * one, TH1.AX1
    prf += zero, TH1.AX1

    #test_print(prf.eq_proof_str())

@test
def test_timeout():

    blocked, ready = consts('blocked, ready')
    x, y, z = vars('x, y, z')
    xa, xb, xc = actionvars('xa, xb, xc')
    
    TH0 = Theory(
    AX1 = blocked * x == blocked,
    AX2 = ready * x == x,
    AX3 = x * ready == x,
    AX4 = x + blocked == x,
    AX5 = x + y == y + x,
    AX6 = x + x == x,
    AX7 = (x + y) + x == x + (y + z),
    AX8 = (x * y) * z == x * (y * z),
    AX9 = (x + y) * z == x * z + y * z,

    # testing action-variables in axioms
    AX10 = Atom(xa) * ready == Atom(xa) 
    )

    a,b,c = atomic_actions('a, b, c')

    # testing action-variables in proofs
    prf = EqProof(b * (c * ready))
    prf += b *c, TH0.AX10


    # verifying substitution of action-variables fails
    # for non-actions
    try:
        prf = EqProof(b * (ready * ready))
        prf += b *ready, TH0.AX10
    except ProofException as pe:
        assert str(TH0.AX10) in str(pe)
        assert str(b * (ready * ready) == b * ready) in str(pe)

    # create a process p built up from the actions
    p = a * b * (a + b) * c
    q = a * b * (a * c + b * c)

    assert timeout() == 120 # default timeout
    set_timeout(1)
    assert timeout() == 1

    prf = EqProof(p)
    s0 = str(prf)
    try:
        prf += q, TH0.AX9
    except ProofException as pe:
        pass

    # verify that the length of the proof is 1
    # and that the process is p
    assert len(prf.step) == 1
    assert prf.step[0] == p



if __name__ == '__main__':
    run_tests(print_summary_only=False, new_suppress_test_output=False)
    print(test_summary())

