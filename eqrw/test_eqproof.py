from test_framework import *
from theory import Theory
from eqproof import *
from z3 import *

@test
def test_EqProof_append():
    a, b, c = Ints('a b c')
    p = EqProof(IntVal(10))
    p.append(10 + c - c)
    p.append(c + 10, c == 0)
    p.append(a - 91, c == 0, a == 101)

    assert len(p) == 4
    #test_print(p.eq_proof_str(indent=4))
    #test_print(p[-1])

@test
def test_EqProof_add():
    a, b, c = Ints('a b c')
    p = EqProof(IntVal(10))
    p.add(10 + c - c)
    p.add(c + 10, c == 0)
    p.add(a - 91, c == 0, a == 101)

    assert len(p) == 4
    #test_print(p.eq_proof_str(indent=4))
    #test_print(p[-1])


@test
def test_EqProof_iadd():
    a, b, c = Ints('a b c')

    t = Theory('th1', {c == 0, a == 101})
    #test_print(f"Theory {t}:")
    #test_print("    " + ("\n    ".join(str(eq) for eq in t)))

    assert t[0].eq == (c == 0)

    assert t.EQ0.eq == (c == 0)
    assert t.EQ1.eq == (a == 101)
    
    p = EqProof(IntVal(10))
    p += 10 + c - c
    p += c + 10, t.EQ0
    p += a - 91, t

    assert len(p) == 4
    
    test_print(p.eq_proof_str(indent=4))
    #test_print(p[-1])

if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)

