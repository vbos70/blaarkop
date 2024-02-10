from z3 import *
from eqrw import *

def test_prove():
    i, j = Ints('i j')
    eq1 = i == j + 100
    eq2 = j == 17
    assert prove(i == 117, eq1, eq2)

    assert not prove(i == 117, eq1)

test_prove()

def test_Proof__init__():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.eq0 == (i, j)
    assert p.ts[0] == i

test_Proof__init__()

def test_Proof_theorem():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.theorem() == (i == j)

test_Proof_theorem()

def test_Proof_lhs():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.lhs() == i

test_Proof_lhs()

def test_Proof_rhs():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.rhs() == j

test_Proof_rhs()

def test_Proof_first():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.first() == i

test_Proof_first()

def test_Proof_last():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.last() == i

test_Proof_last()


def test_num_steps():
    i, j, k = Ints('i j k')
    p = Proof(i, k)
    assert p.num_steps() == 0

    p += j, i == j
    assert p.num_steps() == 1

    p += k, j == k
    assert p.num_steps() == 2
    
test_num_steps()


IV = IntVal

def test_Proof__iadd__():
    i, j = Ints('i j')
    eq1 = i == j + IV(100)
    eq2 = j == IV(17)

    p = Proof(i, j + IV(100))
    p += j + IV(100), eq1

    p1 = Proof(i, j + IV(100))
    p1 += j + IV(100), eq1

    p2 = Proof(j + IV(100), IV(117))
    p2 += IV(17) + IV(100), eq2
    p2 += IV(117)

test_Proof__iadd__()

def IV(x): return x
def test_Proof__add__():
    i, j = Ints('i j')
    eq1 = i == j + IV(100)
    eq2 = j == IV(17)

    p1 = Proof(i, j + IV(100))
    p1 += j + IV(100), eq1

    print(p1)
    print()

    p2 = Proof(j + IV(100), IV(117))
    print(p2)
    print()
    p2 += IV(17) + IV(100), eq2
    p2 += IV(117)
    print(p2)
    print()

    p3 = p1 + p2
    assert p3.theorem() == (i == IV(117)), f'Fails: {p3.theorem()} == {i == IV(117)}'
    print(p3)
test_Proof__add__()



def test_proving():

    x = Real('x')
    y = Real('y')
    A, B, C = Reals('A B C')

    eq_A = A == 2 * B + C
    eq_B = B == 3 - C/2

    p = Proof(A, 6)
    p += 2 * B + C,             eq_A
    p += 2 * (3 - C/2) + C,     eq_B
    assert not p.is_complete()
    p += 2 * 3 - 2 * C/2 + C
    p += 6 - C + C
    p += 6
    assert p.is_complete()

    p1 = Proof(A, 2 * 3 -2 * C/2 + C)
    p1 += 2 * 3 - 2 * C/2 + C, eq_A, eq_B
    assert p1.is_complete()
    print(p1.theorem())

    p2 = Proof(2 * 3 -2 * C/2 + C, 6)
    p2 += 6
    assert p2.is_complete()
    print(p2.theorem())

    print()
    p = p1 + p2
    print(p.theorem())
    print(p)

    print()
    p1 += p2
    print(type(p1))
    print(p1)

test_proving()

def test_summary():
    x = Real('x')
    y = Real('y')
    A, B, C = Reals('A B C')

    eq_A = A == 2 * B + C
    eq_B = B == 3 - C/2

    p = Proof(A, 6)
    p += 2 * B + C,             eq_A
    p += 2 * (3 - C/2) + C,     eq_B
    assert not p.is_complete()
    print(f'summary of {p.theorem()}')
    print(p.summary())
    print()

    p += 2 * 3 - 2 * C/2 + C
    p += 6 - C + C
    p += 6
    assert p.is_complete()
    print(f'summary of {p.theorem()}')
    print(p.summary())
    print()
    
test_summary()