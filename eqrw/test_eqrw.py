from z3 import *
from eqrw import *
from test_framework import test, run_tests, test_summary, test_print

@test
def test_Equation():
    i, j = Ints('i j')
    eq = Equation(i + 10, j + i)
    assert eq.lhs == i + 10
    assert eq.rhs == j + i
    assert str(eq) == 'i + 10 == j + i'
    assert eq.expr == (i + 10 == j + i)

    eq = Equation(10, i)
    assert eq.lhs == 10
    assert eq.rhs == i
    assert str(eq) == '10 == i'
    assert eq.expr == (10 == i)

    # NOTE: (10 == i) is evaluated as i.__eq__(10), i.e., as i == 10:
    assert str(eq.expr) == "i == 10"
    assert not str(eq.expr) == str(eq)

@test
def test_prove():
    i, j = Ints('i j')
    eq1 = i == j + 100
    eq2 = j == 17
    assert z3_prove(i == 117, eq1, eq2)

    assert not z3_prove(i == 117, eq1)


@test
def test_Proof__init__():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.eq0.expr == (i == j)
    assert p.terms[0] == i


@test
def test_Proof_theorem():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.eq0.expr == (i == j)


@test
def test_Proof_lhs():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.lhs() == i


@test
def test_Proof_rhs():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.rhs() == j


@test
def test_Proof_first():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.first() == i


@test
def test_Proof_last():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.last() == i


@test
def test_num_steps():
    i, j, k = Ints('i j k')
    p = Proof(i, k)
    assert p.num_steps() == 0

    p += j, i == j
    assert p.num_steps() == 1

    p += k, j == k
    assert p.num_steps() == 2


IV = IntVal

@test
def test_add_step():
    i, j = Ints('i j')
    eq1 = i == j + IV(100)
    eq2 = j == IV(17)

    p = Proof(i, j + IV(100))
    p.add_step(eqs = [eq1],
               target = j + IV(100))
    
    assert p.num_steps() == 1
    assert p.is_complete()

    p2 = Proof(j + 100, IV(117))
    assert p2.rhs() == IV(117)
    assert p2.last() == j + 100
    assert not p2.last() == p2.rhs()
    assert not p2.is_complete()

    assert str(IV(17) + IV(100)) == '117'

    p2 += IV(17) + IV(100), eq2
    assert p2.rhs() == IV(117)
    assert p2.last() == IV(17) + IV(100)
    assert str(p2.rhs()) == '117'

    p2 += 117
    assert p2.is_complete()


@test
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

def IV(x): return x
@test
def test_Proof__add__():
    i, j = Ints('i j')
    eq1 = i == j + IV(100)
    eq2 = j == IV(17)

    p1 = Proof(i, j + IV(100))
    p1 += j + IV(100), eq1

    test_print(p1)
    test_print()

    p2 = Proof(j + IV(100), IV(117))
    test_print(p2)
    test_print()
    p2 += IV(17) + IV(100), eq2
    p2 += IV(117)
    test_print(p2)
    test_print()

    p3 = p1 + p2
    assert p3.eq0.expr == (i == IV(117)), f'Fails: {p3.eq0} == {i == IV(117)}'
    test_print(p3)


@test
def test_steps():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert len(list(p.steps())) == 0
    p += 10, i == 10
    assert len(list(p.steps())) == 1
    p += j, j == 10
    assert len(list(p.steps())) == 2


@test
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
    test_print(p1.eq0)

    p2 = Proof(2 * 3 -2 * C/2 + C, 6)
    p2 += 6
    assert p2.is_complete()
    test_print(p2.eq0)

    test_print()
    p = p1 + p2
    test_print(p.eq0)
    test_print(p)

    test_print()
    p1 += p2
    test_print(type(p1))
    test_print(p1)


@test
def test_proof_summary():
    x = Real('x')
    y = Real('y')
    A, B, C = Reals('A B C')

    eq_A = A == 2 * B + C
    eq_B = B == 3 - C/2

    p = Proof(A, 6)
    p += 2 * B + C,             eq_A
    p += 2 * (3 - C/2) + C,     eq_B
    assert not p.is_complete()
    test_print(f'summary of {p.eq0}')
    test_print(p.summary())
    test_print()

    p += 2 * 3 - 2 * C/2 + C
    p += 6 - C + C
    p += 6
    assert p.is_complete(), f'Expected proof of {p.eq0} to be complete.'
    test_print(f'summary of {p.eq0}')
    test_print(p.summary())
    test_print()


@test
def test_EqProof_append():
    a, b, c = Ints('a b c')
    p = EqProof(10)
    p.append(10 + c - c)
    p.append(c + 10, c == 0)
    p.append(a - 91, c == 0, a == 101)

    assert len(p) == 4
    #print(p.eq_proof_str(indent=4))
    #print(p[-1])

@test
def test_EqProof_add():
    a, b, c = Ints('a b c')
    p = EqProof(10)
    p.add(10 + c - c)
    p.add(c + 10, c == 0)
    p.add(a - 91, c == 0, a == 101)

    assert len(p) == 4
    #print(p.eq_proof_str(indent=4))
    #print(p[-1])


@test
def test_EqProof_iadd():
    a, b, c = Ints('a b c')

    t = Theory('th1', {c == 0, a == 101})
    #print(f"Theory {t}:")
    #print("    " + ("\n    ".join(str(eq) for eq in t)))

    assert t[0] == (c == 0)

    assert t.EQ0 == (c == 0)
    assert t.EQ1 == (a == 101)
    
    p = EqProof(10)
    p += 10 + c - c
    p += c + 10, t.EQ0
    p += a - 91, t

    assert len(p) == 4
    print('Proof')
    print(p.eq_proof_str(indent=4))
    #print(p[-1])


@test
def test_Theory():
    a, b, c = Ints('a b c')
    T1 = Theory('T1', [a == 1, b==10])
    T2 = Theory('T2', [b == 10, c == 2])

    assert len(T1) == 2
    assert len(T2) == 2
    assert T1.name == 'T1'
    assert T2.name == 'T2'

    T1_T2 = T1 + T2
    assert T1_T2.name == '(T1+T2)'
    assert len(T1_T2) == 3

run_tests(print_summary_only=True, new_suppress_test_output=True)
print(test_summary())

#run_tests(test_proof_summary, new_suppress_test_output=True)
#print(test_summary())

