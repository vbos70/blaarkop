from z3 import *
from eqrw import *
from traceback import print_exception

num_tests = 0
num_failed_tests = 0
test_output = []
suppress_test_output = False

def test_print(*args):
    global suppress_test_output
    if not suppress_test_output:
        test_output.extend(list(str(a) for a in args))

def test(func):

    def inner():
        global num_tests
        global num_failed_tests
        global test_output
        print(f'# Test {func.__name__}: ', end='', flush=True)
        try:            
            test_output = []
            num_tests += 1
            func()
            print(f'passed.')
            if len(test_output)>0:
                print("Test output:\n" + "\n".join(test_output))
        except AssertionError as ae:
            num_failed_tests += 1
            print(f'Failed:')
            print_exception(ae, limit=-1)
    return inner

def test_summary():
    global num_tests
    global num_failed_tests
    return f'# Tests: {num_tests}. Passed: {num_tests-num_failed_tests}. Failed: {num_failed_tests}.'        

suppress_test_output = True



@test
def test_prove():
    i, j = Ints('i j')
    eq1 = i == j + 100
    eq2 = j == 17
    assert prove(i == 117, eq1, eq2)

    assert not prove(i == 117, eq1)

test_prove()

@test
def test_Proof__init__():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.eq0 == (i, j)
    assert p.terms[0] == i

test_Proof__init__()

@test
def test_Proof_theorem():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.theorem() == (i == j)

test_Proof_theorem()

@test
def test_Proof_lhs():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.lhs() == i

test_Proof_lhs()

@test
def test_Proof_rhs():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.rhs() == j

test_Proof_rhs()

@test
def test_Proof_first():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.first() == i

test_Proof_first()

@test
def test_Proof_last():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert p.last() == i

test_Proof_last()

@test
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

test_Proof__iadd__()

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
    assert p3.theorem() == (i == IV(117)), f'Fails: {p3.theorem()} == {i == IV(117)}'
    test_print(p3)
test_Proof__add__()


@test
def test_steps():
    i, j = Ints('i j')
    p = Proof(i, j)
    assert len(list(p.steps())) == 0
test_steps()


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
    test_print(p1.theorem())

    p2 = Proof(2 * 3 -2 * C/2 + C, 6)
    p2 += 6
    assert p2.is_complete()
    test_print(p2.theorem())

    test_print()
    p = p1 + p2
    test_print(p.theorem())
    test_print(p)

    test_print()
    p1 += p2
    test_print(type(p1))
    test_print(p1)

test_proving()

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
    test_print(f'summary of {p.theorem()}')
    test_print(p.summary())
    test_print()

    p += 2 * 3 - 2 * C/2 + C
    p += 6 - C + C
    p += 6
    assert p.is_complete(), f'Expected proof of {p.theorem()} to be complete.'
    test_print(f'summary of {p.theorem()}')
    test_print(p.summary())
    test_print()
    
test_proof_summary()

print(test_summary())

