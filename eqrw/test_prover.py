from test_framework import *
from pyspec import *
from prover import *

@test
def test_prover():
    p = Prover()

    A = make_z3sort_expression(z3.DeclareSort('A'))
    x,y,z = A.mk_atoms('x, y, z')

    unique_atoms = [ a != b for a in A.atoms for b in A.atoms - {a} ]
    for f in unique_atoms:
        p.add_fact(f)

    assert p.prove(x == x)
    assert p.prove(x != y)

    test_print(str(x + y), str((x+y).z3Expr))
    test_print(str((y==z).z3Expr))
    assert p.prove(x + y == x + z, y == z)

@test
def test_forall():
    p = Prover()

    A = make_z3sort_expression(z3.DeclareSort('A'))
    x,y,z = A.mk_atoms('x, y, z')

    l1 = ForAll([x, y], x + y == y + x)    
    test_print(str(l1))
    assert p.prove(z + y == y + z, l1)
                   
    B = make_z3sort_expression(z3.DeclareSort('B'))
    r,s,t = B.mk_atoms('r, s, t')
    l2 = ForAll([x, y, s], t + s == s + t)    

@test
def test_prove():
    A = make_z3sort_expression(z3.DeclareSort('A'))
    zero, one = A.mk_atoms('zero, one')

    x,y,z = A.mk_atoms('x, y, z')

    l1 = ForAll([x], zero + x == x)
    l2 = ForAll([x], one * x == x)
    l3 = ForAll([x, y], x + y == y + x)
    
    p = Prover()
    assert p.prove(x + zero == x, l3, l1)

@test
def test_prove_sequence():
    A = make_z3sort_expression(z3.DeclareSort('A'))
    zero, one = A.mk_atoms('zero, one')

    x,y,z = A.mk_atoms('x, y, z')

    l1 = ForAll([x], zero + x == x)
    l2 = ForAll([x], one * x == x)
    l3 = ForAll([x, y], x + y == y + x)

    sequence = [
        [x],
        [one * x, l2],
        [one * (one * x), l2]
    ]

    p = Prover()
    assert p.prove(sequence[0][0] == sequence[1][0], sequence[1][1])
    assert p.prove(sequence[1][0] == sequence[2][0], sequence[2][1])
    


if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)

