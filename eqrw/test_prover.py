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

    test_print(str((x+y).z3Expr))
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
                   
if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)

