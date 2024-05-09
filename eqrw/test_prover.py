from test_framework import *
from pyspec import *
from prover import *

@test
def test_prover():
    p = Prover()

    A = make_z3sort_expression(z3.DeclareSort('A'))
    x,y,z = A.mk_atoms('x, y, z')

    unique_atoms = [a == a for a in A.atoms ] + [ a != b for a in A.atoms for b in A.atoms - {a} ]
    for f in unique_atoms:
        p.add_fact(f)

    assert p.prove(x == x)
    assert p.prove(x != y)
                   
                   
if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)

