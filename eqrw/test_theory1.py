from typing import Any
from eqproof import EqProof
from z3 import *
from test_framework import test, run_tests, test_summary, test_print
from utils import AttrDict

@test
def test_f0():

    n, m = Ints('n m')

    nats = And((n >= 0), (m>=0)) 
    eq1 = n == 1
    eq2 = m == n + 8

    thm = m == 9

    p = EqProof(m)
    p += n + 8, eq2
    p += 1 + 8, eq1
    p += 9



def open_theory(t):
    g = globals()
    old_g = dict(globals())
    for n in t:
        g[n] = t[n]
    return old_g

def close_theory(old_g):
    g = globals()
    g_new = []
    for n in g:
        if n in old_g:
            g[n] = old_g[n]
        else:
            g_new.append(n)
    for n in g_new:
        del g[n]
@test
def test_AttrDict():
    ad = AttrDict(a = 0, b = 1)
    assert ad.a == 0
    assert ad.b == 1


@test
def test_f1():

    n, m = Ints('n m')

    th0 = AttrDict(
        n = Int('n'),
        m = Int('m'),
        nats = And((n >= 0), (m>=0)) ,
        eq1 = n == 1,
        eq2 = m == n + 8)

    thm = th0.m == 9

    p = EqProof(m)
    p += th0.n + 8, th0.eq2
    p += 1 + 8,     th0.eq1
    p += 9


@test
def test_f2():

    n, m = Ints('n m')

    th0 = AttrDict(
        nats = And((n >= 0), (m>=0)) ,
        eq1 = n == 1,
        eq2 = m == n + 8)


    g = open_theory(th0)
    p = EqProof(m)
    p += n + 8, eq2
    p += 1 + 8, eq1
    p += 9
    close_theory(g)

    # Verify the theory names are out of scope.
    try:
        assert nats == None
    except NameError as ne:
        assert str(ne) == "name 'nats' is not defined"


from contextlib import contextmanager

@contextmanager
def push_scope(cur_scope, level=[]):
    try:
        level.append(None)
        indent = '    ' * len(level)
        print(indent + f'with: pushed scope {id(cur_scope)}: {",".join(n for n in cur_scope)}')
        old_g = AttrDict(cur_scope)
        print(indent + f'backup scope: {id(old_g)}: {",".join(n for n in old_g)}')
        yield old_g
    finally:
        print(indent + f'finally: restore scope: {id(old_g)}: {",".join(n for n in old_g)}')
            
                
@test
def test_f3():

    try:
        assert n == 1
    except NameError:
        pass
    print()
    with push_scope(locals()) as prev:
        n = Int('n')
        m = Int('m')
        eq1 = 'undefined'
        assert 'nats' not in locals()
        with push_scope(locals()) as prev:
            nats = And((n >= 0), (m>=0))            
            eq1 = n == 1
            eq2 = m == n + 8
            assert 'eq2' in locals()
            p = EqProof(m)
            p += n + 8, eq2
            p += IntVal(1) + 8, eq1
            p += 9
        del nats
        del eq1
        n = prev.n
        m = prev.n
        eq1 = prev.eq1
        print(",".join(n for n in prev))

    del n
    del m
    del eq1
    print(",".join(n for n in prev))
    assert not 'n' in locals()
    assert not 'nats' in locals()
    test_print(p.eq_proof_str())
    # Verify the theory names are out of scope.
    try:
        assert globals()['nats'] == None, f"Unexpected nats: {nats}"
    except KeyError as ke:
        pass


if __name__ == '__main__':

    run_tests(new_suppress_test_output=False)
    #run_tests(print_summary_only=True, new_suppress_test_output=True)
    print(test_summary())

