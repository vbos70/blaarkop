from test_framework import *
from pyspec import *

@test
def test_op_order():

    A = make_z3sort_expression(z3.DeclareSort('A'))
    
    assert all(op_order.Noop < o for o in { n: op_order[n] for n in op_order if n != 'Noop' }.values())
    
    assert all(op_order.Pow < o for o in { n: op_order[n] for n in op_order if n != 'Noop' and n != 'Pow' }.values())
    
    assert all(op_order.Xor > o for o in { n: op_order[n] for n in op_order if n not in ['And', 'Or', 'Xor'] }.values())

    assert op_order.Add == op_order.Sub

    assert op_order.Mul == op_order.MatMul
    assert op_order.Mul == op_order.TrueDiv
    assert op_order.Mul == op_order.FloorDiv
    assert op_order.Mul == op_order.Mod

    assert op_order.Xor < op_order.Or
    assert op_order.And < op_order.Xor



@test
def test_comparison():
    A = make_z3sort_expression(z3.DeclareSort('A'))

    x,y,z = A.mk_atoms('x, y, z')
 
    e1 = x<y
    assert str(e1) == 'x<y'

    e2 = y<z
    assert str(e2) == 'y<z'

    # Strange behaviour for changed comparisons
    e3 = x<y<z
    assert str(e3) == 'y<z'
    # Python translates 'x<y<z' into the same bytecode as 'x<y and y<z'

@test
def test_add_op():
    A = make_z3sort_expression(z3.DeclareSort('A'))
    x,y,z = A.mk_atoms('x, y, z')

    e = x + y + z
    assert e.assoc_left
    assert e.op == '+'
    assert e.args[0].op == '+'
    assert e.args[1].op is None
    e= x + (y + z)
    assert e.assoc_left
    assert e.op == '+'
    assert e.args[1].op == '+'
    assert e.args[0].op is None

    assert str(x) == 'x'
    assert str((x+y)+z) == 'x+y+z'
    assert str(x+(y+z)) == 'x+(y+z)', str(x+(y+z))


    e = x**y**z
    assert str(e) == 'x**y**z', str(e)

    ops = '+,-,*,/,//,%,**,@,<<,>>,&,^,|,<,<=,==,!=,>=,>'.split(',')
    compare_ops = '<,<=,==,!=,>=,>'.split(',')
    assoc_left = {
        '+': True,
        '-': True,
        '*': True,
        '/': True,
        '//': True,
        '%': True,
        '**': False,
        '@': True,
        '<<': True,
        '>>': True,
        '&': True,
        '^': True,
        '|': True,
        '<': True,
        '<=': True,
        '==': True,
        '!=': True,
        '>=': True,
        '>': True,
    }

    prec = {
        '**': 0,
        '*': 1,
        '@': 1,
        '/': 1,
        '//': 1,
        '%': 1,
        '+': 2,
        '-': 2,
        '<<': 3,
        '>>' : 3,
        '&': 4,
        '^': 5,
        '|': 6,
        '<': 7,
        '<=': 7,
        '==': 7,
        '!=': 7,
        '>=': 7,
        '>': 7

    }
    errors = 0
    for op1 in ops:
        test_print(op1, end=': ')
        for op2 in ops:
            test_print(op2, end=', ')
            if errors > 0:
                continue
            try:
                d = AttrDict(s = f'x{op1}y{op2}z',
                             sl = f'(x{op1}y){op2}z' if op1 not in compare_ops else None,
                             sr = f'x{op1}(y{op2}z)' if op2 not in compare_ops else None)                
                e = eval(d.s)
                el = eval(d.sl) if d.sl is not None else None
                er = eval(d.sr) if d.sr is not None else None

                if el is not None and prec[op1]<prec[op2]:
                    assert str(e) == str(el)
                elif er is not None and prec[op1]>prec[op2]:
                    assert str(e) == str(er)
                else:
                    if el is not None and assoc_left[op1]:
                        assert str(e) == str(el), f'{str(e)}=={str(el)}'
                    elif er is not None:
                        assert str(e) == str(er), f'{str(e)}=={str(el)}'
            except TypeError as te:
                test_print("ERROR:", te)
                test_print(f'ERROR: op1={op1}, op2={op2}')
                test_print(f'{d.s}, {d.sl}, {d.sr}')
                errors += 1
        test_print()


@test
def test_make_z3class():

    A = make_z3sort_expression(z3.DeclareSort('A'))
    a,b,c = A.mk_atoms('a,b,c')
    assert str(a) == 'a'

    e_A = a + b - c
    assert str(e_A) == 'a+b-c'
    assert str(e_A.z3Expr) == 'z3_Sub(z3_Add(a, b), c)', str(e_A.z3Expr)

    B = make_z3sort_expression(z3.DeclareSort('B'))
    d,e,f = B.mk_atoms('d,e,f')

    e_B = d + e + f
    assert str(e_B) == 'd+e+f'
    assert str(e_B.z3Expr) == 'z3_Add(z3_Add(d, e), f)', str(e_B.z3Expr)

    assert issubclass(type(a), A)
    assert not issubclass(type(a), B)
    

    assert str(a+b-c) == str((a+b)-c)
    assert str(a**b**c) == str(a**(b**c))


    assert str(d+e-f) == str((d+e)-f)
    assert str(d**e**f) == str(d**(e**f))

    try:
        assert str(a+(d*f)) == 'e+d*f'
    except TypeError as te:
        assert str(te) == "Operands of + operator have incompatible types: 'a: A_Atom' versus 'd*f: B_Mul'"



if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)
