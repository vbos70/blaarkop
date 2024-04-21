from test_framework import *
from pyspec import *

@test
def test_op_order():
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
def test_add_op():
    x = Expression('x')
    y = Expression('y')
    z = Expression('z')

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

    ops = '+,-,*,/,//,%,**,@,&,|,^'.split(',')

    assoc_left = {
        '+': True,
        '-': True,
        '*': True,
        '/': True,
        '//': True,
        '%': True,
        '**': False,
        '@': True,
        '&': True,
        '|': True,
        '^': True
    }

    prec = {
        '+': 2,
        '-': 2,
        '*': 1,
        '/': 1,
        '//': 1,
        '%': 1,
        '**': 0,
        '@': 1,
        '&': 3,
        '|': 5,
        '^': 4
    }
    errors = 0
    for op1 in ops:
        for op2 in ops:
            if errors > 0:
                continue
            try:
                d = AttrDict(s = f'x{op1}y{op2}z',
                             sl = f'(x{op1}y){op2}z',
                             sr = f'x{op1}(y{op2}z)')
                e = eval(d.s)
                el = eval(d.sl)
                er = eval(d.sr)

                if prec[op1]<prec[op2]:
                    assert str(e) == str(el)
                elif prec[op1]>prec[op2]:
                    assert str(e) == str(er)
                else:
                    if assoc_left[op1]:
                        assert str(e) == str(el), f'{str(e)}=={str(el)}'
                    else:
                        assert str(e) == str(er)
            except TypeError as te:
                test_print(te)
                test_print(f'op1={op1}, op2={op2}')
                errors += 1

if __name__ == '__main__':
    run_tests(new_suppress_test_output=False)
