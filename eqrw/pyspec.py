from enum import Enum
from utils import AttrDict


# See, e.g., https://pythongeeks.org/python-operator-precedence/
op_order = AttrDict(
    Noop = -1,
    Pow = 0,
    Mul = 1,
    MatMul = 1,
    TrueDiv = 1,
    FloorDiv = 1,
    Mod = 1,
    Add = 2,
    Sub = 2,
    And = 3,
    Xor = 4,
    Or = 5,
)


class Expression:


    prec = op_order.Noop
    assoc_left = True
    op = None


    def __init__(self, *args):
        self.args = args


    def __str__(self):
        def parenthesize(x, ctx, strict):
            if x.prec == op_order.Noop:
                return str(x)
            if x.prec < ctx.prec:
                return str(x)
            if not strict and x.prec == ctx.prec:
                    return str(x)
            return f'({str(x)})'
         
        if self.op is None:
            return str(self.args[0] if len(self.args)==1 else self.args)
        else:
            args = [ parenthesize(self.args[0], self, not self.assoc_left)
                   , parenthesize(self.args[1], self, self.assoc_left) ]
            return self.op.join(args)


    def mk_operator(self, other, op):
        if isinstance(other, Expression):
            return op(self, other)
        return NotImplemented
    
    def __pow__(self, other):
        return self.mk_operator(other, Pow)

    def __mul__(self, other):
        return self.mk_operator(other, Mul)
    
    def __matmul__(self, other):
        return self.mk_operator(other, MatMul)

    def __truediv__(self, other):
        return self.mk_operator(other, TrueDiv)

    def __floordiv__(self, other):
        return self.mk_operator(other, FloorDiv)

    def __mod__(self, other):
        return self.mk_operator(other, Mod)

    def __add__(self, other):
        return self.mk_operator(other, Add)
    
    def __sub__(self, other):
        return self.mk_operator(other, Sub)

    def __and__(self, other):
        return self.mk_operator(other, And)

    def __xor__(self, other):
        return self.mk_operator(other, Xor)

    def __or__(self, other):
        return self.mk_operator(other, Or)


class Mul(Expression):

    prec = op_order.Mul
    assoc_left = True
    op = '*'

    def __init__(self, x, y):
        super().__init__(x, y)

class MatMul(Expression):

    prec = op_order.MatMul
    assoc_left = True
    op = '@'

    def __init__(self, x, y):
        super().__init__(x, y)

class TrueDiv(Expression):

    prec = op_order.TrueDiv
    assoc_left = True
    op = '/'

    def __init__(self, x, y):
        super().__init__(x, y)

class FloorDiv(Expression):

    prec = op_order.FloorDiv
    assoc_left = True
    op = '//'

    def __init__(self, x, y):
        super().__init__(x, y)

class Mod(Expression):

    prec = op_order.Mod
    assoc_left = True
    op = '%'

    def __init__(self, x, y):
        super().__init__(x, y)

class Add(Expression):

    prec = op_order.Add
    assoc_left = True
    op = '+'

    def __init__(self, x, y):
        super().__init__(x, y)

class Sub(Expression):

    prec = op_order.Sub
    assoc_left = True
    op = '-'

    def __init__(self, x, y):
        super().__init__(x, y)

class Pow(Expression):

    prec = op_order.Pow
    assoc_left = False
    op = '**'

    def __init__(self, x, y):
        super().__init__(x, y)

class And(Expression):

    prec = op_order.And
    assoc_left = True
    op = '&'

    def __init__(self, x, y):
        super().__init__(x, y)

class Xor(Expression):
    
    prec = op_order.Xor
    assoc_left = True
    op = '^'

    def __init__(self, x, y):
        super().__init__(x, y)

class Or(Expression):

    prec = op_order.Or
    assoc_left = True
    op = '|'

    def __init__(self, x, y):
        super().__init__(x, y)



