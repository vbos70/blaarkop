from enum import Enum
from utils import AttrDict

# Future:
# - here is an alternative to define new operators: https://code.activestate.com/recipes/384122/

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
    LT = 3,
    LE = 3,
    EQ = 3,
    NE = 3,
    GE = 3,
    GT = 3,
    LShift = 4,
    RShift = 4,
    And = 5,
    Xor = 6,
    Or = 7,
)


class Expression:


    prec = op_order.Noop
    is_assoc = True
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

    def __lshift__(self, other):
        return self.mk_operator(other, LShift)
    
    def __rshift__(self, other):
        return self.mk_operator(other, RShift)
    
    def __and__(self, other):
        return self.mk_operator(other, And)

    def __xor__(self, other):
        return self.mk_operator(other, Xor)

    def __or__(self, other):
        return self.mk_operator(other, Or)


    # comparison operators

    def __lt__(self, other):
        return self.mk_operator(other, LT)

    def __le__(self, other):
        return self.mk_operator(other, LE)

    def __eq__(self, other):
        return self.mk_operator(other, EQ)

    def __ne__(self, other):
        return self.mk_operator(other, NE)

    def __ge__(self, other):
        return self.mk_operator(other, GE)

    def __gt__(self, other):
        return self.mk_operator(other, GT)

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


class LShift(Expression):

    prec = op_order.LShift
    assoc_left = True
    is_assoc = False
    op = '<<'

    def __init__(self, x, y):
        super().__init__(x, y)

class RShift(Expression):

    prec = op_order.RShift
    assoc_left = True
    is_assoc = False
    op = '>>'

    def __init__(self, x, y):
        super().__init__(x, y)

class LT(Expression):

    prec = op_order.LT
    assoc_left = True
    is_assoc = False
    op = '<'

    def __init__(self, x, y):
        super().__init__(x, y)

class LE(Expression):

    prec = op_order.LE
    assoc_left = True
    is_assoc = False
    op = '<='

    def __init__(self, x, y):
        super().__init__(x, y)

class EQ(Expression):

    prec = op_order.EQ
    assoc_left = True
    is_assoc = False
    op = '=='

    def __init__(self, x, y):
        super().__init__(x, y)

class NE(Expression):

    prec = op_order.NE
    assoc_left = True
    is_assoc = False
    op = '!='

    def __init__(self, x, y):
        super().__init__(x, y)

class GE(Expression):

    prec = op_order.GE
    assoc_left = True
    is_assoc = False
    op = '>='

    def __init__(self, x, y):
        super().__init__(x, y)

class GT(Expression):

    prec = op_order.GT
    assoc_left = True
    is_assoc = False
    op = '>'

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



