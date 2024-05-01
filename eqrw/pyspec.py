from enum import Enum
from utils import AttrDict

# Future:
# - here is an alternative to define new operators: https://code.activestate.com/recipes/384122/

# See, e.g., https://pythongeeks.org/python-operator-precedence/
op_order = AttrDict(
    Noop = -1, # used for atomic (unstructured) expressions
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
    '''Base class of Expressions. Do not instantiate this class directly. Instead use sub-classes of Expression to create
    specialized Expression objects.'''


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

class Atom(Expression): pass

def mk_atoms(names: str) -> Atom:
    '''Splits the names string by `,` and creates an Atom for each sub-string. Returns a tuple of the created Atoms.'''
    return (Atom(name.strip()) for name in names.split(','))

def BinOp(op_order=op_order.Noop, is_left_assoc=True, symbol=None):
    '''Creates a subclass of Expression. The expression is a an operator and 2 arguments.'''

    class Binop(Expression):

        prec = op_order
        assoc_left = is_left_assoc
        op = symbol
    
    return Binop

Mul = BinOp(op_order=op_order.Mul, is_left_assoc=True, symbol='*')
MatMul = BinOp(op_order=op_order.MatMul, is_left_assoc=True,symbol='@')
TrueDiv = BinOp(op_order=op_order.TrueDiv, is_left_assoc=True,symbol='/')
FloorDiv = BinOp(op_order=op_order.FloorDiv, is_left_assoc=True,symbol='//')
Mod = BinOp(op_order=op_order.Mod, is_left_assoc=True,symbol='%')

Add = BinOp(op_order=op_order.Add, is_left_assoc=True,symbol='+')
Sub = BinOp(op_order=op_order.Sub, is_left_assoc=True,symbol='-')

Pow = BinOp(op_order=op_order.Pow, is_left_assoc=False,symbol='**')

LShift = BinOp(op_order=op_order.LShift, is_left_assoc=True,symbol='<<')
RShift = BinOp(op_order=op_order.RShift, is_left_assoc=True,symbol='>>')

LT = BinOp(op_order=op_order.LT, is_left_assoc=True,symbol='<')
LE = BinOp(op_order=op_order.LE, is_left_assoc=True,symbol='<=')
EQ = BinOp(op_order=op_order.EQ, is_left_assoc=True,symbol='==')
NE = BinOp(op_order=op_order.NE, is_left_assoc=True,symbol='!=')
GE = BinOp(op_order=op_order.GE, is_left_assoc=True,symbol='>=')
GT = BinOp(op_order=op_order.GT, is_left_assoc=True,symbol='>')

And = BinOp(op_order=op_order.And, is_left_assoc=True,symbol='&')
Xor = BinOp(op_order=op_order.Xor, is_left_assoc=True,symbol='^')
Or = BinOp(op_order=op_order.Or, is_left_assoc=True,symbol='|')



def make_sort_expression(sortname):

    op_order = AttrDict(
        Noop = -1, # used for atomic (unstructured) expressions
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


    class SortExpressionBase:
        '''Base class of Expressions. Do not instantiate this class directly. Instead use sub-classes of Expression to create
        specialized Expression objects.'''

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
            if isinstance(other, SortExpression):
                return op(self, other)
            raise TypeError(f"Operands of {op.op} operator have incompatible types: '{str(self)}: {type(self).__name__}' versus '{str(other)}: {type(other).__name__}'")


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


    # Create a SortExpressionBase-subclass with sortname as part of the class name
    SortExpression = type(f'{sortname}_Expression', (SortExpressionBase,), {})
    

    class Atom(SortExpression): pass
    Atom = type(f'{sortname}_Atom', (Atom,), {})

    def mk_atoms(names: str) -> Atom:
        '''Splits the names string by `,` and creates an Atom for each sub-string. Returns a tuple of the created Atoms.'''
        return (Atom(name.strip()) for name in names.split(','))

    SortExpression.mk_atoms = mk_atoms

    def mk_BinOp(opname, op_order=op_order.Noop, is_left_assoc=True, symbol=None):
        '''Creates a subclass of Expression. The expression is a an operator and 2 arguments.'''

        class Binop(SortExpression):

            prec = op_order
            assoc_left = is_left_assoc
            op = symbol
        
        return type(f'{sortname}_{opname}', (Binop,), {})

    Mul = mk_BinOp(opname='Mul', op_order=op_order.Mul, is_left_assoc=True, symbol='*')
    MatMul = mk_BinOp(opname='MatMul', op_order=op_order.MatMul, is_left_assoc=True,symbol='@')
    TrueDiv = mk_BinOp(opname='TrueDiv', op_order=op_order.TrueDiv, is_left_assoc=True,symbol='/')
    FloorDiv = mk_BinOp(opname='FloorDiv', op_order=op_order.FloorDiv, is_left_assoc=True,symbol='//')
    Mod = mk_BinOp(opname='Mod', op_order=op_order.Mod, is_left_assoc=True,symbol='%')

    Add = mk_BinOp(opname='Add', op_order=op_order.Add, is_left_assoc=True,symbol='+')
    Sub = mk_BinOp(opname='Sub', op_order=op_order.Sub, is_left_assoc=True,symbol='-')

    Pow = mk_BinOp(opname='Pow', op_order=op_order.Pow, is_left_assoc=False,symbol='**')

    LShift = mk_BinOp(opname='LShift', op_order=op_order.LShift, is_left_assoc=True,symbol='<<')
    RShift = mk_BinOp(opname='RShift', op_order=op_order.RShift, is_left_assoc=True,symbol='>>')

    LT = mk_BinOp(opname='LT', op_order=op_order.LT, is_left_assoc=True,symbol='<')
    LE = mk_BinOp(opname='LE', op_order=op_order.LE, is_left_assoc=True,symbol='<=')
    EQ = mk_BinOp(opname='EQ', op_order=op_order.EQ, is_left_assoc=True,symbol='==')
    NE = mk_BinOp(opname='NE', op_order=op_order.NE, is_left_assoc=True,symbol='!=')
    GE = mk_BinOp(opname='GE', op_order=op_order.GE, is_left_assoc=True,symbol='>=')
    GT = mk_BinOp(opname='GT', op_order=op_order.GT, is_left_assoc=True,symbol='>')

    And = mk_BinOp(opname='And', op_order=op_order.And, is_left_assoc=True,symbol='&')
    Xor = mk_BinOp(opname='Xor', op_order=op_order.Xor, is_left_assoc=True,symbol='^')
    Or = mk_BinOp(opname='Or', op_order=op_order.Or, is_left_assoc=True,symbol='|')

    return SortExpression

import z3

def make_z3sort_expression(z3sort):

    if type(z3sort) != z3.z3.SortRef:
        raise TypeError('Invalid type of z3sort argument. Expected type: z3.z3.SortRef')

    sortname = str(z3sort)

    op_order = AttrDict(
        Noop = -1, # used for atomic (unstructured) expressions
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


    class Z3SortExpressionBase:
        '''Base class of Z3 Sort Expressions. Do not instantiate this class directly. Instead use sub-classes of Expression to create
        specialized Expression objects.'''

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
            if isinstance(other, Z3SortExpression):
                return op(self, other)
            raise TypeError(f"Operands of {op.op} operator have incompatible types: '{str(self)}: {type(self).__name__}' versus '{str(other)}: {type(other).__name__}'")


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


    # Create a SortExpressionBase-subclass with sortname as part of the class name
    Z3SortExpression = type(f'{sortname}_Z3SortExpression', (Z3SortExpressionBase,), {})
    

    class Atom(Z3SortExpression): pass
    Atom = type(f'{sortname}_Atom', (Atom,), {})

    def mk_atoms(names: str) -> Atom:
        '''Splits the names string by `,` and creates an Atom for each sub-string. Returns a tuple of the created Atoms.'''
        return (Atom(name.strip()) for name in names.split(','))

    Z3SortExpression.mk_atoms = mk_atoms

    def mk_BinOp(opname, op_order=op_order.Noop, is_left_assoc=True, symbol=None):
        '''Creates a subclass of Expression. The expression is a an operator and 2 arguments.'''

        class Binop(Z3SortExpression):

            prec = op_order
            assoc_left = is_left_assoc
            op = symbol
        
        return type(f'{sortname}_{opname}', (Binop,), {})

    Mul = mk_BinOp(opname='Mul', op_order=op_order.Mul, is_left_assoc=True, symbol='*')
    MatMul = mk_BinOp(opname='MatMul', op_order=op_order.MatMul, is_left_assoc=True,symbol='@')
    TrueDiv = mk_BinOp(opname='TrueDiv', op_order=op_order.TrueDiv, is_left_assoc=True,symbol='/')
    FloorDiv = mk_BinOp(opname='FloorDiv', op_order=op_order.FloorDiv, is_left_assoc=True,symbol='//')
    Mod = mk_BinOp(opname='Mod', op_order=op_order.Mod, is_left_assoc=True,symbol='%')

    Add = mk_BinOp(opname='Add', op_order=op_order.Add, is_left_assoc=True,symbol='+')
    Sub = mk_BinOp(opname='Sub', op_order=op_order.Sub, is_left_assoc=True,symbol='-')

    Pow = mk_BinOp(opname='Pow', op_order=op_order.Pow, is_left_assoc=False,symbol='**')

    LShift = mk_BinOp(opname='LShift', op_order=op_order.LShift, is_left_assoc=True,symbol='<<')
    RShift = mk_BinOp(opname='RShift', op_order=op_order.RShift, is_left_assoc=True,symbol='>>')

    LT = mk_BinOp(opname='LT', op_order=op_order.LT, is_left_assoc=True,symbol='<')
    LE = mk_BinOp(opname='LE', op_order=op_order.LE, is_left_assoc=True,symbol='<=')
    EQ = mk_BinOp(opname='EQ', op_order=op_order.EQ, is_left_assoc=True,symbol='==')
    NE = mk_BinOp(opname='NE', op_order=op_order.NE, is_left_assoc=True,symbol='!=')
    GE = mk_BinOp(opname='GE', op_order=op_order.GE, is_left_assoc=True,symbol='>=')
    GT = mk_BinOp(opname='GT', op_order=op_order.GT, is_left_assoc=True,symbol='>')

    And = mk_BinOp(opname='And', op_order=op_order.And, is_left_assoc=True,symbol='&')
    Xor = mk_BinOp(opname='Xor', op_order=op_order.Xor, is_left_assoc=True,symbol='^')
    Or = mk_BinOp(opname='Or', op_order=op_order.Or, is_left_assoc=True,symbol='|')

    return Z3SortExpression

