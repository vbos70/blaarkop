from enum import Enum
from utils import AttrDict
import z3







class And:

    def __init__(self, *args):
        self.args = args
        try:
            self.z3Expr = z3.And(*(a.z3Expr for a in self.args))
        except z3.z3types.Z3Exception:
            raise TypeError(f"One or more arguments of And does not have the expected boolean type.") from None
        
    def __str__(self):
        return f'And({", ".join(str(a) for a in self.args)})'

class Or:

    def __init__(self, *args):
        self.args = args
        try:
            self.z3Expr = z3.Or(*(a.z3Expr for a in self.args))
        except z3.z3types.Z3Exception:
            raise TypeError(f"One or more arguments of Or does not have the expected boolean type.") from None
        
    def __str__(self):
        return f'Or({", ".join(str(a) for a in self.args)})'


class Implies:

    def __init__(self, *args):
        self.args = args
        try:
            self.z3Expr = z3.Implies(*(a.z3Expr for a in self.args))
        except z3.z3types.Z3Exception:
            raise TypeError(f"One or more arguments of Implies does not have the expected boolean type.") from None
        
    def __str__(self):
        return f'Implies({", ".join(str(a) for a in self.args)})'

class Xor:

    def __init__(self, *args):
        self.args = args
        try:
            self.z3Expr = z3.Xor(*(a.z3Expr for a in self.args))
        except z3.z3types.Z3Exception:
            raise TypeError(f"One or more arguments of Xor does not have the expected boolean type.") from None
        
    def __str__(self):
        return f'Xor({", ".join(str(a) for a in self.args)})'

class Not:

    def __init__(self, a):
        self.a = a
        try:
            self.z3Expr = z3.Not(self.a.z3Expr)
        except z3.z3types.Z3Exception:
            raise TypeError(f"Argument of Not does not have the expected boolean type.") from None
        
    def __str__(self):
        return f'Not({str(self.a)})'


class ForAll:

    def __init__(self, vs, formula):
        self.vs = vs
        self.formula = formula
        try:
            self.z3Expr = z3.ForAll([v.z3Expr for v in vs], formula.z3Expr)
        except z3.z3types.Z3Exception:
            raise TypeError(f"One or more arguments of ForAll does not have the expected type.") from None

    def __str__(self):
        return f'ForAll([{", ".join(str(v) for v in self.vs)}], {str(self.formula)})'


class Exists:

    def __init__(self, vs, formula):
        self.vs = vs
        self.formula = formula
        try:
            self.z3Expr = z3.Exists([v.z3Expr for v in vs], formula.z3Expr)
        except z3.z3types.Z3Exception:
            raise TypeError(f"One or more arguments of Exists does not have the expected type.") from None

    def __str__(self):
        return f'ForAll([{", ".join(str(v) for v in self.vs)}], {str(self.formula)})'





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
    BAnd = 5,
    BXor = 6,
    BOr = 7,
)


def make_z3sort_expression(z3sort):

    if type(z3sort) != z3.z3.SortRef:
        raise TypeError('Invalid type of z3sort argument. Expected type: z3.z3.SortRef')

    sortname = str(z3sort)


    class Z3SortExpressionBase:
        '''Base class of Z3 Sort Expressions. Do not instantiate this class directly. Instead use sub-classes of Expression to create
        specialized Expression objects.'''


        prec = op_order.Noop
        assoc_left = True
        op = None
        z3Sort = z3sort


        def __init__(self, *args):
            self.args = args
            self.z3Expr = None


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
            return op(self, other)
            #if isinstance(other, Z3SortExpression):
            #    return op(self, other)
            #raise TypeError(f"Operands of {op.op} operator have incompatible types: '{str(self)}: {type(self).__name__}' versus '{str(other)}: {type(other).__name__}'")


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
            return self.mk_operator(other, BAnd)

        def __xor__(self, other):
            return self.mk_operator(other, BXor)

        def __or__(self, other):
            return self.mk_operator(other, BOr)


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
    Z3SortExpression.atoms = set()
    

    class Atom(Z3SortExpression):

        def __init__(self, *args):
            super().__init__(*args)
            self.z3Expr = z3.Const(args[0], z3sort)
        
        def __hash__(self):
            return hash(self.z3Expr)

    Atom = type(f'{sortname}_Atom', (Atom,), {})

    def mk_atoms(names: str) -> Atom:
        '''Splits the names string by `,` and creates an Atom for each sub-string. Returns a tuple of the created Atoms.'''
        ats = [Atom(name.strip()) for name in names.split(',')]
        Z3SortExpression.atoms.update(ats)
        return ats if len(ats)>1 else ats[0]

    Z3SortExpression.mk_atoms = mk_atoms

    def mk_BinOp(opname, op_order=op_order.Noop, is_left_assoc=True, symbol=None):
        '''Creates a subclass of Expression. The expression is a an operator and 2 arguments.'''

    
        class BinOpBase(Z3SortExpression):

            prec = op_order
            assoc_left = is_left_assoc
            op = symbol
            z3Func = z3.Function(f'z3_{opname}', z3sort, z3sort, z3sort)
            
            def __init__(self, *args):
                super().__init__(*args)
                try:
                    self.z3Expr = self.z3Func(args[0].z3Expr, args[1].z3Expr)
                except Exception:
                    raise TypeError(f'Arguments of {self.op} have incompatible sorts: {args[0].z3Expr.sort()} and {args[1].z3Expr.sort()}') from None
                
        return type(f'{sortname}_{opname}', (BinOpBase,), {})

    def mk_CmpOp(opname, op_order=op_order.Noop, is_left_assoc=True, symbol=None):
        '''Creates a subclass of Expression. The expression is a a comparison operator and 2 arguments.'''

    
        class CmpOpBase(Z3SortExpression):

            prec = op_order
            assoc_left = is_left_assoc
            op = symbol
            if op == '==':
                z3Func = lambda self, x, y: x == y
            elif op == '!=':
                z3Func = lambda self, x, y: x != y
            else:
                z3Func = z3.Function(f'z3_{opname}', z3sort, z3sort, z3.BoolSort())
            
            def __init__(self, *args):
                super().__init__(*args)
                try:
                    self.z3Expr = self.z3Func(args[0].z3Expr, args[1].z3Expr)
                except Exception:
                    raise TypeError(f'Arguments of {self.op} have incompatible sorts.') from None
                
        return type(f'{sortname}_{opname}', (CmpOpBase,), {})
    
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

    LT = mk_CmpOp(opname='LT', op_order=op_order.LT, is_left_assoc=True,symbol='<')
    LE = mk_CmpOp(opname='LE', op_order=op_order.LE, is_left_assoc=True,symbol='<=')
    EQ = mk_CmpOp(opname='EQ', op_order=op_order.EQ, is_left_assoc=True,symbol='==')
    NE = mk_CmpOp(opname='NE', op_order=op_order.NE, is_left_assoc=True,symbol='!=')
    GE = mk_CmpOp(opname='GE', op_order=op_order.GE, is_left_assoc=True,symbol='>=')
    GT = mk_CmpOp(opname='GT', op_order=op_order.GT, is_left_assoc=True,symbol='>')

    BAnd = mk_BinOp(opname='BAnd', op_order=op_order.BAnd, is_left_assoc=True,symbol='&')
    BXor = mk_BinOp(opname='BXor', op_order=op_order.BXor, is_left_assoc=True,symbol='^')
    BOr = mk_BinOp(opname='BOr', op_order=op_order.BOr, is_left_assoc=True,symbol='|')


    class Function(Z3SortExpression):
        '''Functions with Z3SortExpression as result type.'''

        def __init__(self, name, *sorts):
            '''Create a Function with given name. The argument types are given 
            by *sorts. the result type is Z3SortExpression.'''
            self.name = name
            self.sorts = sorts + (Z3SortExpression,)
            self.z3Expr = z3.Function(name, *(s.z3Sort for s in self.sorts))
            self.prec = op_order.Noop

        def __call__(self, *args):
            return FuncApp(self, *args)
        
        def __str__(self):
            return str(self.name)

    Z3SortExpression.mk_function = Function

    class FuncApp(Z3SortExpression):

        def __init__(self, func, *args):
            self.func = func
            self.args = args
            self.z3Expr = func.z3Expr(*(a.z3Expr for a in self.args))
            self.prec = op_order.Noop

        def __str__(self):
            return f'{str(self.func)}({", ".join(str(a) for a in self.args)})'
        


    return Z3SortExpression

def is_atom(e):
    return e.op is None

def is_binop(e):
    return e.op in set(['+','-','*','@','/','//','%','**','<<','>>','&','^','|'])

def is_cmpop(e):
    return e.op in set(['<','<=','==','!=','>=','>'])

