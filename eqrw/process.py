import z3
from utils import unique
from enum import Enum

ActionSort = z3.DeclareSort('ActionSort')

class Action:

    def __init__(self, name: str):
        self.name = name
        self.z3expr = z3.Const(name, ActionSort)

    def __str__(self):
        return self.name

def ids(xs, f=lambda x: x):
    if ',' in xs:
        xs = (x.strip() for x in xs.split(','))
    return tuple(f(x) for x in xs)

def actions(s):
    return ids(s, Action)

ProcessSort = z3.DeclareSort('Process')

z3_Atom = z3.Function('Atom', ActionSort, ProcessSort)

ProcessType = Enum('ProcessType', 'Const Var RecVar Atom Seq Alt Merge CMerge LMerge Encap Hide')
ProcessRepr = {
    # process prefix constructors
    ProcessType.Const: 'Const',
    ProcessType.Var: 'Var',
    ProcessType.RecVar: 'RecVar',
    ProcessType.Atom: 'Atom',
    ProcessType.CMerge: 'cmerge',
    ProcessType.LMerge: 'lmerge',
    ProcessType.Encap: 'encap',
    ProcessType.Hide: 'hide',

    # process binary infix operators
    ProcessType.Seq: '*',
    ProcessType.Alt: '+',
    ProcessType.Merge: '|'
}



def parenthesize_process_in_context(p, ctx: ProcessType, strict=True):
    ''' Returns a str representation of `p` that is parenthesized if `ctx` is an operator 
    with stronger (`strict==True`)  or stronger-or-equal (`strict==False`) binding power.
    '''
    if p.proc_type.value < ProcessType.Seq.value:
        return str(p)
    elif strict and p.proc_type.value > ctx.proc_type.value:
        return f"({p})"
    elif not strict and p.proc_type.value >= ctx.proc_type.value:
        return f"({p})"
    else:
        return str(p)


class ProcessEquality:

    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
    
    def __str__(self):
        return f'{str(self.lhs)} == {str(self.rhs)}'

    @property
    def z3expr(self):
        return self.lhs.z3expr == self.rhs.z3expr
    

class Process:

    def __init__(self, proc_type, *sub_procs):
        self.z3expr = None
        self.proc_type = proc_type
        self.sub_procs = sub_procs

    def __hash__(self):
        return hash(self.z3expr)
    
    def __eq__(self, other):
        '''Equality == '''
        return ProcessEquality(self, other)

    def __mul__(self, other):
        ''' Seq * '''
        return Seq(self, other)

    def __add__(self, other):
        ''' Alt + '''
        return Alt(self, other)

    def __or__(self, other):
        ''' Merge | '''
        return Merge(self, other)

    def __str__(self):
        return str(self.z3expr)
    

    def enumerate_by_proc_type(self, proc_type):
        if self.proc_type == proc_type:
            yield self
        for p in self.sub_procs:
            yield from p.enumerate_by_proc_type(proc_type)
            
        
    def vars(self):
        yield from unique(self.enumerate_by_proc_type(ProcessType.Var))


    def recvars(self):
        yield from unique(self.enumerate_by_proc_type(ProcessType.RecVar))


    def consts(self):
        yield from unique(self.enumerate_by_proc_type(ProcessType.Const))


    def atoms(self):
        yield from unique(self.enumerate_by_proc_type(ProcessType.Atom))



class Const(Process):

    def __init__(self, a):
        '''Returns an Const_a : Process '''
        super().__init__(ProcessType.Const)
        self.name = a
        self.z3expr = z3.Const("Const_" + a, ProcessSort)

    def __str__(self):
        return str(self.name)

def consts(ats):
    return ids(ats, Const)


class Var(Process):

    def __init__(self, a):
        '''Returns an Var_a : Process '''
        super().__init__(ProcessType.Var)
        self.name = a
        self.z3expr = z3.Const("Var_" + a, ProcessSort)

    def __str__(self):
        return str(self.name)

def vars(vs):
    return ids(vs, Var)


class RecVar(Process):

    def __init__(self, a):
        '''Returns an RecVar_a : Process '''
        super().__init__(ProcessType.RecVar)
        self.name = a
        self.z3expr = z3.Const("RecVar_" + a, ProcessSort)

    def __str__(self):
        return str(self.name)

def recvars(vs):
    return ids(vs, RecVar)


class Atom(Process):

    def __init__(self, a: Action):
        '''Returns an Atom(a) : Process '''
        super().__init__(ProcessType.Atom)
        self.name = a
        self.z3expr = z3_Atom(a.z3expr)
       
    def __str__(self):
        return str(self.name)

def atoms(acts):
    return ids(acts, Atom)

def atomic_actions(s):
    return tuple(Atom(a) for a in actions(s))


z3Seq = z3.Function('z3Seq', ProcessSort, ProcessSort, ProcessSort)
class Seq(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Seq, x, y)
        self.z3expr = z3Seq(x.z3expr, y.z3expr)

    def __str__(self):
        sub_proc_strs = [parenthesize_process_in_context(self.sub_procs[0], self, strict=True),
                         parenthesize_process_in_context(self.sub_procs[1], self, strict=False)]
        return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]
    

z3Alt = z3.Function('z3Alt', ProcessSort, ProcessSort, ProcessSort)
class Alt(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Alt, x, y)
        self.z3expr = z3Alt(x.z3expr, y.z3expr)

    def __str__(self):
        sub_proc_strs = [parenthesize_process_in_context(self.sub_procs[0], self, strict=True),
                         parenthesize_process_in_context(self.sub_procs[1], self, strict=False)]
        return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]

z3Merge = z3.Function('z3Merge', ProcessSort, ProcessSort, ProcessSort)
class Merge(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Merge, x, y)
        self.z3expr = z3Merge(x.z3expr, y.z3expr)
        
    def __str__(self):
        sub_proc_strs = [parenthesize_process_in_context(self.sub_procs[0], self, strict=True),
                         parenthesize_process_in_context(self.sub_procs[1], self, strict=False)]
        return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]

z3CM = z3.Function('z3CM', ProcessSort, ProcessSort, ProcessSort)
class CM(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.CMerge, x, y)
        self.z3expr = z3CM(x.z3expr, y.z3expr)

    def __str__(self):
        return f"CM({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"


z3LM = z3.Function('z3LM', ProcessSort, ProcessSort, ProcessSort)
class LM(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.LMerge, x, y)
        self.z3expr = z3LM(x.z3expr, y.z3expr)
        
    def __str__(self):
        return f"LM({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"

z3Encap = z3.Function('z3Encap', ProcessSort, ProcessSort, ProcessSort)
class Encap(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Encap, x, y)
        self.z3expr = z3Encap(x.z3expr, y.z3expr)
        
    def __str__(self):
        return f"Encap({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"

z3Hide = z3.Function('z3Hide', ProcessSort, ProcessSort, ProcessSort)
class Hide(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Hide, x, y)
        self.z3expr = z3Hide(x.z3expr, y.z3expr)
        
    def __str__(self):
        return f"Hide({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"

