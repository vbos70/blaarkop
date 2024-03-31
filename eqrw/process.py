from z3 import *

from enum import Enum

Process = DeclareSort('Process')

class ProcessException(Exception): pass

ProcessType = Enum('ProcessType', 'Atom Var Action Seq Alt Merge CMerge LMerge')
ProcessRepr = {
    # process prefix constructors
    ProcessType.Atom: 'Atom',
    ProcessType.Var: 'Var',
    ProcessType.Action: 'Action',
    ProcessType.CMerge: 'cmerge',
    ProcessType.LMerge: 'lmerge',

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
    

#z3Process = Function('z3Process', Process)

class CoreProcess:

    def __init__(self, proc_type, *sub_procs):
        self.z3expr = None#Const(f'Process({",".join(sub_procs)})', Process)
        self.proc_type = proc_type
        self.sub_procs = sub_procs


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
    
    def vars(self):
        if self.proc_type == ProcessType.Var:
            yield self
        for p in self.sub_procs:
            for v in p.vars():
                yield v
        
    def atoms(self):
        if self.proc_type == ProcessType.Atom:
            yield self
        for p in self.sub_procs:
            for a in p.atoms():
                yield a


class Var(CoreProcess):

    def __init__(self, a):
        '''Returns an a : Process '''
        super().__init__(ProcessType.Var)
        self.name = a
        self.z3expr = Const(a, Process)

    def __str__(self):
        return str(self.name)

def ids(xs, f=lambda x: x):
    if ',' in xs:
        xs = (x.strip() for x in xs.split(','))
    return tuple(f(x) for x in xs)

def vars(vs):
    return ids(vs, Var)


class Atom(CoreProcess):

    def __init__(self, a):
        '''Returns an a : Process '''
        super().__init__(ProcessType.Atom)
        self.name = a
        self.z3expr = Const(a, Process)

    def __str__(self):
        return str(self.name)

def atoms(ats):
    return ids(ats, Atom)


zero = Atom('zero')
one = Atom('one')

class Action(CoreProcess):

    def __init__(self, a):
        '''Returns an Action(a) : Process '''
        super().__init__(ProcessType.Action)
        self.name = a
        self.z3expr = Const(a, Process)
       
    def __str__(self):
        return str(self.name)


def actions(acts):
    return ids(acts, Action)


z3Seq = Function('z3Seq', Process, Process, Process)
class Seq(CoreProcess):
    def __init__(self, x, y):
        super().__init__(ProcessType.Seq, x, y)
        self.z3expr = z3Seq(x.z3expr, y.z3expr)

    def __str__(self):
        sub_proc_strs = [parenthesize_process_in_context(self.sub_procs[0], self, strict=True),
                         parenthesize_process_in_context(self.sub_procs[1], self, strict=False)]
        return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]
    

z3Alt = Function('z3Alt', Process, Process, Process)
class Alt(CoreProcess):
    def __init__(self, x, y):
        super().__init__(ProcessType.Alt, x, y)
        self.z3expr = z3Alt(x.z3expr, y.z3expr)

    def __str__(self):
        sub_proc_strs = [parenthesize_process_in_context(self.sub_procs[0], self, strict=True),
                         parenthesize_process_in_context(self.sub_procs[1], self, strict=False)]
        return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]

z3Merge = Function('z3Merge', Process, Process, Process)
class Merge(CoreProcess):
    def __init__(self, x, y):
        super().__init__(ProcessType.Merge, x, y)
        self.z3expr = z3Merge(x.z3expr, y.z3expr)
        
    def __str__(self):
        sub_proc_strs = [parenthesize_process_in_context(self.sub_procs[0], self, strict=True),
                         parenthesize_process_in_context(self.sub_procs[1], self, strict=False)]
        return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]

z3CM = Function('z3CM', Process, Process, Process)
class CM(CoreProcess):
    def __init__(self, x, y):
        super().__init__(ProcessType.CMerge, x, y)
        self.z3expr = z3CM(x.z3expr, y.z3expr)

    def __str__(self):
        return f"CM({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"


z3LM = Function('z3LM', Process, Process, Process)
class LM(CoreProcess):
    def __init__(self, x, y):
        super().__init__(ProcessType.LMerge, x, y)
        self.z3expr = z3LM(x.z3expr, y.z3expr)
        
    def __str__(self):
        return f"LM({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"
