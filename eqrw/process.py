from z3 import *

from enum import Enum

class ProcessException(Exception): pass

ProcessType = Enum('ProcessType', 'Action Const Seq Alt Merge CMerge LMerge')
ProcessRepr = {
    # process prefix constructors
    ProcessType.Action: 'Action',
    ProcessType.Const: 'Const',
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


class Process:

    def __init__(self, proc_type, *sub_procs):
        self.proc_type = proc_type
        self.sub_procs = sub_procs
        
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
        if self.proc_type == ProcessType.Action:
            return str(self.sub_procs[0])
        if self.proc_type == ProcessType.Const:
            return str(self.sub_procs[0])
        elif self.proc_type == ProcessType.CMerge:
            return f"cmerge({self.sub_procs[0]}, {self.sub_procs[1]})"
        elif self.proc_type == ProcessType.LMerge:
            return f"lmerge({self.sub_procs[0]}, {self.sub_procs[1]})"
        else:
            sub_proc_strs = [parenthesize_process_in_context(sp, self, strict=True) for sp in self.sub_procs]
            return sub_proc_strs[0] + f' {ProcessRepr[self.proc_type]} ' + sub_proc_strs[1]

            
def const_process(nm):
    return Process(ProcessType.Const, nm)

delta = const_process('delta')

empty = const_process('empty')

class Action(Process):

    def __init__(self, a):
        '''Returns an Action(a) : Process '''
        super().__init__(ProcessType.Action, a)
        
    def __str__(self):
        return str(self.sub_procs[0])
    
class Const(Process):

    def __init__(self, a):
        '''Returns an Const(a) : Process '''
        super().__init__(ProcessType.Const, a)
        
    def __str__(self):
        return f"Const({str(self.sub_procs[0])})"
    
    
class Seq(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Seq, x, y)

    #def __str__(self):
    #    return parenthesize_process_in_context(self.sub_procs[0], self) + " * " + parenthesize_process_in_context(self.sub_procs[1], self)
    
class Alt(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Alt, x, y)
        
    #def __str__(self):
    #    return parenthesize_process_in_context(self.sub_procs[0], self) + " + " + parenthesize_process_in_context(self.sub_procs[1], self)
    
class Merge(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.Merge, x, y)
        
    #def __str__(self):
    #    return parenthesize_process_in_context(self.sub_procs[0], self) + " | " + parenthesize_process_in_context(self.sub_procs[1], self)
    
class CM(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.CMerge, x, y)
        
    def __str__(self):
        return f"CM({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"


class LM(Process):
    def __init__(self, x, y):
        super().__init__(ProcessType.LMerge, x, y)
        
    def __str__(self):
        return f"LM({str(self.sub_procs[0])}, {str(self.sub_procs[1])})"
