from enum import IntEnum
from collections import namedtuple

def add(d1, d2):
    result = dict(d1)
    for k in d2:
        result[k] = d2[k]
    return result

Processor = IntEnum('Processor', 'P1 P2 P3 P4 P5 P6') 
# IntEnum starts with value 1, so we also give names starting from 1

Job = IntEnum('Job', 'J1 J2 J3 J4 J5')

class State:

    def __init__(self, processors, T0, alloc=None):
        self.processors = processors
        self.T0 = T0
        if alloc is None:
            alloc = {}
        self.cur_alloc = { p : (alloc[p] if p in alloc else None) for p in Processor }

    def configure(self, alloc):
        self.cur_alloc = { p : (alloc if p in alloc else self.cur_alloc)[p] for p in Processor }
        self.T0 += 1

    def __str__(self):
        jstrs = [ j.name if j is not None else "None" for j in self.cur_alloc.values() ]
        pstrs = [ p.name for p in self.cur_alloc.keys() ]
        astr = ", ".join(f"{pname:}:{jname:}" for (pname, jname) in zip(pstrs, jstrs))
        return f"T0: {self.T0:4d}: {astr:}"
            

def job_scheduler(max_steps):

    s = State(processors=[p for p in Processor],
              T0=0,
              alloc=add({Processor(i+1): Job(i+1) for i in range(len(Job))}, {Processor.P6 : Job.J1})
    )
    mirror = Processor.P1
    n = 0
    while n < max_steps:
        print(s)
        n += 1
        if mirror < len(Job):
            mirror += 1
        else:
            mirror = Processor.P1
        s.configure({Processor.P6 : s.cur_alloc[mirror]})
    print(s)
        
        
    
