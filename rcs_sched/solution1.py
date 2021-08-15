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
        

def prev(p: Processor):
    return Processor(p.value-1) if p.value>1 else Processor(len(Processor))
    
def job_scheduler2(max_steps):
    
    mirror = Processor.P2
    jobs = [j for j in Job ]
    processors = [p for p in Processor if p != mirror]
    pj_tuples = zip(processors, jobs)
    red_job = Job(mirror.value-1 if mirror.value>1 else 5)
    alloc = add({ p : j for (p,j) in pj_tuples}, { mirror: red_job})
    s = State(processors=processors,
              T0=0,
              alloc=alloc
    )
    n = 0
    while n<max_steps:
        print(s, mirror)
        n += 1
        if mirror<len(Processor):
            mirror = Processor(mirror.value + 2)
        else:
            mirror = Processor.P2
            jobs = jobs[1:] + [jobs[0]]
        processors = [p for p in Processor if p != mirror]
        alloc0 = { p: j for p,j in zip(processors, jobs) }
        red_job = Job(alloc[mirror])
        alloc = add(alloc0, { mirror: red_job})
        s.configure(alloc)
    print(s)

def prev_proc(p:Processor):
    if p.value-1 < 1:
        return Processor(len(Processor))
    else:
        return Processor(p.value-1)
    
def next_proc(p:Processor):
    if p.value+1 > len(Processor):
        return Processor(1)
    else:
        return Processor(p.value+1)
    
def job_scheduler3(max_steps, mirror):
    mirror = Processor(mirror)
    
    alloc = { p : None for p in Processor }
    p_idx = 1
    for j in Job:
        if mirror.value == j.value:
            p_idx += 1

        alloc[Processor(p_idx)] = j
        p_idx += 1
    alloc[mirror] = alloc[prev_proc(mirror)]
    
    s = State([p for p in Processor],
              T0=0,
              alloc=alloc
    )
    n = 0
    while n<max_steps:
        print(s, mirror)
        n += 1

        new_alloc = alloc
        new_alloc[mirror] = alloc[next_proc(mirror)]
        new_alloc[next_proc(mirror)] = alloc[next_proc(next_proc(mirror))]
        
        if mirror<len(Processor)-1:
            mirror = Processor(mirror.value + 2)
        else:
            mirror = Processor.P2
        s.configure(new_alloc)
    print(s)

    
