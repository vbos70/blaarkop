import z3

class ProofException(Exception): pass

_solver = z3.Solver()

def prove(formula, *eqs, solver: z3.Solver =_solver):
    ''' Returns True if `formula` can be proven by `solver` 
    using the equations in `*eqs` and the built in z3 laws / axioms.
    Returns False otherwise.
    '''
    solver.push()
    solver.add(*eqs)
    result = not (solver.check(z3.Not(formula)) == z3.sat) 
    solver.pop()
    return result

class Proof:

    def __init__(self, lhs, rhs):
        self.eq0 = (lhs, rhs)
        self.ts = [lhs]
        self.eqs = []

    def theorem(self):
        return self.lhs() == self.rhs()
    
    def lhs(self):
        return self.eq0[0]
    
    def rhs(self):
        return self.eq0[1]
    
    def first(self):
        return self.ts[0]
    
    def last(self):
        return self.ts[-1]
    
    def __iadd__(self, other):
        ''' Extends this Proof with `other`, which is assumed to be a 
        single step consisting of a target term and zero or more 
        equations.

        The proof extensions succeeds if the equality 
            "self.final == other[0]" 
        can be proven by prove() with `ax=other[1:]`.

        If that fails, a ProofException is raised and this Proof is
        not extended.

        Returns `self`
        '''
        if type(other) == Proof:
                
            if not (self.last() == other.first()):
                raise ProofException(f"First proof's final term is different from second proof's first term.")

            self.eq0 = (self.eq0[0], other.eq0[1])
            for (to, eqs) in zip(other.ts[1:], other.eqs):
                self.ts.append(to)
                self.eqs.append(eqs)
            return self
        
        if type(other) is not tuple:
            other = (other,)
        
        if len(other) == 0:
            raise ProofException(f'Expected a tuple with at least 1 element, got {other}')

        to = other[0]
        rs = list(other[1:])

        lhs, rhs = self.ts[0], self.ts[-1]
        rs.append(lhs == rhs)
        if not prove(rhs == to, *rs):
            user_rules = rs[:-1]
            if len(user_rules) > 0:
                with_str = f' with {user_rules}'
            else:
                with_str = ''
            raise ProofException(f"Cannot prove {rhs} == {to}{with_str}")
        self.ts.append(to)
        self.eqs.append(rs[:-1])
        return self

    def __add__(self, other):
        '''Returns a new Proof by appending `other` to `self`.
        
        Raises a ProofException if "self.rhs != other.lhs".
        '''
        if not (self.last() == other.first()):
            raise ProofException(f"First proof's last term {self.last()} is different from second proof's first term {other.first()}.")
        p = Proof(self.lhs(), other.rhs())
        p.ts = self.ts + other.ts[1:]
        p.eqs = self.eqs + other.eqs
        return p
    
    def is_complete(self):
        return self.lhs() == self.first() and self.rhs() == self.last()
    
    def __str__(self):
        result = [f'Theorem: {self.lhs()} == {self.rhs()}',
                  'Proof:' if self.is_complete() else 'Partial proof:']
        result += [f'   {self.ts[0]}']
        for (rs, t1) in zip(self.eqs, self.ts[1:]):
            result.append(f'== {rs if len(rs)>0 else ""}')
            result.append(f'   {t1}')
        return "\n".join(result)

