from dataclasses import dataclass

import z3
_solver = z3.Solver()

Expr = z3.ExprRef

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

@dataclass
class Equation:
    lhs : Expr
    rhs : Expr

    def __str__(self):
        return f'{self.lhs} == {self.rhs}'

    @property
    def expr(self):
        return self.lhs == self.rhs

    
class ProofException(Exception): pass
class Proof:

    def __init__(self, lhs: Expr, rhs: Expr):
        self.eq0 = Equation(lhs, rhs)
        self.terms = [lhs]
        self.eqs = []
    
    def steps(self):
        l = self.lhs()
        for eqs, r in zip(self.eqs, self.terms[1:]):
            yield (l, eqs, r)
            l = r
    
    def lhs(self):
        return self.eq0.lhs
    
    def rhs(self):
        return self.eq0.rhs
    
    def first(self):
        return self.lhs()
    
    def last(self):
        return self.terms[-1]
    
    def num_steps(self):
        return len(self.eqs)
    
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

            self.eq0 = Equation(self.lhs(), other.rhs())
            for (to, eqs) in zip(other.terms[1:], other.eqs):
                self.terms.append(to)
                self.eqs.append(eqs)
            return self
        
        if type(other) is not tuple:
            other = (other,)
        
        if len(other) == 0:
            raise ProofException(f'Expected a tuple with at least 1 element, got {other}')

        to = other[0]
        rs = list(other[1:])

        lhs, rhs = self.terms[0], self.terms[-1]
        rs.append(lhs == rhs)
        if not prove(rhs == to, *rs):
            user_rules = rs[:-1]
            if len(user_rules) > 0:
                with_str = f' with {user_rules}'
            else:
                with_str = ''
            raise ProofException(f"Cannot prove {rhs} == {to}{with_str}")
        self.terms.append(to)
        self.eqs.append(rs[:-1])
        return self

    def __add__(self, other):
        '''Returns a new Proof by appending `other` to `self`.
        
        Raises a ProofException if "self.rhs != other.lhs".
        '''
        if not (self.last() == other.first()):
            raise ProofException(f"First proof's last term {self.last()} is different from second proof's first term {other.first()}.")
        p = Proof(self.lhs(), other.rhs())
        p.terms = self.terms + other.terms[1:]
        p.eqs = self.eqs + other.eqs
        return p
    
    def is_complete(self):
        return self.lhs() == self.first() and self.rhs() == self.last()
    
    def __str__(self):
        result = [f'Theorem: {self.eq0}',
                  'Proof:' if self.is_complete() else 'Partial proof:']
        result += [f'   {self.terms[0]}']
        for (rs, t1) in zip(self.eqs, self.terms[1:]):
            result.append(f'== {rs if len(rs)>0 else ""}')
            result.append(f'   {t1}')
        return "\n".join(result)
    
    def equations(self):
        return set(eq for rs in self.eqs for eq in rs)

    def summary(self):
        result = []
        result += [f'   {self.lhs()}']
        if self.is_complete():
            result.append(f'== [{self.num_steps()} steps, {len(self.equations())} equations]')
        else:
            if self.num_steps() > 0:
                result.append(f'== [{self.num_steps()} steps, {len(self.equations())} equations]')                
                result.append(f'   {self.terms[-1]}')   
            else:
                pass
            result.append(f'?? incomplete proof')
        result.append(f'   {self.rhs()}')
        return "\n".join(result)
