from dataclasses import dataclass
from itertools import zip_longest

import z3
_solver = z3.Solver()

Expr = z3.ExprRef

def z3_prove(formula, *eqs, solver: z3.Solver =_solver):
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


def merge(l1, l2, fillvalue=None):
    '''A generator that yields the elements of `l1` and `l2` alternatively.

    `l1` and `l2` are iterables
    `fillvalue` is yielded when one of `l1` and `l2` runs out, but not the other.

    The generator stops when all values of both `l1` and `l2` have been yielded.
    '''
    for a,b in zip_longest(l1, l2, fillvalue=fillvalue):
        yield a
        if len(b)>0:
            yield b


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
    
    def add_step(self, eqs, target):
        ''' Extends this Proof by proving `target` from `self.last()`
        by applying the given equations in `eqs`.

        If `target`cannot be proven with the given equations, a 
        ProofException is raised and this Proof is not extended.
        '''
        to = target
        rs = eqs

        #lhs, rhs = self.terms[0], self.terms[-1]
        #rs.append(lhs == rhs)
        if not z3_prove(self.last() == to, *rs):
            user_rules = rs
            if len(user_rules) > 0:
                with_str = f' with {user_rules}'
            else:
                with_str = ''
            raise ProofException(f"Cannot prove {self.last()} == {to}{with_str}")
        self.terms.append(to)
        self.eqs.append(rs)


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

        self.add_step(eqs = list(other[1:]),
                      target = other[0])
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


class EqProof():
    def __init__(self, e):
        ''' Create an equational proof starting with z3 expression `e`.
        Since `e` is the initial step of the proof, its justification is set to `None`.
        '''
        self.step = [e]
        self.justification = [None]
        

    def step_is_valid(self, i=None):
        ''' Checks if step `i` in this proof is valid, meaning it can be proven by z3.

        Returns `True` if z3 can prove step `i`, `False` otherwise.

        If no `i` is given (`i==None`), the last step of the proof is checked.

        A `ProofException` is raised if `i<0` or `i>=len(self)`. 
        '''
        if i is None:
            i = len(self.step)-1
        if i < 0:
            raise ProofException(f"step index shall be at least 0, got {i}")
        if not i < len(self.step):
            raise ProofException(f"step index shall less than the len(self): {len(self.step)}, got {i}")
        if i == 0:
            return True
        return z3_prove(self.step[i-1] == self.step[i], self.justification[i])
    

    def _extend_(self, e, cs):
        equations = []
        for c in cs:
            if type(c) == Theory:
                equations.extend(c)
            else:
                equations.append(c)

        if not z3_prove(self.step[-1] == e, equations):
            raise ProofException(f"Cannot proof {self.step[-1]} == {e} from {cs}")
        self.step.append(e)
        self.justification.append(cs)


    def __iadd__(self, other):
        '''Extends this proof by z3 expression `e` and justification `*cs`.

        Returns `self`.

        Raises a `ProofException` if z3 cannot prove `e` with the justification `*cs`.
        '''
        if type(other) is not tuple:
            other = (other,)
        self._extend_(other[0], other[1:])
        return self

    def add(self, e, *cs):
        '''This is equivalent to `self.__iadd__(tuple([e] + cs))`.'''
        self._extend_(e, cs)


    def append(self, e, *cs):
        '''This is equivalent to `self.__iadd__(tuple([e] + cs))`.'''
        self._extend_(e, cs)

    def eq_proof_str(self, indent = 0):
        return "\n".join(merge(((" " * indent)+ "  " + str(e) for e in self.step), 
                               ((" " * indent)+"= {" + ", ".join(str(c) for c in cs) + "}" for cs in self.justification[1:]),
                               fillvalue=''))

    def __getitem__(self, i):
        if type(i) == slice:
            result = EqProof(self[i.start])
            result.step = self.step[i]
            result.justification = self.justification[i]
            return result
        return EqProof(self.step[i])
    
    def __len__(self):
        return len(self.step)

class Theory(set):

    def __init__(self, name, equations):
        super().__init__(equations)
        self.name = name
    
    def __str__(self):
        return self.name
    
    def __add__(self, other):
        return Theory(f'({self.name}+{other.name})', self | other)
    
    def __getitem__(self, i):
        return list(self)[i]
    
    def __getattr__(self, a):
        if a[:2] == 'EQ':
            return self[int(a[2:])]
        else:
            raise AttributeError(f'Theory object has no attribute called {a}')
