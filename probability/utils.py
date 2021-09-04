# Generic functions
from fractions import Fraction


class Universe:
    '''A Universe object is a generic (finite) sample space. It provides
    functions to compute probabilities of elements belonging to a
    subset of the Universe.

    '''

    def __init__(self, S: set):
        self.S = S

        
    def __iter__(self):
        return iter(self.S)

    
    def __len__(self):
        return len(self.S)

    
    def P(self, s: set) -> Fraction:
        '''Returns the probability of an "s"-element, when randomly picking an
        element from this Universe. 

        Pre: s <= self.S

        The probability is computed as the Fraction of the number of
        elements in s and the total of elements in this Universe.

        '''
        return Fraction(len(s), len(self.S))

    
    def CP(self, s: set, c: set) -> Fraction:
        '''Returns the conditional probability of s given c. 

        Pre: s <= self.S and c <= self.S

        The conditional probability is computed according to
        Definition 2.2.1 (Conditional probability).

        '''
        return self.P(s & c) / self.P(c)

