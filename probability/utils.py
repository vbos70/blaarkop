# Generic functions
from fractions import Fraction

def comment(msg):
    print("# " + ("\n# ".join(msg.splitlines())))

from typing import Iterable
def FS(xs: Iterable)-> frozenset:
    '''Short notation for `frozenset`.'''
    return frozenset(xs)


def prob(E: set, S: set) -> Fraction:
    '''Return the probability of event E in the universe S.

    Assumptions: 

        1. Naive definition of probability is applicable.

        2. E and S are sets and E is a sub-set of S

    Parameters:

        E: set The event modelled as a subset of S.

        S: set The universe of all events.
    '''
    if len(S) == 0:
        return Fraction(0, 1)
    return Fraction(len(E), len(S))


def cprob(E: set, C: set, S: set) -> Fraction:
    '''Return the probability of event E conditioned on C in the universe S.

    Assumptions: 

        1. Naive definition of probability is applicable.

        2. E, C, and S are sets and both E and C are sub-sets of S.

    Parameters:

        E: set The event modelled as a subset of S.

        C: set The condition-event modelled as a subset of S.

        S: set The universe of all events.
    '''
    pc = prob(C, S)
    if pc == 0:
        return Fraction(0, 1)
    return prob([e for e in E if e in  C], S) / prob(C, S)

    # P(A|B)
    # = { Def 2.2.1: Conditional probability }
    # P(A & B) / P(B)
    # =
    # (|A & B| / |S|) / (|B| / |S|)
    # = |A & B| / |B|
