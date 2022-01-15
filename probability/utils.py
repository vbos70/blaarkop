# Generic functions
from fractions import Fraction

def comment(msg):
    print("# " + ("\n# ".join(msg.splitlines())))


def prob(E: set, S: set) -> Fraction:
    '''Return the probability of event E in the universe S.

    Assumption: E and S are sets and E is a sub-set of S.

        E: set The event modelled as a subset of S.

        S: set The universe of all events.
    '''
    if len(S) == 0:
        return Fraction(0, 1)
    return Fraction(len(E), len(S))


def cprob(E: set, C: set, S: set) -> Fraction:
    '''Return the probability of event E conditioned on C in the universe S.

    Assumption: E, C, and S are sets and both E and C are sub-sets of S.

        E: set The event modelled as a subset of S.

        C: set The condition-event modelled as a subset of S.

        S: set The universe of all events.
    '''
    pc = prob(C, S)
    if pc == 0:
        return Fraction(0, 1)
    return prob(E & C, S) / prob(C, S)

