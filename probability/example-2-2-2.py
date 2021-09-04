from collections import namedtuple
from enum import Enum

from utils import *

#  Example 2.2.2
#
# (Two cards). A standard deck of cards is shuffled well. Two cards
# are drawn randomly, one at a time without replacement. Let A be the
# event that the first card is a heart, and B be the event that the
# second card is red. Find P(A|B) and P(B|A).

Value = Enum('Value', 'Two Three Four Five Six Seven Eight Nine Ten Jack Queen King Ace')
Shape = Enum('Shape', 'Diamonds Hearts Clubs Spades')


Card = namedtuple('Card', ['value', 'shape'])
TwoCards = namedtuple('TwoCards', ['card0', 'card1'])

def red_card(c):
    return c.shape in { Shape.Diamonds, Shape.Hearts }

E0 = {Card(value=v, shape=s) for v in Value for s in Shape}

# The Universe contains all pairs of cards *without* the pairs where
# card0==card1 (one card cannot be the first and the second card).
E = Universe({TwoCards(card0=c0, card1=c1)
              for c0 in E0 for c1 in E0
              if c0 != c1 })
assert len(E) == 52*51, len(E)

# A is set of two cards with Hearts for card0.
A = { e for e in E
      if e.card0.shape == Shape.Hearts }

# B is set of two cards with card1 a red card
B = { e for e in E if red_card(e.card1) }

print(f"P(A & B) = {E.P(A & B):}")
print(f"P(B) = {E.P(B):}")

assert E.CP(A, B) == Fraction(25, 102)
print(f"CP(A,B) = {E.CP(A, B):}")

assert E.CP(B, A) == Fraction(25, 51)
print(f"CP(B,A) = {E.CP(B, A):}")
