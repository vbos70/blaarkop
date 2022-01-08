from collections import namedtuple
from enum import Enum

from utils import *

#  Example 2.2.2
#
comment('''(Two cards). A standard deck of cards is shuffled. Two cards are
drawn randomly without replacement. Let A be the event that the first
card is a heart, and B be the event that the second card is red. Find
P(A|B) and P(B|A).

''')

Value = Enum('Value', 'Two Three Four Five Six Seven Eight Nine Ten Jack Queen King Ace')
Shape = Enum('Shape', 'Diamonds Hearts Clubs Spades')


Card = namedtuple('Card', ['value', 'shape'])
TwoCards = namedtuple('TwoCards', ['card0', 'card1'])

def red_card(c):
    return c.shape in { Shape.Diamonds, Shape.Hearts }

E0 = {Card(value=v, shape=s) for v in Value for s in Shape}

comment('''E is the set of all possibilities to draw two cards without
replacement from a standard deck of cards. We model this as the set of
all (card0, card1) pairs such that card0 != card1. Since a standard
deck of cards has 52 cards, E contains 52*51 cards.

''')

E = Universe({TwoCards(card0=c0, card1=c1)
              for c0 in E0 for c1 in E0
              if c0 != c1 })
assert len(E) == 52*51, len(E)

comment('A is the set of pairs of cards with card0 hearts.')
A = { e for e in E
      if e.card0.shape == Shape.Hearts }
print(f"P(A) = {E.P(A):}")

comment('B is the set of pairs of cards with card1 red.')
B = { e for e in E if red_card(e.card1) }
print(f"P(B) = {E.P(B):}")

comment('Compute the chance of A and B')
print(f"P(A & B) = {E.P(A & B):}")
comment('''The chance of A and B is not equal to P(A)*P(B), because A and B are
dependent on each other. For instance, if the first card is a heart, then the
chance of the second card being red is (26-1)/(52-1).''')

print(f'P(B|A) = {E.CP(B,A):}')
assert E.CP(B, A) == Fraction(25, 51)


comment('''Similarly, if the second card is red, then the chance of the first
card being a hearts is 13/(52-1)*1/2 + 12/(52-1)*1/2''')
assert E.CP(A, B) == (Fraction(13, 52-1) * Fraction(1,2) + Fraction(12, (52-1))*Fraction(1,2))
print(f"P(A|B) = {E.CP(A, B):}")
# 13/(52-1) * 1/2 + 12/(52-1) * 1/2

