from collections import namedtuple
from enum import Enum

from utils import *

#  Example 2.2.7
#
# (A girl born in winter). A family has two children. Find the
# probability that both children are girls, given that at least one of
# the two is a girl who was born in winter. Assume that the four
# seasons are equally likely and that gender is independent of season
# (this means that knowing the gender gives no information about the
# probabilities of the seasons, and vice versa; see Section 2.5 for
# much more about this).


Sex = Enum('Sex', 'BOY GIRL')
Seasons = Enum('Seasons', 'SPRING, SUMMER, AUTUMN, WINTER')

Child = namedtuple('Child', ['sex', 'season'])
Children = namedtuple('Children', ['child0', 'child1'])

# E0 is a set of all possibilities for a child:
E0 = { Child(sex=sx, season=sn)
       for sx in Sex
       for sn in Seasons }

# E is the set of all possibilities for two children:
E = Universe({ Children(child0=c0, child1=c1)
               for c0 in E0
               for c1 in E0 })

# both_girls is the subset of E with child0 == child1 == GIRL:
both_girls = { e for e in E
               if e.child0.sex == Sex.GIRL and e.child1.sex == Sex.GIRL }

# at_least_one_winter_girl is the subset of E with at least one of
# child0 and child1 equal to (GIRL, WINTER):
at_least_one_winter_girl = { e for e in E
                             if Child(sex=Sex.GIRL, season=Seasons.WINTER) in e }

# Compute the probability that both children are girls, given that at
# least one of the two is a girl who was born in winter.
print(E.CP(both_girls, at_least_one_winter_girl))
