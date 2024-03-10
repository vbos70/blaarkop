from z3 import *

Nat = DeclareSort('Nat')

zero = Const('zero', Nat)
succ = Function('succ', Nat, Nat)
add = Function('add', Nat, Nat, Nat)
mul = Function('mul', Nat, Nat, Nat)

x, y = Consts('x y', Nat)
PA1 = ForAll(x,      add(x, zero) == x)
PA2 = ForAll([x, y], add(x, succ(y)) == succ(add(x, y)))
PA3 = ForAll(x,      mul(x, zero) == zero)
PA4 = ForAll([x, y], mul(x, succ(y)) == add(x, mul(x, y)))
