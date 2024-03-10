from T1_eqt import *

exp = Function('exp', Nat, Nat, Nat)

x, y = Consts('x y', Nat)
PA5 = ForAll(x,      exp(x, zero) == succ(zero))
PA6 = ForAll([x, y], exp(x, succ(y)) == mul(exp(x, y), x))

