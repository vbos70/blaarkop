Act ::= a
      | a , b

Atom ::= done
      | wait
      | Act a
      | Var v

a : Atom 
Proc ::= a
       | x ; y
       | x + y
       | x || y  
       | x |- y     -- left merge
       | x && y     -- communication merge
       | Bind v x y


eval (Bind v x w)
  | v == w    = x
  | otherwise = (Bind v x (eval w))


simplify (wait ; x) = wait
simplify (done ; x) = x
simplify (x ; done) = x
simplify (wait + x) = x
simplify (x + wait) = x
simplify x ; (y ; z) = (x ; y) ; z
simplify a ; x = a ; (simplify x)
simplify x + (y + z) = (x + y) + z
simplify x || y = (x |- y) + (y |- x) + (x && y)
simplify a |- x = a ; x
simplify wait |- x = wait
simplify done |- x = wait
simplify a ; x |- y = a ; (x || y)
simplify (x + y) |- z = (simplify (x |- z)) + (simplify (y |- z))
simplify (a && b) = a , b
simplify (wait && x) = wait
simplify (done && x) = wait
simplify (a ; x && b ; y) = (a,b) ; (x || y) 
simplify (Bind v x y) = Bind v x y



apply (a,b) c
   | a == c    = b
   | otherwise = a


data Equal a = Equal a a

alt_assoc_right x y z = Equal (x + (y + z) ((x + y) + z))


[ a + (a + b)
, Step (alt_assoc_right a a b)
, (a + a) + b
]


check [] = True
check [x] = True
check ((Step x y) : z : xs)
    | y == z = check (z : xs)
    | otherwise = False
check (x : (Step y z) : xs)
    | x == y = check (z : xs)
    | otherwise = False
check (x : y : xs)
    | x == y = check (y : xs)
    | otherwise = False



x; Step (a, b) = Step (x; a) (x; b)

[ a + (a + b)
, eval (alt_assoc_right a a b)
, (a + a) + b
]

[p; q; (a + (a + b))
, p; q; eval (Step (alt_assoc_right a a b))
, p; q; ((a + a) + b)
]