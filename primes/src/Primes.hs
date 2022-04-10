module Primes where

-- Infinite (?) list of all primes
-- Note: it isn't infinite, because it computes only primes <= maxBound :: Int
primes :: [Int]
primes = sieve [2 .. ]

-- Implementation of the sieve of Eratosthenes
sieve :: [Int] -> [Int]
sieve [] = []
sieve (nextPrime:rest) = nextPrime : sieve noFactors
  where noFactors = filter (not . (==0) . (`mod` nextPrime)) rest
