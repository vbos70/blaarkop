module Primes where

primes :: [Int]
primes = [1 .. ] -- to be refactored later

-- Implementation of the sieve of Eratosthenes
sieve :: [Int] -> [Int]
sieve [] = []
sieve (nextPrime:rest) = nextPrime : sieve noFactors
  where noFactors = filter (not . (==0) . (`mod` nextPrime)) rest
