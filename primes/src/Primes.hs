module Primes where

-- Upper bound for primes check
upperBound = 10000 :: Int

-- Determine if a number is prime.
isPrime :: Int -> Maybe Bool
isPrime n | n < 2  = Nothing
          | n < upperBound = Just (n `elem` primes)
          | otherwise = Nothing

-- List of all primes less than upperBound
primes :: [Int]
primes = sieve [2 .. upperBound]

-- Implementation of the sieve of Eratosthenes
sieve :: [Int] -> [Int]
sieve [] = []
sieve (nextPrime:rest) = nextPrime : sieve noFactors
  where noFactors = filter (not . (==0) . (`mod` nextPrime)) rest
