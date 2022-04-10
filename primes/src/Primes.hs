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

-- Compute prime factors of n with 2 <= n < upperBound
-- Assumption: the 2nd argument is a list of prime numbers.
unsafePrimeFactors :: Int -> [Int] -> [Int]
unsafePrimeFactors 0 [] = []
unsafePrimeFactors n [] = []
unsafePrimeFactors n (next:rest) = if n `mod` next == 0
                                   then next:unsafePrimeFactors (n `div` next) (next:rest)
                                   else unsafePrimeFactors n rest
                                          
-- Compute prime factors of n :: Int
primeFactors :: Int -> Maybe [Int]
primeFactors n | n < 2 = Nothing
               | n >= upperBound = Nothing
               | otherwise = Just (unsafePrimeFactors n primesLessThanN)
  where primesLessThanN = filter (<= n) primes
        
