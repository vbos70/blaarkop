import Test.QuickCheck
import Primes

import Data.Maybe

-- Check border-cases
prop_validPrimesOnly val = if val < 2 || val >= upperBound --length primes
                       then result == Nothing
                       else isJust result
  where result = isPrime val

-- Check if n is a prime when isPrime n == Just True
prop_primesArePrime val = if result == Just True
                          then length divisors == 0
                          else True
  where result = isPrime val
        divisors = filter ((== 0) . (val `mod`)) [2 .. (val - 1)]

-- Check if n is composite if isPrime n == Just False
prop_nonPrimesAreComposite val = if result == Just False
                                 then length divisors > 0
                                 else True
  where result = isPrime val
        divisors = filter ((== 0) . (val `mod`)) [2 .. (val - 1)]

-- Check if n equals the product of its prime factors
prop_factorsMakeOriginal val = if result == Nothing
                               then True
                               else product (fromJust result) == val
  where result = primeFactors val

-- Check if all prime factors are primes
prop_allFactorsPrime val = if result == Nothing
                           then True
                           else all (== Just True) resultsPrime
  where result = primeFactors val
        resultsPrime = map isPrime (fromJust result)
        
main :: IO ()
main = do
  quickCheckWith stdArgs { maxSuccess = 8000 } prop_validPrimesOnly
  quickCheckWith stdArgs { maxSuccess = 1000 } prop_primesArePrime
  quickCheckWith stdArgs { maxSuccess = 1000 } prop_nonPrimesAreComposite
  quickCheckWith stdArgs { maxSuccess = 1000 } prop_factorsMakeOriginal
  quickCheck prop_allFactorsPrime

  
