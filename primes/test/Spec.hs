import Test.QuickCheck
import Primes

import Data.Maybe

-- Check border-cases
prop_validPrimesOnly val = if val < 2 || val >= upperBound
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
        
main :: IO ()
main = do
  quickCheck prop_validPrimesOnly
  quickCheckWith stdArgs { maxSuccess = 1000} prop_primesArePrime
  quickCheckWith stdArgs { maxSuccess = 1000} prop_nonPrimesAreComposite
