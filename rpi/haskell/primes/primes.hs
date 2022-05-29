-- Generate prime numbers up to the maximum of a list of arbitrary
-- large natural numbers.  Algorithm: Sieve of Eratosthenes.
--
-- Usage:
--     runhaskell primes.hs 54                -- primes up to 54
--     runhaskell primes.hs 54 45 2           -- primes up to 54
--     runhaskell primes.hs                   -- primes up to 2
--     runhaskell primes.hs 1020102011        -- primes up to 1020102011 (takes a long time)
--
-- Compile with:
--     ghc --make primes.hs  -- and the run as ./primes
--
import System.Environment
import Data.List

removeMultiples :: Integer -> [Integer] -> [Integer]
removeMultiples n [] = []
removeMultiples n (x : xs)
  | x `mod` n == 0 = removeMultiples n xs
  | otherwise     = x : (removeMultiples n xs)


myTail :: [a] -> [a]
myTail [] = []
myTail (a : as) = as

-- Take last n elements from a list (Stack overflow:
--  https://stackoverflow.com/questions/17252851/how-do-i-take-the-last-n-elements-of-a-list
zipLeftover :: [a] -> [a] -> [a]
zipLeftover []     []     = []
zipLeftover xs     []     = xs
zipLeftover []     ys     = ys
zipLeftover (x:xs) (y:ys) = zipLeftover xs ys

lastN :: Int -> [a] -> [a]
lastN n xs = zipLeftover (drop n xs) xs

last10 :: [a] -> [a]
last10  = lastN 10

primes :: [Integer] -> [Integer]
primes [] = []
primes (x : xs) = x : (primes (removeMultiples x xs))

upToMax :: Integer -> [String] -> Integer
upToMax max [] = max
upToMax max (a : as)
  | max < x    = upToMax x as
  | otherwise  = upToMax max as
  where x = (read a) :: Integer

main = do
  args <- getArgs
  putStrLn (show (last10 (primes [2 .. (upToMax 2 args)])))

