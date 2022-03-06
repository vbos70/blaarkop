-- blmean: compute the mean value of a big list of Doubles.
--
-- The code is copied from:
-- https://donsbot.wordpress.com/2008/06/04/haskell-as-fast-as-c-working-at-a-high-altitude-for-low-level-performance/

-- Compile and run with:
--
--     make
--     time ./blmean_lowlevel 1e9
--

-- This is called a "low level" version with a recursive definition of
-- the mean function.

import Text.Printf
import System.Environment

mean :: Double -> Double -> Double
mean n m
  | m > 0     = go 0 0 n
  | otherwise = 0.0
  where
    go :: Double -> Int -> Double -> Double
    go s l x | x > m      = s / fromIntegral l
             | otherwise  = go (s+x) (l+1) (x+1)

main = do
  [d] <- map read `fmap` getArgs
  printf "%f\n" (mean 1 d)
