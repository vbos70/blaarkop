-- blmean: compute the mean value of a big list of Doubles.
--
-- The code is based on:
-- https://donsbot.wordpress.com/2008/06/04/haskell-as-fast-as-c-working-at-a-high-altitude-for-low-level-performance/

-- Compile and run with:
--
--     make
--     time ./blmean_highlevel1 1e9
--

-- This is called a "high level" version, because the (input list)
-- generation, recursion, and accumulation are separated.

import Text.Printf
import System.Environment

-- As mentioned in the blog post, Haskell's tuples are lazy data types
-- and therefore not suitable here. Instead, we define our own data
-- types of pairs and ensure the constructor is strict in both
-- arguments.
data P a b = P !a !b

foldl' g z n m | n > m = z
               | otherwise = foldl' g z1 (n+1) m
  where z1 = z `seq` n `seq` (z `g` n)


-- foldr + z [a1 .. an ] = foldr + (a1 + z) [a2 an]
--                       = foldr + (a2 + (a1 + z)) [a3 an]
--                       = an + (..(a2 + (a1 + z))..)
--
-- foldl + z [a1 .. an ] = (..((z + a1) + a2) ..) + an
--                       = (foldl + z [a1 .. a(n-1)]) + an
--                       = 


-- (z `seq`) forces strict evaluation of z. Without this, memory use increases a lot:
--                 | otherwise = foldl' g (z `g` n0) (n0+1) n1
            
mean :: Double -> Double -> Double
mean n m = s / fromIntegral l
  where
    P s l = foldl' k (P 0 0) n m
    k (P s l) a = P (s+a) (l+1) -- here the strict pair data type
                                -- keeps memory usage small
-- If normal list generation is uses, as in
--    P s l = foldl k (P 0 0) [n .. m]
-- then the runtime performance is much worse (but memory use is the same).

main = do
  [d] <- map read `fmap` getArgs
  printf "%f\n" (mean 1 d)
