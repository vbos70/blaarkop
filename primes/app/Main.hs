module Main where

import Primes (primeFactors)
import System.Environment ( getArgs )
import Control.Category (Category(id))

formatInts :: Maybe [Int] -> String
formatInts Nothing = ""
formatInts (Just [i]) = show i
formatInts (Just (i:is)) = show i <> ", " <> formatInts (Just is)

formatPrimeFactors [] = "no input"
formatPrimeFactors [x] = show x <> ": " <> formatInts (primeFactors x)
formatPrimeFactors (x:xs) = show x <> ": " <> formatInts (primeFactors x) <> "\n" <> formatPrimeFactors xs


main :: IO ()
main = do
    input <- getArgs
    putStrLn $ formatPrimeFactors (map read input)
    --putStrLn("Prime factors of 53622: " <> (show $ primeFactors 53662)) 
