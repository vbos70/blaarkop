module Main (main) where

import Lib (code_str, gps_prn_code)

main :: IO ()
main = putStrLn $ code_str $ take 10 $ gps_prn_code 1
