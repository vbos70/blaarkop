#!/usr/bin/env stack
-- stack --resolver lts-7.14 --install-ghc runghc
main = do
    putStrLn "Please enter your birth year"
    year <- getLine
    putStrLn $ "In 2020, you will be: " ++ show (2020 - read year)