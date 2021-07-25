module Main where

import Lib
import qualified Data.ByteString.Lazy as B

readInput = B.getContents

main :: IO ()
main = do
  contents <- readInput
  putStrLn $ showCRC $ computeCRC contents

