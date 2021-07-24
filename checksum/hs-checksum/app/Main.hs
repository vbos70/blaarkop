module Main where

import Lib
import qualified Data.ByteString

readInput = Data.ByteString.getContents

main :: IO ()
main = do
  contents <- readInput
  putStrLn $ showCRC $ computeCRC contents

