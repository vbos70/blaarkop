module Main (main) where

import Lib ( computeCRC, showCRC )
import qualified Data.ByteString.Lazy as B

readInput :: IO B.ByteString
readInput = B.getContents

main :: IO ()
main = do
  contents <- readInput
  putStrLn $ showCRC $ computeCRC contents

