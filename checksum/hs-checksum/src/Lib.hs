module Lib
    ( CRC(..),
      ByteString,
      showCRC,
      computeCRC

    ) where

import qualified Data.ByteString.Lazy as B
--import Data.Int
import Data.Word
import Numeric (showHex)

type ByteString = B.ByteString

-- CRC computation uses strict pairs instead of lazy tuples. This
-- gives much better performance. The idea is from
-- https://donsbot.wordpress.com/2008/06/04/haskell-as-fast-as-c-working-at-a-high-altitude-for-low-level-performance/

-- The strict pair data type
data CRC = CRC !Word8 !Word8 deriving (Show, Eq)

showCRC :: CRC -> String
showCRC (CRC crc0 crc1) = showHex crc0 " " ++ showHex crc1 ""

-- This is the CRC computation using the strict pair data type CRC as
-- well as foldl' which is strict in its accumulator
computeCRC :: ByteString -> CRC
computeCRC = b_foldl fcrc (CRC 0 0)
  where b_foldl = B.foldl'
        fcrc :: CRC -> Word8 -> CRC
        fcrc (CRC crc0 crc1) b = let crc0' = crc0 + b
                                 in CRC crc0' (crc1 + crc0')

