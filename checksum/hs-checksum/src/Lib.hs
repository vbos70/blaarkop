module Lib
    ( CRC(..),
      ByteString,
      showCRC,
      computeCRC
      
    ) where

import qualified Data.ByteString
import Data.Bits
import Data.Int
import Data.Word

type ByteString = Data.ByteString.ByteString

-- CRC computation uses strict pairs instead of lazy tuples. This
-- gives much better performance. The idea is from
-- https://donsbot.wordpress.com/2008/06/04/haskell-as-fast-as-c-working-at-a-high-altitude-for-low-level-performance/

-- The strict pair data type
data CRC = CRC !Word8 !Word8 deriving (Show, Eq)

hexDigits :: Word8 -> String
hexDigits n = (hexd ((n `shiftR` 4))) : (hexd n) : ""
  where
    hexd h = "0123456789ABCDEF" !! (fromIntegral (h .&. 0xF))


showCRC :: CRC -> String
showCRC (CRC crc0 crc1) = (hexDigits crc0) ++ " " ++ (hexDigits crc1)
  
-- This is the CRC computation using the strict pair data type CRC as
-- well as foldl' which is strict in its accumulator
computeCRC :: ByteString -> CRC
computeCRC bs = foldl fcrc (CRC 0 0) bs
  where foldl = Data.ByteString.foldl'
        pack = Data.ByteString.pack
        fcrc :: CRC -> Word8 -> CRC
        fcrc (CRC crc0 crc1) b = CRC (b + crc0) ((b `shiftL` 1) + crc1 + crc0)
  -- Note: crc0' = crc0 + b
  --       crc1' = crc1 + crc0' + b
  --             = crc1 + (crc0 + b) + b
  --             = crc1 + crc0 + 2*b
  --             = crc1 + crc0 + (b << 1)
  --                                `shiftL` is <<

