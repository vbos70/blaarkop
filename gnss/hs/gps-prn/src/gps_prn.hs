module Gps_prn
    ( someFunc
    ) where
import Data.Bifoldable (bifoldl1)


data FBSR where
  FBSR :: {es :: [Bool], len :: Int, fb :: [Int], out:: [Int]} -> FBSR
  deriving Show


initFBSR :: [Bool] -> [Int] -> [Int] -> FBSR
initFBSR es fb out
    | n >= length fb = FBSR { es=es, len = n, fb=fb, out=out}
    | otherwise        = error "Too many taps for FSRB"
    where n = length es

select :: [Bool] -> [Int] -> [Bool]
select bs is = [ bs !! i | i <- is ]

xorlist :: [Bool] -> Bool
xorlist = foldl1 (/=)

feedback :: [Bool] -> [Int] -> Bool
feedback fbsr fb = xorlist $ select fbsr fb

output ::  [Bool] -> [Int] -> Bool
output fbsr out = xorlist $ select fbsr out


shift :: FBSR -> (Bool, FBSR)
shift FBSR { es, len, fb, out } = (b, FBSR { es=e : take (len-1) es, len, fb, out })
    where 
        e = feedback es fb
        b = output es out



fbsr1 = initFBSR [True, True, True, True] [0, 3] [3]
fbsr2 = snd $ shift fbsr1

someFunc :: IO ()
someFunc = putStrLn $ "fbsr1: " ++ show fbsr1 ++ "\n" ++ "fbsr2: " ++ show fbsr2

data Coder where
    Coder :: { r1 :: FBSR, r2 :: FBSR } -> Coder
    deriving Show

shiftCoder :: Coder -> (Bool, Coder)
shiftCoder coder = (b1 /= b2, coder { r1=r1', r2=r2'})
    where 
        (b1, r1') = shift $ r1 coder
        (b2, r2') = shift $ r2 coder

next :: Coder -> Bool
next coder = b0 /= b1 
    where 
        (b0, _) = shift (r1 coder)
        (b1, _) = shift (r2 coder)

runCoder :: Coder -> [Bool]
runCoder coder = b : runCoder coder'
    where (b, coder') = shiftCoder coder


generate :: Coder -> Int -> [Bool]
generate coder n = take n $ runCoder coder

-- GPS C/A PRN codes: see https://www.gps.gov/technical/icwg/IS-GPS-200N.pdf
-- The G2 register has PRN-specific output taps:
-- PRN 1: gps_g2_taps[1 - 1]
-- PRN 2: gps_g2_taps[2 - 1]
-- etc.
gps_g2_taps :: [(Int, Int)]
gps_g2_taps = [
    (2, 6),  -- PRN 1
    (3, 7),  -- PRN 2
    (4, 8),
    (5, 9),
    (1, 9),
    (2, 10),
    (1, 8),
    (2, 9),
    (3, 10),
    (2, 3),
    (3, 4),
    (5, 6),
    (6, 7),
    (7, 8),
    (8, 9),
    (9, 10),
    (1, 4),
    (2, 5), 
    (3, 6),
    (4, 7),
    (5, 8),
    (6, 9),
    (1, 3),
    (4, 6),
    (5, 7),
    (6, 8),
    (7, 9),
    (8, 10),
    (1, 6),
    (2, 7),
    (3, 8), 
    (4, 9),
    (5, 10),
    (4, 10),
    (1, 7),
    (2, 8),
    (4, 10)  -- PRN 37 (same as PRN 34)
    ]

--data GPS_L1CA_Coder where
--    GPS_L1CA_Coder :: { g1 :: FBSR, g2 :: FBSR }
--    deriving Show

coder_GPS_L1CA_PRN_code :: Int -> Coder
coder_GPS_L1CA_PRN_code prn = Coder { 
    r1 = FBSR { 
        es=[True | i <- [1..10]], 
        len=10, 
        fb=[(3 - 1), (10 - 1)], 
        out=[10 - 1]},
    r2 = FBSR { 
        es = [True | i <- [1..10]], 
        len = 10, 
        fb = [(2 - 1), (3 - 1), (6 - 1), (8 - 1), (9 - 1), (10 - 1)],
        out = [(fst $ gps_g2_taps !! (prn - 1)) - 1, (snd $ gps_g2_taps !! (prn - 1)) - 1]}
    }

gps_prn_code :: Int -> [Bool]
gps_prn_code prn = runCoder (coder_GPS_L1CA_PRN_code prn)

code_str :: [Bool] -> String
code_str [] = ""
code_str (b : bs)
    | b         = '1' : (code_str bs)
    | otherwise = '0' : (code_str bs) 