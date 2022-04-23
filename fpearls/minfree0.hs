-- compile with
--     ghc minfree0.hs
-- run as
--     ./minfree0
--
import Data.Array
import Data.List

search :: [Bool] -> Int
search = length . takeWhile id 

checklist :: [Int] -> Array Int Bool
checklist xs = accumArray (||) False (0,n)
  (zip (filter (<=n) xs) (repeat True))
  where n = length xs

minfree0 :: [Int] -> Int
minfree0 = search . elems . checklist

main :: IO ()
main = putStrLn (show ( minfree0 ([0 .. n] \\ [n - a])) ++ ", " ++ (show (n - a)))
  where n = 10000000
        a = (n `div` 10) + 7
                
