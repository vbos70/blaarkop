-- compile with
--     ghc minfree1.hs
-- run as
--     ./minfree1
--
import Data.Array
import Data.Array.ST
import Data.List

search :: [Bool] -> Int
search = length . takeWhile id 

checklist :: [Int] -> Array Int Bool
checklist xs = accumArray (||) False (0,n)
  (zip (filter (<=n) xs) (repeat True))
  where n = length xs

checklistST xs =
  runSTArray (do { a <- newArray (0, n) False;
                   sequence [writeArray a x True | x <- xs, x <= n];
                   return a})
  where n = length xs

minfree1 = search . elems . checklistST

main :: IO ()
main = putStrLn (show ( minfree1 ([0 .. n] \\ [n - a])) ++ ", " ++ (show (n - a)))
  where n = 10000000
        a = (n `div` 10) + 7
                
