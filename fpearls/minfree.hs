-- pofad: minfree

import Data.Array
import Data.Array.ST
import Data.List

l0 :: [Int]
l0 = [08, 23, 09, 00, 12, 11, 01, 10, 13, 07, 41, 04, 21, 05, 17, 03, 19, 02, 06]
l1 :: [Int]
l1 = [08, 09, 00, 12, 11, 01, 10, 13, 07, 04, 05, 03, 02, 06]
l3 = [0::Int .. 10]

-- minfree is the executable specification. Its performance is O(n^2).
minfree :: [Int] -> Int
minfree xs = head ([0..] \\ xs)

-- search returns the index of the first False element in a [Bool]
-- list or, if no such element exists, it returns n+1, where n is the
-- length of the List.
-- Note: the book takes search :: Array Int Bool -> Int.
search :: [Bool] -> Int
search = length . takeWhile id 

checklist :: [Int] -> Array Int Bool
checklist xs = accumArray (||) False (0,n)
  (zip (filter (<=n) xs) (repeat True))
  where n = length xs

minfree0 :: [Int] -> Int
minfree0 = search . elems . checklist

countlist :: [Int] -> Array Int Int
countlist xs = accumArray (+) 0 (0,n) (zip xs (repeat 1))
  where n = maximum xs

sortlist :: [Int] -> [Int]
sortlist xs = concat [replicate k x | (x, k) <- assocs (countlist xs)]

checklistST xs =
  runSTArray (do { a <- newArray (0, n) False;
                   sequence [writeArray a x True | x <- xs, x <= n];
                   return a})
  where n = length xs

minfree1 = search . elems . checklistST

minfree2 :: [Int] -> Int
minfree2 xs = minfrom 0 (length xs, xs)
minfrom :: Int -> (Int, [Int]) -> Int
minfrom a (n, xs) | n == 0 = a
                  | m == b - a = minfrom b (n - m, vs)
                  | otherwise = minfrom a (m ,us)
    where (us, vs) = partition (<b) xs
          b = a + 1 + n `div` 2
          m = length us
