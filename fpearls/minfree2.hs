-- compile with
--     ghc minfree1.hs
-- run as
--     ./minfree1
--
import Data.List

minfree2 :: [Int] -> Int
minfree2 xs = minfrom 0 (length xs, xs)
minfrom :: Int -> (Int, [Int]) -> Int
minfrom a (n, xs) | n == 0 = a
                  | m == b - a = minfrom b (n - m, vs)
                  | otherwise = minfrom a (m ,us)
    where (us, vs) = partition (<b) xs
          b = a + 1 + n `div` 2
          m = length us

main :: IO ()
main = putStrLn (show ( minfree2 ([0 .. n] \\ [n - a])) ++ ", " ++ (show (n - a)))
  where n = 10000000
        a = (n `div` 10) + 7
                
