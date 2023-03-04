#!/usr/bin/env stack
-- stack --resolver lts-7.14 --install-ghc runghc
import Control.Applicative ((<*>), Applicative)
import Prelude (return, Monad)
import qualified Prelude

fmap :: (Applicative m, Monad m) => (a -> b) -> (m a -> m b)
fmap f x = return f <*> x

main =
    case fmap (Prelude.+ 1) (Prelude.Just 2) of
        Prelude.Just 3 -> Prelude.putStrLn "Good job!"
        _ -> Prelude.putStrLn "Try again"