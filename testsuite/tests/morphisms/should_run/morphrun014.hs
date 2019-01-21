module Main where

import Control.Monad ( ap, liftM )

data Option a = Some a | None deriving Show

instance Monad Option where
    return = Some
    Some x >>= f = f x
    None >>= _ = None

--instance Functor Option where
--    fmap f (Some x) = Some (f x)
--    fmap _ None = None

main = print $ fmap (+1) (Some 4)
