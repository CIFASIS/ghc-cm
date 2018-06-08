module Main where

import Control.Monad ( ap, liftM )

class morphism Monad -> Applicative where
  pure = return
  (<*>) = ap

class morphism Applicative -> Functor where
  fmap f x = pure f <*> x

class morphism Monad -> Functor where
  fmap = liftM

data Option a = Some a | None deriving Show

instance Monad Option where
    return = Some
    Some x >>= f = f x
    None >>= _ = None

--instance Functor Option where
--    fmap f (Some x) = Some (f x)
--    fmap _ None = None

main = print $ fmap (+1) (Some 4)
