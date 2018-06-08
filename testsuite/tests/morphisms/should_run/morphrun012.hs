{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where
import Control.Applicative
import Debug.Trace

class AutoMonad m where
    return' :: a -> m a
    (>>==) :: m a -> (a -> m b) -> m b

class AutoMonad2 m where
    return'' :: a -> m a
    (>>===) :: m a -> (a -> m b) -> m b

class morphism AutoMonad -> Functor where
    fmap f m = m >>== (return' . f)

class morphism AutoMonad -> Applicative where
    pure = return'
    f <*> x = f >>== \ff -> x >>== \xx -> return' (ff xx)

class morphism AutoMonad -> Monad where
    return = return'
    (>>=) = (>>==)

data Option x a = Some a | None
    deriving Show

instance AutoMonad (Option ()) where
    return' = Some
    None   >>== _ = None
    Some x >>== f = f x

instance AutoMonad (Option Int) where
    return' = Some
    None   >>== _ = None
    Some x >>== f = f x

t1 :: Functor (Option x) => Option x Int
t1 = fmap (+1) (Some 1)

t1_x :: Option Int Int
t1_x = t1

-- Need to annotate this one since we're missing expansion of flexible constraints (TODO)
t2 :: Applicative (Option x) => Option x Int
t2 = Some (+1) <*> Some 1

t3 :: Option () Int
t3 = do v <- Some (1 :: Int)
        return (v + 1)

instance Monad (Option Int) where
    return = trace "Hey M!" . return'
    (>>=) = (>>==)

instance Functor (Option Int) where
    fmap f m = trace "Hey F!" $ m >>== (return' . f)

main :: IO ()
main = putStrLn $ show $ (t1_x, t2 :: Option () Int, t3)
