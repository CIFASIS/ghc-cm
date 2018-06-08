{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

class AutoMonad m where
    return' :: a -> m a
    (>>==) :: m a -> (a -> m b) -> m b

class AutoMonad2 m where
    return'' :: a -> m a
    (>>===) :: m a -> (a -> m b) -> m b

class morphism AutoMonad -> Functor where
    fmap f m = m >>== (return' . f)
    (<$) = error "1"

class morphism AutoMonad -> Applicative where
-- instance AutoMonad m => Applicative m
    pure = return'
    f <*> x = f >>== \ff -> x >>== \xx -> return' (ff xx)

class morphism AutoMonad -> Monad where
    return = return'
    (>>=) = (>>==)
    (>>) = error "4"
    fail = error "5"

class morphism AutoMonad2 -> Functor where
    fmap f m = m >>=== (return'' . f)
    (<$) = error "6"

class morphism AutoMonad2 -> Applicative where
    pure = return''
    f <*> x = f >>=== \ff -> x >>=== \xx -> return'' (ff xx)
    (<*) = error "7"
    (*>) = error "8"

class morphism AutoMonad2 -> Monad where
    return = return''
    (>>=) = (>>===)
    (>>) = error "9"
    fail = error "10"

data Option a = Some a | None
    deriving Show

instance AutoMonad Option where
    return' = Some
    None   >>== _ = None
    Some x >>== f = f x

t1 = fmap (+1) (Some 1)
t2 = Some (+1) <*> Some 1
t3 = do v <- Some 1
        return (v + 1)

main :: IO ()
main = putStrLn $ show $ (t1,t2,t3)
