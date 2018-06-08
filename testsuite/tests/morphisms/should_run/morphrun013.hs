module Main where

data Option a = None | Some a deriving Show
data Option' a = None' | Some' a deriving Show

class AutoMonad m where
    return' :: a -> m a
    (>>==) :: m a -> (a -> m b) -> m b

-- Should work without giving default methods
class morphism AutoMonad -> Functor where
    fmap f m = m >>== (return' . f)

class morphism AutoMonad -> Applicative where
    pure = return'
    f <*> x = f >>== \ff -> x >>== \xx -> return' (ff xx)

class morphism AutoMonad -> Monad where
    return = return'
    (>>=) = (>>==)

instance AutoMonad Option where
    return' = Some
    None >>== _ = None
    Some x >>== f = f x

h :: Monad m => m Int -> m Int
h m = fmap (+1) m

{- do x <- m -}
{-          return (x + 1) -}

{- main = putStrLn $ show $ (f (Some 8), g, h (Some 8)) -}

main = putStrLn $ show $ h (Some 4)
