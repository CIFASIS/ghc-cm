module Main where

class Func f where
    fmap_ :: (a -> b) -> f a -> f b

class App f where
    pure_ :: a -> f a
    (<**>) :: f (a -> b) -> f a -> f b

class Mon m where
    return_ :: a -> m a
    (>>==) :: m a -> (a -> m b) -> m b

class morphism Mon -> App where
    pure_ = return_
    f <**> x = f >>== \ff -> x >>== \xx -> return_ (ff xx)

class morphism Mon -> Func where
    fmap_ f x = x >>== (return_ . f)

class morphism App -> Func where
    fmap_ f x = (pure_ f) <**> x

data Id a = Id a
 deriving Show

unId (Id x) = x

instance Mon Id where
    return_ = Id
    Id x >>== f = f x

instance Func Id where
    fmap_ f (Id x) = Id (f x)

f :: Mon m => m Int -> m Int
f x = (fmap_ (+1) x) >>== (\x -> return_ (x-2))

g :: (Func m, Mon m) => m Int -> m Int
g x = (fmap_ (+1) x) >>== (\x -> return_ (x-2))

h :: Id Int -> Id Int
h x = (fmap_ (+1) x) >>== (\x -> return_ (x-2))

main = putStrLn $ show (f (Id 0), g (Id 0), h (Id 0))
