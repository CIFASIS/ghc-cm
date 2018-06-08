module Main where

class A a where
    a :: a -> Int
class B b where
    b :: b -> Int

class morphism A -> B where
    b x = 1 + f x

f :: A a => a -> Int
f x = 1 + b x

instance A () where
    a _ = 9

-- Infinite loop, but that's OK
-- It's the same behaviour with regular instances
main = putStrLn $ show $ b ()
