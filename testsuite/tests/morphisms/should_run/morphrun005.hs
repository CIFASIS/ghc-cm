module Main where

class A a where
    a :: a -> Int
class B a where
    b :: a -> Int

class morphism A -> B where
    b x = 1 + a x

instance A () where
    a () = 2

instance B () where
    b () = 25

pepeh :: A a => a -> Int
pepeh x = b x

pepek :: B a => a -> Int
pepek x = b x

-- This should return (25, 25)
main = putStrLn $ show (pepeh (), pepek ())
