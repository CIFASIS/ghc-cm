module Main where

class A a where a :: a -> Int
class C c where c :: c -> Int
class C b => B b where b :: b -> Int

-- m :: AD a -> [[CD a]] -> BD a
-- should fail here, no way to generically get C
class morphism A -> B where
    b x = 2222

-- Explodes because no instance for C Int (or similar)
instance A Int where
    a x = x

main = print $ b (2 :: Int)
