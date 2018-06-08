{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

class F a where f :: a -> Int 
class G a where g :: a -> Int
class morphism F -> G where g x = 1
class morphism G -> F where f x = 2

instance F () where
    f () = 3

instance F a => F [a] where
    f (x:xs) = f x

f' :: F a => a -> [Int]
f' x = f x : g' x

g' :: G a => a -> [Int]
g' x = g x : f' x

main = print $ take 25 $ f' ()
