{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Main where

class A a where
    a :: a -> Int

class B a where
    b :: a -> Int

class C a where
    c :: a -> Int

class D a where
    d :: a -> Int

---------
-- This morphism is the one that makes this code compile
-- Otherwise, there would be an overlap
class morphism A -> D where
    d x = a x + 16
---------

class morphism A -> B where
    b x = a x + 1

class morphism A -> C where
    c x = a x + 2

class morphism B -> D where
    d x = b x + 4

class morphism C -> D where
    d x = c x + 8

instance A () where
    a () = 0

x :: Int
x = d ()

main = putStrLn $ show x
