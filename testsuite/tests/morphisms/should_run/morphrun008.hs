module Main where
import Data.List

map2 f [] _ = []
map2 f _ [] = []
map2 f (x:xs) (y:ys) = (f x y) : map2 f xs ys

class C a where
     c :: a -> a -> Int
     c' :: a -> Int
class D a where
     d :: a -> a -> Int
     d' :: a -> Int

class morphism C -> D where
   d x y = c y x
   d' = c'

instance C a => C [a] where
   c xs ys = sum $ map2 c xs ys
   c' xs = sum $ map c' xs

instance C Int where
   c x y = x + y
   c' x = 25 + x

--(81,10)
main = print $ (d' [1::Int, 2, 3], d [3 :: Int, 2] [4 :: Int, 1])
