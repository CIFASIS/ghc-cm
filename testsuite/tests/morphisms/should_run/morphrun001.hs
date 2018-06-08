module Main where

class C a where
     c :: a -> Int

class D a where
     d :: a -> Int

class morphism C -> D where
   d = c 

instance C a => C [a] where
   c xs = sum $ map c xs 

instance C Int where
   c x = x

main = print $ d [1 :: Int,2,3]
