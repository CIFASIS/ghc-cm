module Main where

-- This should succeed

class B a where
    b :: a -> ([Int], [Int])

class C a   where c :: a -> [Int]
class C' a  where c' :: a -> [Int]
class C'' a where c'' :: a -> [Int]

class D a    where d :: a -> [Int]
class D' a   where d' :: a -> [Int]
class D'' a  where d'' :: a -> [Int]
class D''' a where d''' :: a -> [Int]

{- class X a where -}

class morphism D'' -> D' where
    d' = (1:) . d''
    
class morphism D' -> D where
    d = (2:) . d'

class morphism D''' -> D where
    d = (3:) . d'''

class morphism C'' -> C' where
    c' = (4:) . c''

class morphism C' -> C where
    c = (5:) . c'

instance B () where
    b x = (d x, c x)

-- Just to mess it up
{- class morphism X -> D where -}
{- class morphism X -> D' where -}
{- class morphism X -> D'' where -}
{- class morphism X -> D''' where -}
{- class morphism X -> C where -}
{- class morphism X -> C' where -}
{- class morphism X -> B where -}

instance D'' () where
    d'' () = [6]
instance D''' () where
    d''' () = [7]
instance C'' () where
    c'' () = [8]

{- f :: B a => a -> () -}
{- f x = () -}

{- x = f () -}

-- ([3,7],[5,4,8])
main = print $ b ()
