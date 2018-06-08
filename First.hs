module Main where

import Data.List ( sort )

data T a = T a
  deriving Show

instance Monad T where
    return = T
    T x >>= f = f x

test1 :: T Integer
test1 = fmap (*7) (return 6)

data ABC = A | B | C
  deriving Show

instance Enum ABC where
    fromEnum A = 0
    fromEnum B = 1
    fromEnum C = 2
    toEnum 0 = A
    toEnum 1 = B
    toEnum 2 = C

test2 = sort [C, B, A, C, B]

main = do print test1
          print test2

class morphism Enum -> Ord where
    compare x y = compare (fromEnum x) (fromEnum y)

class morphism Ord -> Eq where
    x == y = compare x y == EQ
