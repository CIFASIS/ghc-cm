module BadMethod where

class A a where f :: a -> String

class B a where g :: a -> Int

class morphism A -> B where
  g a = f a 

