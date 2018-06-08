{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module Main where

class Fun a where
    fun :: a -> Int

class App a where
    app :: a -> Int

class Mon a where
    mon :: a -> Int

instance Mon () where
    mon () = 0

class morphism Mon -> App where
    app _ = 1

class morphism Mon -> Fun where
    fun _ = 2

class morphism App -> Fun where
    fun _ = 4

-- This should print 2, because applying the morphism "Mon ~> Fun" is
-- more direct than going through the "App" instance
main = print $ fun ()
