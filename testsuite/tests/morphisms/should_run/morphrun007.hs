module Main where

class F a where
    f :: a -> Int

class G a where
    g :: a -> Int

class H a where
    h :: a -> Int

class morphism F -> G where
    g x = f x + 1

class morphism G -> H where
    h x = g x + 2

ff :: F a => a -> [Int]
ff x = [f x, g x, h x]

instance F () where
    f () = 0

main = putStrLn $ show $ ff ()
