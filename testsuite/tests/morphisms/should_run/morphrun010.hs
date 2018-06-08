module Main where

class AutoMonad m where
    return' :: a -> m a
    (>>==) :: m a -> (a -> m b) -> m b

class morphism AutoMonad -> Functor where
    fmap f m = m >>== (return' . f)
    (<$) = error ""

class morphism AutoMonad -> Applicative where
    pure = return'
    f <*> x = f >>== \ff -> x >>== \xx -> return' (ff xx)

class morphism AutoMonad -> Monad where
    return = return'
    (>>=) = (>>==)

class AutoApp f where
    pure' :: a -> f a
    (<**>) :: f (a -> b) -> f a -> f b

class morphism AutoApp -> Functor where
    fmap f m = pure' f <**> m
    x <$ f = fmap (const x) f

class morphism AutoApp -> Applicative where
    pure = pure'
    (<*>) = (<**>)

------------------------------------------------------------------------------

data Option a = None | Some a
    deriving Show

{- instance AutoMonad Option where -}
{-     return' = Some -}
{-     None >>== _ = None -}
{-     Some x >>== f = f x -}

{- instance Functor Option where -}
{- instance Applicative Option where -}

instance AutoMonad Option where
    return' = Some
    None >>== _ = None
    Some x >>== f = f x

{- instance AutoApp Option where -}
{-     pure' = Some -}
{-     Some f <**> Some v = Some (f v) -}
{-     _ <**> _ = None -}

-- These two cause an exponential blowup?
{- class morphism Monad -> Applicative where -}
{-     pure = return -}
{-     f <*> x = do ff <- f -}
{-                  xx <- x -}
{-                  return (ff xx) -}

{- class morphism Applicative -> Functor where -}
{-     fmap f x = pure f <*> x -}

{- instance AutoApp Option where -}
{-     pure' = Some -}
{-     Some f <**> Some x = Some (f x) -}
{-     _ <**> _ = None -}

{- instance Functor Option where -}
{-     fmap _ _ = error "asd" -}

{- class Pepe (t :: * -> *) where -}
{-     x :: t a -> t Int -}

{- class morphism Functor -> Pepe where -}
{-     x = fmap (const 3) -}

{- main = putStrLn $ show $ x (Some ()) -}

t1 = fmap (+1) (Some 3)

t2 = Some (+1) <*> Some 4

t3 = do v <- Some 5
        return (v + 1)

f1 :: Monad m => m a -> m ()
f1 m = fmap (const ()) m

f2 :: Applicative m => m a -> m ()
f2 m = fmap (const ()) m

f3 :: Functor m => m a -> m ()
f3 m = fmap (const ()) m

main = putStrLn $ show $ (t1,
                          t2,
                          t3,
                          f1 (Some 1),
                          f2 (Some 2),
                          f3 (Some 3)
                          )
