# Class morphisms

Prototype implementation of class morphisms in GHC.

## Quick compile

Everything in https://ghc.haskell.org/trac/ghc/wiki/Building applies,
but if you don't feel like reading, here's the magic recipe:

    $ git submodule update --init
    $ perl boot
    $ ./configure
    $ make

That will take quite long, you can use `-j` in the `make` invocation to
run more threads.

## Try me out

Compile GHC and try First.hs module in the root directory.

    $ ./inplace/bin/ghc-stage2 First.hs
    [1 of 1] Compiling Main             ( First.hs, First.o )
    Linking First ...
    $ ./First
    T 42
    [A,B,B,C,C]

It works, but how? We did not declare instances for Functor T nor
Applicative T. Yet the module behaves correctly, and we are even calling
`fmap` for `T`.

What's more, we defined an instance of `Enum ABC`, but then we're using
`sort` on it, which requires `Ord ABC`, and it also works.

Both are consequences of class morphisms. The first one, those included
in the Prelude modelling the relation between the Functor, Applicative
and Monad classes, and the second ones are in the file itself.

Read ahead to find out how.

## How to use?

The syntax of class morphisms is pretty simple. Consider the
following well-known typeclass in Haskell:

```
class Enum a where
  toEnum   :: Int -> a
  fromEnum :: a -> Int
```

And suppose that someone wants to declare a morphism from Enum to Eq
(since it is clear that any Enum-type can be tested for equality).
Then, the corresponding syntax for that would be:

```
class morphism Enum -> Eq where
  x == y = (fromEnum x) == (fromEnum y)
```
Note that you can use the methods from the antecedent typeclass to
define the consequent's methods.

Something important to take into account is that whenever the consequent
typeclass has superclasses, then some way of generically obtaining them
should be provided. For example, we **need** the previous morphism if we now
want to define the following:
```
class morphism Enum -> Ord where
  compare x y = compare (fromEnum x) (fromEnum y)
```
Otherwise, the morphism going from `Enum` to `Ord` won't go through the
typechecker.

## Work in progress (and known bugs)

### Better errors
We need to give more descriptive and user-friendly errors.

### Optimization
We are changing some structures and algorithms so that we achieve a better performance.

### Laziness
Right now we are breaking GHC laziness since we are forcing every external module to be
loaded before computing the cover of instances. This is definitely just a hack until
we come up with a proper solution.
This issue does not only affect the performance of GHC. It also makes that some programs
don't work in the interactive mode. Consider the following piece of code:

```
class Functor f => Pointed f where point :: a -> f a
class morphism Monad -> Pointed where point = return

f = point 5 :: Either () Int
```
If we compile that code using GHC, everything goes smoothly: The `Monad` instance
for `Either e` is in scope (because we are forcing it), so the corresponding `Pointed`
instance for `Either e` is derived when we calculate the cover.

However, if we add those declarations line by line in GHCi, no `Pointed` instance will
be derived for `Either e` since `Data.Either` interface was never loaded by the time we
calculate the cover. So when we try to compute
```
Prelude> point 5 :: Either () Int
```
we'll get the corresponding error.
