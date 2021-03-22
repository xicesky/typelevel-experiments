
{-# OPTIONS_GHC
    -Wno-unused-imports
    -Wno-name-shadowing
#-}

module NonDetSearch.CPSControl where

import Control.Applicative (Alternative)
import Control.Monad

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Redundant lambda" #-}
{-# ANN module "HLint: ignore Avoid lambda using `infix`" #-}

{- | Class for non-deterministic choice

This could actually just be 'Alternative', but we want a class
that is seperate from that and doesn't require our type to be
an 'Applicative'.
-}
class NonDet n where
    failure :: n a
    choice :: n a -> n a -> n a

{-----------------------------------------------------------------------------}
-- "Direct" CPS

newtype CPS0 a = CPS0 { unCPS0 :: forall r. (a -> r) -> r }

-- infixl 1 >>-
-- (>>-) :: CPS0 a -> (a -> r) -> r
-- (>>-) = unCPS0

instance Functor CPS0 where
    fmap = liftM

instance Applicative CPS0 where
    pure = return
    (<*>) = ap

instance Monad CPS0 where
    return x = CPS0 $ \c -> c x
    -- (CPS0 a) >>= f = a f
    a >>= f = CPS0 $ \c -> a `unCPS0` (\x -> f x `unCPS0` c)
    -- a >>= f = CPS0 $ \c -> a >>- \x -> f x >>- c

-- type CPS a = forall r. (a -> r) -> r

-- infixl 1 >>-
-- (>>-) :: CPS a -> (a -> r) -> r
-- (>>-) = id

-- bind :: CPS a -> (a -> CPS b) -> CPS b
-- bind ma = ma


{-----------------------------------------------------------------------------}
-- CPS over any type c

newtype CPS1 c a = CPS1 { unCPS1 :: forall r. (a -> c r) -> c r }

-- unCPS1 :: CPS1 c a -> (a -> c r) -> c r

instance Functor (CPS1 c) where
    fmap = liftM

instance Applicative (CPS1 c) where
    pure = return
    (<*>) = ap

instance Monad (CPS1 c) where
    return x = CPS1 $ \c -> c x
    -- (CPS0 a) >>= f = a f
    a >>= f = CPS1 $ \c -> a `unCPS1` (\x -> f x `unCPS1` c)
    -- a >>= f = CPS0 $ \c -> a >>- \x -> f x >>- c

instance NonDet c => NonDet (CPS1 c) where
    failure = CPS1 $ const failure
    choice :: CPS1 c a -> CPS1 c a -> CPS1 c a
    choice (CPS1 a) (CPS1 b) = CPS1 $ \c ->
        choice (a c) (b c)

{-----------------------------------------------------------------------------}

one :: (Int -> r) -> r
one c = c 1

plusone :: Int -> (Int -> r) -> r
plusone x c = c (x + 1)


add_cps :: Int -> Int -> ((Int -> r) -> r)
add_cps x y = \k -> k ((+) x y)

square_cps :: Int -> ((Int -> r) -> r)
square_cps x = \k -> k (x * x)

chainCPS :: ((a -> r) -> r) -> (a -> ((b -> r) -> r)) -> ((b -> r) -> r)
chainCPS fa fab =
    \k -> fa (\a -> fab a k)

-- ACTUALLY
{-# ANN chainCPS' "HLint: ignore Eta reduce" #-}
chainCPS' :: (forall r. (a -> r) -> r)
    -> (forall r. a -> ((b -> r) -> r))
    -> (forall r. (b -> r) -> r)
chainCPS' fa fab = fa fab

-- Error continuation
doStuff :: Int -> (Int -> r) -> (String -> r) -> r
doStuff i success failure
    | i > 0     = success (i+1)
    | otherwise = failure "Value too small"

exampleCall :: Int
exampleCall = 
    doStuff (-1) id (const 0)
