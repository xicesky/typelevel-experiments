
{-# OPTIONS_GHC
    -Wno-unused-imports
#-}

-- Naive but general solver
module NonDetSearch.SearchImpl where

import Data.List (foldl')
import Control.Monad hiding (guard)

import Debug.Trace

{-----------------------------------------------------------------------------}
-- Support for non-determinism (apart from Applicative)

class NonDet m where
    {-# MINIMAL failure, choice #-}
    failure :: m a
    choice :: m a -> m a -> m a

    choices :: [m a] -> m a
    choices = foldl' choice failure

anyof :: (Applicative m, NonDet m) => [a] -> m a
anyof = choices . fmap pure

guard :: (Monad m, NonDet m) => Bool -> m ()
guard True  = return ()
guard False = failure

{-----------------------------------------------------------------------------}
-- Dumb impl using lists

instance NonDet [] where
    failure = []
    choice = (++)
    choices = join

searchList :: [a] -> [a]
searchList = id

{-----------------------------------------------------------------------------}
-- Mini algebraic effects

data VE w r
    =   Val w
    |   E (r (VE w r))

newtype Eff r a = Eff
    {   runEff :: forall w. (a -> VE w r) -> VE w r
    }

instance Functor (Eff r) where
    fmap = liftM

instance Applicative (Eff r) where
    pure = return
    (<*>) = ap

instance Monad (Eff r) where
    return x = Eff $ \c -> c x
    a >>= f = Eff $ \c -> a `runEff` (\x -> f x `runEff` c)

-- "send" an effect
send :: forall r a. (forall w. (a -> VE w r) -> r (VE w r)) -> Eff r a
send f = Eff $ \k -> E (f k)

-- "run" to the next effect
admin :: Eff r w -> VE w r
admin (Eff m) = m Val

{-----------------------------------------------------------------------------}
-- Nondeterministic, visualizable search

data ND a
    =   Failure
    -- |   forall v. Choice v v (v -> a)
    |   Choice a a

-- ndFailure :: Eff ND a
-- ndFailure = send $ const Failure

-- ndChoice :: a -> a -> Eff ND a
-- ndChoice a b = send $ \k -> Choice (k a) (k b)

-- ndC :: Eff ND a -> Eff ND a -> Eff ND a
-- ndC a b = join $ ndChoice a b

-- instance NonDet ND where
--     failure = Failure
--     Choice = Choice

instance NonDet (Eff ND) where
    failure     = send $ const Failure
    choice :: Eff ND a -> Eff ND a -> Eff ND a
    choice a b  = join $ send $ \k -> Choice (k a) (k b)

-- ARGH, mega-slow
searchND :: Eff ND a -> [a]
searchND e = loop (admin e) where
    loop :: VE a ND -> [a]
    loop (Val x) = return x
    loop (E Failure) = []
    loop (E (Choice a b)) = loop a ++ loop b    -- Inefficient

{-----------------------------------------------------------------------------}
-- Example problems

-- Pythagorean triples, limited to values <= 20
pytriple' :: (Monad m, NonDet m) => m (Int, Int, Int)
pytriple' = do
    a <- anyof [1..20]
    b <- anyof [a+1..20]
    c <- anyof [b+1..20]
    guard $ a * a + b * b == c * c
    return (a, b, c)

-- Pidgeonhole, n into m
pidgeonHole :: (Monad m, NonDet m) => Int -> Int -> m [Int]
pidgeonHole 0 _ = return []
pidgeonHole n m = do
    -- Choose hole for n-th pidgeon
    hole <- anyof [1..m]
    others <- pidgeonHole (n-1) m
    --traceM $ "pidgeonHole " ++ show (hole : others)
    -- Hole must be free
    guard $ notElem hole others
    return $ hole : others

{- How to fit n pidgeons in (n-1) holes?

In ghci without optimisations (on my Macbook), @n = 8@ is already slow.
-}
pidgeonHole' :: (Monad m, NonDet m) => Int -> m [Int]
pidgeonHole' n = pidgeonHole n (n-1)

-- For profiling
profSearch :: [String] -> IO ()
profSearch _ = print $ searchND (pidgeonHole' 8)
