
{-
Interfaces for non-deterministic search.
-}
module NonDetSearch.NonDet where

import Data.List (foldl')
import Control.Monad (join)

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
