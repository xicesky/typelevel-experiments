
{-# OPTIONS_GHC
    -Wno-unused-imports
    -Wno-orphans
#-}

-- Naive but general solver
module NonDetSearch.SearchImpl where

import Control.Monad (join, MonadPlus(..))
--import Control.Monad hiding (guard)
import Control.Monad.Freer
import qualified Control.Monad.Freer.NonDet as F

import NonDetSearch.NonDet
import Debug.Trace

{-----------------------------------------------------------------------------}
-- Nondeterministic, visualizable search

type ND effs = Member F.NonDet effs

instance ND effs => NonDet (Eff effs) where
    failure :: Eff effs a
    failure     = mzero
    choice :: Eff effs a -> Eff effs a -> Eff effs a
    choice      = mplus

-- ARGH, mega-slow
searchND :: Eff '[F.NonDet] a -> [a]
searchND m = run $ F.makeChoiceA m

{-----------------------------------------------------------------------------}

-- For profiling
profSearch :: [String] -> IO ()
profSearch _ = print $ searchND (pidgeonHole' 8)
