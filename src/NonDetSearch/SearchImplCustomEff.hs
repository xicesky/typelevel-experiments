
{-# OPTIONS_GHC
    -Wno-unused-imports
#-}

-- Search with custom Eff implementation
module NonDetSearch.SearchImplCustomEff where

import Control.Monad hiding (guard)

import NonDetSearch.NonDet
import Debug.Trace

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

-- For profiling
profSearch :: [String] -> IO ()
profSearch _ = print $ searchND (pidgeonHole' 8)
