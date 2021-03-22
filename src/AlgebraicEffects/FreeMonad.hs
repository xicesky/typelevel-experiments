
{-# OPTIONS_GHC
    -Wno-unused-imports
#-}

-- http://okmij.org/ftp/Computation/free-monad.html
module AlgebraicEffects.FreeMonad where

import Prelude ((.),($),const,Int)
import Data.Functor (Functor(..))
import Control.Applicative (Applicative(..))
import Control.Monad (Monad(..), (>=>))
-- import Control.Category ((>>>))
import qualified Prelude as P

data Free f a where
       Pure   :: a -> Free f a
       Impure :: f (Free f a) -> Free f a

eta :: Functor f => f a -> Free f a
eta = Impure . fmap Pure

instance Functor f => Functor (Free f) where
    fmap f (Pure x)   = Pure $ f x
    fmap f (Impure m) = Impure $ fmap (fmap f) m

instance Functor f => Applicative (Free f) where
    pure = Pure
    Pure f <*> m   = fmap f m
    Impure f <*> m = Impure $ fmap (<*> m) f

instance Functor f => Monad (Free f) where
    return = Pure
    Pure a   >>= k = k a
    Impure m >>= k = Impure (fmap (>>= k) m)

{-----------------------------------------------------------------------------}

data FFree g a where
    FPure   :: a -> FFree g a
    FImpure :: g x -> (x -> FFree g a) -> FFree g a

instance Functor (FFree g) where
    fmap f (FPure x)     = FPure (f x)
    fmap f (FImpure u q) = FImpure u (fmap f . q)

instance Applicative (FFree g) where
    pure = FPure
    FPure f     <*> x = fmap f x
    FImpure u q <*> x = FImpure u ((<*> x) . q)

instance Monad (FFree g) where
    return = FPure
    FPure x      >>= k = k x
    FImpure u k' >>= k = FImpure u (k' >=> k)

etaF :: g a -> FFree g a
etaF fa = FImpure fa FPure

{-----------------------------------------------------------------------------}

newtype State s a = State{unState :: s -> (a,s)}

get :: State s s
get = State $ \s -> (s,s)

put :: s -> State s ()
put s = State $ const ((),s)

-- type FState s = Free (State s)

-- getF :: FState s s
-- getF = eta get

-- putF :: s -> FState s ()
-- putF = eta . put

-- runFState :: FState s a -> s -> (a,s)
-- runFState (Pure x) s   = (x,s)
-- runFState (Impure m) s = let (m',s') = unState m s in runFState m' s'

type FFState s = FFree (State s)

getFF :: FFState s s
getFF = etaF get

putFF :: s -> FFState s ()
putFF = etaF . put

runFFState :: FFState s a -> s -> (a,s)
runFFState (FPure x) s     = (x,s)
runFFState (FImpure m q) s = let (x,s') = unState m s in runFFState (q x) s'

testState :: FFState Int Int
testState = do 
    putFF 10
    x <- getFF
    return x

test_run :: (Int, Int)
test_run = runFFState testState 0
-- (10,10)
