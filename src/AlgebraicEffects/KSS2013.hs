
-- http://okmij.org/ftp/Haskell/extensible/exteff.pdf
-- http://okmij.org/ftp/Haskell/extensible/Eff.hs
-- without open unions
module AlgebraicEffects.KSS2013 where

import Control.Monad

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

newtype Reader e v = Reader (e -> v)

ask :: Eff (Reader a) a
ask = send Reader
--ask = Eff $ \k -> E (Reader k)

runReader :: forall a w. Eff (Reader a) w -> a -> Eff VoidF w
runReader m e = loop (admin m) where
    loop :: VE w (Reader a) -> Eff VoidF w
    loop (Val x) = return x
    loop (E (Reader r)) = loop (r e)

data VoidF v

run :: Eff VoidF w -> w
run m = case admin m of
    Val x -> x
    E x -> case x of {}

