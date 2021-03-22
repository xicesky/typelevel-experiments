
module NonDetSearch.Hinze00 where

import Control.Monad

class Transformer t where
    promote :: Monad m => m a -> t m a
    observe :: Monad m => t m a -> m a

{- Laws:
promote (return a) = return a
promote (m >>= k) = promote m >>= (promote . k)

observe (return a) = return a
observe (promote m >>= k) = m >>= (observe k)

-}

data AMonadT m a
    = AReturn a
    | forall b. ABind (AMonadT m b) (b -> AMonadT m a)
    | APromote (m a)

instance Monad m => Functor (AMonadT m) where
    fmap = liftM

instance Monad m => Applicative (AMonadT m) where
    pure = return
    (<*>) = ap

instance Monad m => Monad (AMonadT m) where
    return = AReturn
    (>>=) = ABind

omega0 :: Monad m => AMonadT m a -> m a
omega0 (AReturn a) = return a
omega0 (ABind (AReturn a) k) = omega0 (k a)
omega0 (ABind (ABind m k1) k2) = omega0 (ABind m (k1 >=> k2))   -- (k1 >=> k2) = (\x -> k1 x >>= k2)
omega0 (ABind (APromote a) k) = a >>= (omega0 . k)
omega0 (APromote m) = m

omega1 :: Monad m => AMonadT m b -> (b -> AMonadT m a) -> m a
omega1 (AReturn a) k = omega0 (k a)
omega1 (ABind m k1) k2 = omega0 (ABind m (k1 >=> k2))
omega1 (APromote a) k = a >>= (omega0 . k)

-- omega0 . k :: b -> m a
-- omega_ op (omega0 . c) = omega0 (ABind op c)

omega_ :: Monad m => AMonadT m b -> (b -> m a) -> m a
omega_ (AReturn a) o0k = o0k a
omega_ (ABind m k1) k2 -- = omega0 (ABind (ABind m k1)) c)
    -- = omega0 (ABind m (\x -> k1 x `ABind` c))
    -- = omega_ m (\x -> omega0 (k1 x `ABind` c))
    = omega_ m (\x -> omega_ (k1 x) k2)     -- k2 == omega0 . c
omega_ (APromote a) k = a >>= k

instance Transformer AMonadT where
    promote = APromote
    observe = omega0

-- This is already the simplified version from chapter 3.2
data Raise m a
    = RReturn a
    | forall b. RPromoteBind (m b) (b -> Raise m a)
    | RRaise String

instance Monad m => Functor (Raise m) where
    fmap = liftM

instance Monad m => Applicative (Raise m) where
    pure = return
    (<*>) = ap

instance Monad m => Monad (Raise m) where
    return = RReturn
    -- "Integrated" simplify
    (>>=) (RReturn a) k             = k a
    (>>=) (RRaise e) _              = RRaise e
    (>>=) (RPromoteBind m k1) k2    = RPromoteBind m (k1 >=> k2)

instance Transformer Raise where
    promote a = RPromoteBind a RReturn
    observe (RReturn a) = return a
    observe (RPromoteBind m k)  = m >>= (observe . k)
    observe (RRaise e) = error e

{-----------------------------------------------------------------------------}

-- Context passing
newtype Raise' m a = Raise' (forall b. (a -> m b) -> m b)

unRaise' :: Raise' m a -> forall b. (a -> m b) -> m b
unRaise' (Raise' f) = f

instance Monad m => Functor (Raise' m) where
    fmap = liftM

instance Monad m => Applicative (Raise' m) where
    pure = return
    (<*>) = ap

-- omega_ :: Monad m => AMonadT m b -> (b -> m a) -> m a
-- omega_ (AReturn a) o0k = o0k a
-- omega_ (ABind m k1) k2 -- = omega0 (ABind (ABind m k1)) c)
--     -- = omega0 (ABind m (\x -> k1 x `ABind` c))
--     -- = omega_ m (\x -> omega0 (k1 x `ABind` c))
--     = omega_ m (\x -> omega_ (k1 x) k2)     -- k2 == omega0 . c
-- omega_ (APromote a) k = a >>= k

-- omega_ a x   = ...
-- a            = Raise' $ \c -> ...

instance Monad m => Monad (Raise' m) where
    return a = Raise' $ \c -> c a
    (Raise' m) >>= k = Raise' $ \c -> m (\x -> unRaise' (k x) c)

instance Monad m => MonadFail (Raise' m) where
    fail = error

instance Transformer Raise' where
    promote a = Raise' $ \c -> a >>= c
    observe (Raise' f) = f return
