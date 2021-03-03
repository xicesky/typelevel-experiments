
-- "Standard" extensions
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE DeriveFunctor          #-} 

-- should really be standard...
{-# LANGUAGE KindSignatures         #-}

-- Extensions for compdata usage
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE GADTs                #-}

module VoidTermCompdata where

import Control.Applicative hiding (Const)
import Control.Monad hiding (mapM, sequence)

import Data.Kind (Type)
import Data.Void
import Data.Foldable
import Data.Traversable
import Unsafe.Coerce

import Prelude hiding (foldl, foldl1, foldr, foldr1, mapM, sequence)


{-| This data type represents contexts over a signature. Contexts are
terms containing zero or more holes. The first type parameter is
supposed to be one of the phantom types 'Hole' and 'NoHole'. The
second parameter is the signature of the context. The third parameter
is the type of the holes. -}

data Context :: (Type -> Type) -> Type -> Type where
    Term :: f (Context f a) -> Context f a
    Hole :: a -> Context f a

{-| A term is a context with no holes.  -}
type Term f = Context f Void    -- !!

{-| Convert a functorial value into a context.  -}
simpCxt :: Functor f => f a -> Context f a
{-# INLINE simpCxt #-}
simpCxt = Term . fmap Hole

{-| Cast a term over a signature to a context over the same signature. -}
toCxt :: Functor f => Term f -> Context f a
{-# INLINE toCxt #-}
toCxt = vacuous -- = unsafeCoerce (for performance)
-- equivalent to @Term . (fmap toCxt) . unTerm@

{-| This function converts a constant to a term.

This can only work if the argument is indeed a constant, i.e. does not
have a value for the argument type of the functor @f@. -}

-- We can get rid of this
constTerm :: (Functor f) => f Void -> Term f
constTerm = simpCxt

instance Functor f => Functor (Context f) where
    fmap f = run
        where run (Hole v) = Hole (f v)
              run (Term t) = Term (fmap run t)

instance Functor f => Applicative (Context f) where
    pure = Hole
    (<*>) = ap

instance (Functor f) => Monad (Context f) where
    return = Hole
    m >>= f = run m
        where run (Hole v) = f v
              run (Term t) = Term (fmap run t)

instance (Foldable f) => Foldable (Context f) where
    foldr op c a = run a c
        where run (Hole a) e = a `op` e
              run (Term t) e = foldr run e t

    foldl op = run
        where run e (Hole a) = e `op` a
              run e (Term t) = foldl run e t

    fold (Hole a) = a
    fold (Term t) = foldMap fold t

    foldMap f = run
        where run (Hole a) = f a
              run (Term t) = foldMap run t

instance (Traversable f) => Traversable (Context f) where
    traverse f = run
        where run (Hole a) = Hole <$> f a
              run (Term t) = Term <$> traverse run t

    sequenceA (Hole a) = Hole <$> a
    sequenceA (Term t) = Term <$> traverse sequenceA t

    mapM f = run
        where run (Hole a) = liftM Hole $ f a
              run (Term t) = liftM Term $ mapM run t

    sequence (Hole a) = liftM Hole a
    sequence (Term t) = liftM Term $ mapM sequence t



{-| This function unravels the given term at the topmost layer.  -}

unTerm :: Context f Void -> f (Context f Void)
{-# INLINE unTerm #-}
unTerm (Term t) = t
