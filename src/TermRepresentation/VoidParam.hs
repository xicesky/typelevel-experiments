
{-# OPTIONS_GHC -Wno-unused-imports #-}

module TermRepresentation.VoidParam where

import Data.Kind (Type)
import Data.Void
import Data.Functor.Const
import Data.Function ((&))

{-----------------------------------------------------------------------------}
-- The problem

doBlah :: Either Void a -> a
doBlah (Right v) = v
-- incomplete pattern -> annyoing!!
doBlah (Left void111) = case void111 of {}        -- or: absurd e

-- Another case
type VoidF = Const Void

doStuff :: Either a (VoidF b) -> a
doStuff (Left a) = a
doStuff (Right voidF111) = case voidF111 of {}

-- Strictness? Strictness!
data Either' a b = Left' !a | Right' !b

doBlah' :: Either' Void a -> a
doBlah' (Right' v) = v

{-----------------------------------------------------------------------------}
-- Not a real solution but looks nice
-- https://hackage.haskell.org/package/total

class Empty a where
    impossible :: a -> x

instance Empty Void where
    impossible = absurd

instance Empty (VoidF a) where
    impossible = impossible . getConst

instance (Empty a, Empty b) => Empty (Either a b) where
    impossible (Left  a) = impossible a
    impossible (Right b) = impossible b

_case :: Empty a => a -> x
_case = impossible

_default :: x -> a -> x
_default x _ = x


