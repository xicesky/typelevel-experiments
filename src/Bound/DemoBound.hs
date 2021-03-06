
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

module Bound.DemoBound where

import Data.Kind (Type)
import Data.Void
import Data.List (elemIndex)
import Control.Applicative
import Control.Monad
import Data.Functor.Classes
import Data.Foldable
import Data.Traversable
import Data.Deriving

import Data.Functor.Foldable.TH (makeBaseFunctor)

import Bound
import Bound.Scope
import Bound.Name

import Data.Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

data BNegation = BooleanNot
    deriving (Show, Eq, Ord)
data BooleanOps = BooleanAnd | BooleanOr
    deriving (Show, Eq, Ord)

data Expr val uop bop var
    = Value    val
    | Unary    uop  (Expr val uop bop var)
    | Binary   bop  (Expr val uop bop var) (Expr val uop bop var)
    | Variable var
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
-- TODO: need tags
-- | Literal var
-- | Flattened bop [e]
-- | Lambda   (Scope () (Expr val uop bop) var)            -- Boolean lambda???

makeBaseFunctor ''Expr

-- newtype Fix f = Fix { unFix :: f (Fix f) }
-- newtype Fix4 f a b c d = Fix4 { unFix4 :: f a b c d (Fix4 f a b c d) }
--type Expr = Fix (ExprF Bool BNegation BooleanOps)
type PlainExpr = Expr Bool BNegation BooleanOps

-- Could now be pattern synonyms?
pattern Var :: var -> Expr val uop bop var
pattern Var v       = (Variable v)
pattern Val :: val -> Expr val uop bop var
pattern Val v       = (Value v)
pattern BNot :: Expr val BNegation bop var -> Expr val BNegation bop var
pattern BNot a      = (Unary BooleanNot a)
pattern BOp :: bop -> Expr val uop bop var -> Expr val uop bop var -> Expr val uop bop var
pattern BOp o a b   = (Binary o a b)
pattern BAnd :: Expr val uop BooleanOps var -> Expr val uop BooleanOps var -> Expr val uop BooleanOps var
pattern BAnd a b    = (Binary BooleanAnd a b)
pattern BOr :: Expr val uop BooleanOps var -> Expr val uop BooleanOps var -> Expr val uop BooleanOps var
pattern BOr  a b    = (Binary BooleanOr a b)

{-# COMPLETE Var, Val, BNot, BOp #-}
{-# COMPLETE Var, Val, BNot, BAnd, BOr #-}
{-# COMPLETE Var, Val, Unary, BOp #-}

-- instance Show2 (f a b) => Show1 (Fix4 f a b) where
--     liftShowsPrec1
--         :: (Int -> d -> ShowS) -> ([d] -> ShowS)
--         -> (Int -> e -> ShowS) -> ([e] -> ShowS)
--         -> Int -> Fix f a b c d e -> ShowS
--     liftShowsPrec2 = let
--         liftShowsPrec2'
--             :: (Int -> d -> ShowS) -> ([d] -> ShowS)
--             -> (Int -> e -> ShowS) -> ([e] -> ShowS)
--             -> Int -> f a b c d e -> ShowS
--         liftShowsPrec2' = liftShowsPrec2
--         in _

deriveShow1 ''Expr
deriveEq1 ''Expr
deriveOrd1 ''Expr
deriveRead1 ''Expr

deriveShow2 ''Expr
deriveEq2 ''Expr
deriveOrd2 ''Expr
deriveRead2 ''Expr

-- instance Eq a => Eq (Expr a) where (==) = eq1
-- instance Ord a => Ord (Expr a) where compare = compare1
-- instance Show a => Show (Expr a) where showsPrec = showsPrec1
-- instance Read a => Read (Expr a) where readsPrec = readsPrec1

instance Applicative (Expr a b c) where
    pure = Var
    (<*>) = ap

instance Monad (Expr a b c) where
    return  = Var
    Var a     >>= f     = f a
    Val b     >>= _     = Val b
    Unary o e >>= f     = Unary o (e >>= f)
    BOp o x y >>= f     = BOp o (x >>= f) (y >>= f)

    -- (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
    -- Lam e    >>= f = Lam (e >>>= f)

{-
data Var b a
  = B b -- ^ this is a bound variable
  | F a -- ^ this is a free variable

newtype Scope b f a = Scope { unscope :: f (Var b (f a)) }
Scope (Name vname ()) PlainExpr vname
= PlainExpr (Var (Name vname ()) (PlainExpr vname))

abstract :: Monad f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = Scope (liftM k e) where  -- "fmap k" over variables
  k y = case f y of
    Just z  -> B z                      -- Bound
    Nothing -> F (return y)             -- Free

In a sense, this changes the "name" of the variables from
"String" to Either () (PlainExpr String). 
Free variables thus get marked with an "F" and end up
like "F (F (B ()))"... how is that supposed to have better
performance than plain de-Brujin indices?
-}  

type TopLevelBound vname = Scope (Name vname Int) PlainExpr vname

{- Since, nicely, the variables are the last parameter of Expr,
we can just fold right over them. -}
freeVars :: (Eq a, Hashable a) => PlainExpr a -> HashSet a
freeVars = foldMap HashSet.singleton

bindVars :: (Eq a, Hashable a) => PlainExpr a -> TopLevelBound a
bindVars t = abstractName (`elemIndex` vars) t where
    vars = HashSet.toList (freeVars t)

term :: TopLevelBound String
term = bindVars $ BNot (Var "x" `BAnd` Var "y") `BAnd` Var "z"

-- Renames
rename :: Functor f => (t -> n) -> Scope (Name t ()) f a -> Scope (Name n ()) f a
rename f = mapBound (\(Name a ()) -> Name (f a) ())

main :: IO ()
main = do
  -- let term = lam 'x' (V 'x') :@ V 'y'
  print term         -- Lam (Scope (V (B ()))) :@ V 'y'
  --print $ whnf term  -- V 'y'
