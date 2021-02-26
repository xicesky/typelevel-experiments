
{-# OPTIONS_GHC
    -fenable-th-splice-warnings
    -Wno-unused-matches
    -Wno-unused-imports
#-}

module AlmostCompData where

import Prelude
import Data.Kind    ( Type, Constraint )
--import Data.Bifunctor
import Data.Void    ( absurd )

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Eq
import Data.Singletons.TypeLits

{-# ANN module "HLint: ignore Use camelCase" #-}

-- This is defined in Data.Singletons.Prelude.List.Internal
-- but not exported...
$(singletons [d|
    elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
    elem_by _  _ []         =  False
    elem_by eq y (x:xs)     =  y `eq` x || elem_by eq y xs

    -- Check if all elements of @l1@ occur in @l2@, order must be the same!
    ordSub_by :: (a -> a -> Bool) -> [a] -> [a] -> Bool
    ordSub_by _  []     _       = True
    ordSub_by _  (y:ys) []      = False
    ordSub_by eq (y:ys) (x:xs)  = if y `eq` x
        then ordSub_by eq ys     xs
        else ordSub_by eq (y:ys) xs

    |])

type TypeElemOfList t l = Elem_by DefaultEqSym0 t l
type Has l t        = TypeElemOfList t l ~ 'True
type HasNot l t     = TypeElemOfList t l ~ 'False
type HasAtI l t i   = FindIndex (DefaultEqSym1 t) l ~ 'Just i

type SubList l1 l2 = OrdSub_by DefaultEqSym0 l1 l2 ~ 'True

-- type NotInSum e s = FindIndex (DefaultEqSym1 e) s ~ 'Nothing
-- type InSum e s i = FindIndex (DefaultEqSym1 e) s ~ 'Just i

-- data (f :++: g) v e = Inl (f v e)
--                     | Inr (g v e)

data SumT :: [Type -> Type -> Type] -> Type -> Type -> Type where
    -- !! Only Bifunctors are allowed in our sum
    InHead      :: (Traversable (f v), xs `HasNot` f) =>
                   f v e       ->  SumT (f : xs) v e
    InTail      :: SumT xs v e ->  SumT (f : xs) v e
    InNil       ::                 SumT '[]      v e

{-
-- Proof that f does or doesn't occur in SumT
data Occurs (f :: Type -> Type -> Type) (i :: Maybe Nat) s where
    OccursNil   ::                      Occurs f 'Nothing       (SumT '[] v e)
    OccursHead  :: SumT (f : xs) v e -> Occurs f ('Just 0)      (SumT (f : xs) v e)
    OccursTail  :: Occurs f ('Just i) (SumT xs v e)
                -> SumT (g : xs) v e -> Occurs f ('Just (n+1))  (SumT (g : xs) v e)
    OccursNot   :: (DefaultEq f g ~ 'False)
                => Occurs f 'Nothing (SumT xs v e)
                -> SumT (g : xs) v e -> Occurs f 'Nothing       (SumT (g : xs) v e)
-}

-- Or maybe like this?
data Occurs (f :: Type -> Type -> Type) (i :: Maybe Nat) s where
    OccursHead  :: SumT (f : xs) v e
                -> Occurs f ('Just 0) (SumT (f : xs) v e)
    OccursTail  :: Occurs f ('Just i) (SumT xs v e)
                -> SumT (g : xs) v e
                -> Occurs f ('Just (n+1))  (SumT (g : xs) v e)

type DecideOccurs f i s = Decision (Occurs f i s)

--decideOccurs :: Decision (Occurs f i s)

-- !!! http://hackage.haskell.org/package/decidable
-- has list lookup and so on.

{- TODO: There is some proving to do here!
• Could not deduce: Elem_by DefaultEqSym0 f xs0 ~ 'False
  from the context: (KnownNat i, HasAtI fs f i, Traversable (f v))
• Could not deduce: fs ~ (f : xs0)
• Could not deduce (KnownNat i0) arising from a use of ‘inject’
-}
-- inject :: forall i f v e fs. (KnownNat i, HasAtI fs f i, Traversable (f v))
--     => f v e -> SumT fs v e
-- inject t = case natVal (Proxy :: Proxy i) of
--     0   -> InHead t
--     _   -> InTail $ inject t

{-
instance Bifunctor (SumT xs) where
    bimap :: (a -> b) -> (c -> d) -> SumT xs a c -> SumT xs b d
    bimap a b = \case
        InHead f    -> InHead $ bimap a b f
        InTail s    -> InTail $ bimap a b s
        InNil       -> InNil
-}

instance Functor (SumT xs v) where
    fmap :: (a -> b) -> SumT xs v a -> SumT xs v b
    fmap f = \case
        InHead g    -> InHead $ fmap f g
        InTail s    -> InTail $ fmap f s
        InNil       -> InNil

instance Foldable (SumT xs v) where
    foldMap :: Monoid m => (a -> m) -> SumT xs v a -> m
    foldMap f = \case
        InHead g    -> foldMap f g
        InTail s    -> foldMap f s
        InNil       -> mempty

instance Traversable (SumT xs v) where
    traverse :: forall f a b. Applicative f => (a -> f b) -> SumT xs v a -> f (SumT xs v b)
    traverse f = \case
        InHead g    -> fmap InHead (traverse f g)
        InTail s    -> fmap InTail (traverse f s)
        InNil       -> pure InNil

{- A @Context fs v a@ represents terms with holes over
    the Sum of the Functors @f v@ for all Bifunctors f in fs.
    @fs@ is a list of bifunctors (simple algebraic data types with 2 parameters).
    @v@ is the type of parameters - the first parameter of any @f@ in @fs@.
    @a@ is the type of holes.
-}
data Context :: [ Type -> Type -> Type ] -> Type -> Type -> Type where
    Term :: SumT fs v (Context fs v a) ->   Context fs v a
    Hole :: a ->                            Context fs v a

{-| A term is a context with no holes.  -}
type Term fs v = Context fs v Void

{-| Convert a sum of functors into a context. -}
simpCxt :: forall fs v a. SumT fs v a -> Context fs v a
{-# INLINE simpCxt #-}
simpCxt = Term . fmap Hole

{-| Convert a functorial value into a context.
    For constants, this type simplifies to:
    @MyConst v Void -> Term '[MyConst] v@
-}
simpCxt' :: forall f v a. Traversable (f v) => f v a -> Context '[f] v a
{-# INLINE simpCxt' #-}
simpCxt' = Term . InHead . fmap Hole

{-| This function unravels the given term at the topmost layer.  -}
unTerm :: Context fs v Void -> SumT fs v (Context fs v Void)
{-# INLINE unTerm #-}
unTerm (Term t) = t
unTerm (Hole void) = absurd void

{--------------------------------------------------------------------------------------------------}
-- Injection, projection



{--------------------------------------------------------------------------------------------------}
-- Examples
-- from: https://github.com/pa-ba/compdata/blob/master/examples/Examples/Common.hs

data Value v a  = Const Int | Pair a a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
data Op v a     = Add a a | Mult a a | Fst a | Snd a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- Still super annoying, automate using derive Generic and some TH?
{-  Maybe not even required
instance Bifunctor Value where
    bimap :: (a -> b) -> (c -> d) -> Value a c -> Value b d
    bimap _ _ (Const v) = Const v
    bimap _ g (Pair a b) = Pair (g a) (g b)

instance Bifunctor Op where
    bimap :: (a -> b) -> (c -> d) -> Op a c -> Op b d
    bimap _ g (Add a b) = Add (g a) (g b)
    bimap _ g (Mult a b) = Mult (g a) (g b)
    bimap _ g (Fst a) = Fst (g a)
    bimap _ g (Snd a) = Snd (g a)
-}

-- type Sig = Op :+: Value
type Sig = [Value, Op]

rawEx01 :: Term Sig v
rawEx01 = Term $ InHead (Const 5)

rawEx02 :: Term Sig v
rawEx02 = Term $ InTail $ InHead $ Add rawEx01 rawEx01

{- This is an error:
    rawExErr = Term $ InHead $ Add rawEx01 rawEx01
Couldn't match type ‘'True’ with ‘'False’ arising from a use of ‘InHead’
How to fix the error message?
-}


{--------------------------------------------------------------------------------------------------}

{- Usage:
    Check @(Bool ~ Int)
    Check @(Bool ~ Bool)
    Check @(FindIndex ((==@#@$$) 5) [1,2,5,6] ~ 'Just 3)
    Check @(FindIndex (DefaultEqSym1 Value) [Value, Op] ~ 'Just 0)
-}
data Check :: Constraint -> Type where
    Check :: forall c. c => Check c
deriving instance Show (Check c)
