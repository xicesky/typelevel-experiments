
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC
    -fenable-th-splice-warnings
    -Wno-unused-imports
#-}

-- https://typesandkinds.wordpress.com/2012/12/01/decidable-propositional-equality-in-haskell/

module PropEquality where

import Data.Kind    ( Type, Constraint )
import Data.Void
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude ( SBool )

{--------------------------------------------------------------------------------------------------}
{- The usual inductive naturals, indexed vectors, yada yada. -}

$(singletons [d|
    data Nat = Zero | Succ Nat
    |])

data Vec :: Type -> Nat -> Type where
  VNil  :: Vec a 'Zero
  VCons :: a -> Vec a n -> Vec a ('Succ n)

safeHead :: Vec a ('Succ n) -> a
safeHead (VCons h _) = h

safeTail :: Vec a ('Succ n) -> Vec a n
safeTail (VCons _ t) = t

{--------------------------------------------------------------------------------------------------}
-- The twist: non-trivial property
-- (as usually lifted by singletons)

$(singletons [d|
    boolEq :: Nat -> Nat -> Bool
    boolEq Zero     Zero     = True
    boolEq (Succ a) (Succ b) = boolEq a b
    boolEq Zero     (Succ _) = False
    boolEq (Succ _) Zero     = False
    |])

-- type family BoolEq (a :: Nat) (b :: Nat) :: Bool
-- type instance BoolEq 'Zero 'Zero = 'True
-- type instance BoolEq ('Succ a) ('Succ b) = BoolEq a b
-- type instance BoolEq 'Zero ('Succ x) = 'False
-- type instance BoolEq ('Succ x) 'Zero = 'False

{- And the error:
    Could not deduce: n ~ 'Succ ('Succ n0)
    from the context: BoolEq n ('Succ ('Succ n')) ~ 'True
-}
-- cadr :: forall n n' a. (BoolEq n (Succ (Succ n')) ~ True) => Vec a n -> a
-- cadr v = safeHead (safeTail v)

{-  The problem is that GHC doesn’t know that our Boolean equality
    function really shows the equality of two types.
-}

-- cadr :: SBool (BoolEq n (Succ (Succ n'))) -> a -> Vec a n -> a
-- cadr evidence deflt v = case evidence of
--     STrue -> safeHead (safeTail v)
--     SFalse -> deflt
{-
    • Could not deduce: n ~ 'Succ ('Succ n0)
      from the context: BoolEq n ('Succ ('Succ n')) ~ 'True
Pattern-matching on the SBool just brings the equality
    (BoolEq n (Succ (Succ n'))) ~ True
into the context.
-}

{--------------------------------------------------------------------------------------------------}
-- Let's prove it to GHC!
{- We don't need PropEq, we have

type (:~:) :: forall k. k -> k -> Type
data (:~:) a b where
  Refl :: forall k (a :: k). (:~:) a a
    -- Defined in ‘Data.Type.Equality’
-}

boolToProp :: (BoolEq a b ~ 'True) => SNat a -> SNat b -> a :~: b
boolToProp SZero SZero = Refl
-- boolToProp (SSucc x) (SSucc y) = boolToProp x y
-- ^ Occurs check: cannot construct the infinite type: n ~ 'Succ n
boolToProp (SSucc x) (SSucc y) = case boolToProp x y of
    Refl -> Refl

{- Richard runs in to a GHC bug here.
    I don't, because i'm awesome.
    And maybe because the bugs were fixed in the last 8 years.
-}

cadr :: SBool (BoolEq n ('Succ ('Succ n')))
    -> SNat n -> SNat n'
    -> a -> Vec a n -> a
cadr evidence n n' deflt v = case evidence of
    STrue -> case boolToProp n (SSucc (SSucc n')) of
        Refl    -> safeHead (safeTail v)
    SFalse -> deflt

{- The sad part here is that, to make it work, we needed to pass around two
SNats and perform an O(n) operation (at runtime – the boolToProp “proof”
runs!) to prove to GHC that the operation is valid. Can we do better? -}

{--------------------------------------------------------------------------------------------------}
-- Decidable Propositional Equality

type Not a = a -> Void
type DecidableEquality (a :: k) (b :: k) =
    Either (a :~: b) (Not (a :~: b))

decEq :: SNat a -> SNat b -> DecidableEquality a b
decEq SZero SZero = Left Refl
decEq (SSucc x') (SSucc y') = case decEq x' y' of
    Left Refl -> Left Refl
    Right contra -> Right (\case Refl -> contra Refl)
decEq SZero (SSucc _) = Right (\case)
decEq (SSucc _) SZero = Right (\case)

exFalsoQuodlibet :: Void -> a
exFalsoQuodlibet = absurd

cadr' :: DecidableEquality n 'Zero -> SNat n -> a -> Vec a n -> a
cadr' (Left Refl) _ deflt _ = deflt
cadr' (Right contra) n _ v = case n of
    SZero -> exFalsoQuodlibet (contra Refl)
    SSucc _ -> safeHead v

{--------------------------------------------------------------------------------------------------}
-- Implicit passing?
-- ...

type Predicate k = k ~> Type
type Decide p = forall a. Sing a -> Decision (p @@ a)
class Decidable p where
    decide :: Decide p

-- data EqualZero :: Predicate Nat where
--     IsZero :: EqualZero 'Zero

-- type instance Apply EqualZero a = IsZero

-- FIXME: derive function symbols here
-- $(genDefunSymbols [''EqualZero])

-- type EqualZeroSym0 :: (~>) Nat Type
-- data EqualZeroSym0 a where EqualZeroSym0KindInference :: EqualZeroSym0 a
-- type instance Apply EqualZeroSym0 a = EqualZeroSym1 a
-- type EqualZeroSym1 (a :: Nat) = EqualZero a :: Type

-- instance Decidable EqualZero where
--     decide :: forall a. Sing a -> Decision (EqualZero a)
--     decide sa = _

-- cadr'' :: (Decidable EqualZeroSym0) => SNat n -> a -> Vec a n -> a
-- cadr'' n deflt v = case decide n of
--     (Proved IsZero)     -> deflt
--     (Disproved contra)  -> case n of
--         SZero -> exFalsoQuodlibet (contra Refl)
--         SSucc _ -> safeHead v
