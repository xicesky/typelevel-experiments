
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- Type families simulating type classes
-- https://bahr.io/pubs/files/serrano15haskell-paper.pdf

module TypeFamilyClasses where

import Data.Kind (Type)
import Data.Proxy
import GHC.TypeLits

{-# ANN module "HLint: ignore Use newtype instead of data" #-}

data Intelligence = Smart | Dumb | RaveDubin

checkCon :: forall c. c => Proxy c -> Bool
checkCon Proxy = True

-- required AllowAmbigousTypes
-- checkCon' :: forall c. c => Bool
-- checkCon' = True

{-----------------------------------------------------------------------------}
-- Ex. 1

data Zero
data Succ a

class       AddC m        n     r           | m n -> r
instance    AddC Zero     n     n
instance    AddC m        n     r
    =>      AddC (Succ m) n     (Succ r)

--

sublimeText :: Maybe Intelligence
sublimeText = dumb where dumb = Just Dumb

{-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------}
-- Ex. 2

type family AddF' m n where
    AddF' Zero n = n
    AddF' (Succ m) n = Succ (AddF' m n)

type family Equal x y where
    Equal x x = 'True
    Equal x y = 'False

{-----------------------------------------------------------------------------}

type family Family a
data Example a = Example (Family a)

f :: Example a -> Family a
f (Example x) = x

class FunDep a b | a -> b
data Example' a where
    Example' :: FunDep a b => b -> Example' a

-- Doesn't typecheck:
-- f' :: FunDep a b => Example' a -> b
-- f' (Example' x) = x

type family IsJust x where
    IsJust ('Just x) = 'True
    IsJust 'Nothing = 'False

{-----------------------------------------------------------------------------}

data Defined = Yes | No

type family IsEq' (t :: Type) :: Defined
type IsEq a = (IsEq' a ~ 'Yes)

type instance IsEq' Char = 'Yes
type instance IsEq' Int = 'Yes
type instance IsEq' Bool = 'Yes
type instance IsEq' [a] = IsEq' a


eqIdentity :: IsEq t => t -> t
eqIdentity = id

type family And (a :: Defined) (b :: Defined) where
    And 'Yes 'Yes = 'Yes
    And a    b    = 'No

-- instance (Eq a, Eq b) => Eq (a, b)
type instance IsEq' (a, b) = And (IsEq' a) (IsEq' b)

{-----------------------------------------------------------------------------}

class Collection c e | c -> e where
    empty :: c
    insert :: e -> c -> c

instance Collection [a] a where
    empty = []
    insert = (:)

-- Encode fundep in Collection c e
--  doesn't work yet: r -> e is possible, but not r c -> e
--  https://gitlab.haskell.org/ghc/ghc/-/issues/10832
--type family IsCollection (c :: Type) (e :: Type) = r | r c -> e

{-----------------------------------------------------------------------------}

-- Encoding superclasses
type family IsOrd' (t :: Type) :: Defined
type IsOrd a = (IsOrd' a ~ 'Yes, IsEq a)
-- class Eq a => Ord a where ...

gt :: IsOrd a => a -> a -> Bool
gt _ _ = True

{-----------------------------------------------------------------------------}

-- type FooMessage =
--     'Text "First line of the foo message" ':$$:
--     'Text "Second line of the foo message: " ':<>: 'ShowType ErrorMessage

-- foo :: TypeError FooMessage
-- foo = error "unreachable"

-- "never"
--type instance IsEq' (a -> b) = 'No
type instance IsEq' (a -> b) = TypeError
    (       'Text "Can't compare functions."
    ':$$:   'ShowType (a -> b)
    )

{- Try:
    checkCon (Proxy :: Proxy (IsEq (a->b)))
or
    eqIdentity id
-}

-- "Closed type class"
type family IsIntegral' t where
    IsIntegral' Int = 'Yes
    IsIntegral' Integer = 'Yes
    IsIntegral' t = TypeError ( 'ShowType t ':<>: 'Text " is not integral" )

-- Could also do this?
class (IsIntegral' a ~ 'Yes) => IntegralCompare a where
    icmp :: a -> a -> Bool
    default icmp :: Eq a => a -> a -> Bool
    icmp = (==)

instance IntegralCompare Int
instance IntegralCompare Integer
--instance IntegralCompare Bool       -- error: Bool is not integral

