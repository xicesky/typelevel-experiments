
module TermRepresentation.Proof where

import Data.Kind (Type)
import Data.Void
import Data.Proxy

type V = Void

data Stuff :: Type -> Type -> Type where
    SLeft :: !t1 -> Stuff t1 t2
    SRight :: !t2 -> Stuff t1 t2
    deriving (Show, Eq)

data NotStuff :: Type -> Type -> Type where
    NotStuff :: NotStuff t1 t2
    deriving (Show, Eq)

data T1 = T1
    deriving (Show, Eq)
data T2 = T2
    deriving (Show, Eq)

{- Guarantee #1
    The parameters to "Stuff" and "NotStuff" are either Void or T1 / T2
-}

{- Guarantee #2
    blubb is one of these types:
        blubb :: Stuff a V -> NotStuff a x -> Stuff a x
        blubb :: Stuff V b -> NotStuff x b -> Stuff x b
-}

{-
    #2 together with #1 this means it is either:
        blubb :: Stuff T1 V -> NotStuff T1 x -> Stuff T1 x
        blubb :: Stuff V T2 -> NotStuff x T2 -> Stuff x T2
    where "x" is still free.
    This should be determined by the instance paramters,
    for example "Blubb T1 V" has the first type.
-}

-- class Blubb a b where
--     blubb :: Stuff a b -> NotStuff a b -> Stuff a b

-- {-----------------------------------------------------------------------------}
-- {-
--     We could, of course, make them seperate classes
-- -}
-- class Blubb1 a where
--     blubb1 :: Stuff a V -> NotStuff a b -> Stuff a b

-- class Blubb2 b where
--     blubb2 :: Stuff V b -> NotStuff a b -> Stuff a b

-- instance Blubb1 T1 where
--     blubb1 (SLeft a) NotStuff = SLeft a

-- instance Blubb1 V where
--     blubb1 x = case x of {}

-- instance Blubb2 T2 where
--     blubb2 (SRight b) NotStuff = SRight b

-- instance Blubb2 V where
--     blubb2 x = case x of {}

-- instance (Blubb1 a, Blubb2 b) => Blubb a b where
--     blubb (SLeft a) = blubb1 (SLeft a)
--     blubb (SRight b) = blubb2 (SRight b)

{-----------------------------------------------------------------------------}
-- We know that the output type can be deduced from the input types

data ComputeP t
    = CompJust t t
    | CompJoin t t (ComputeP t) (ComputeP t)

type family HowToComp a b :: ComputeP Type where
    HowToComp V V = 'CompJust V V
    HowToComp a V = 'CompJust a V
    HowToComp V b = 'CompJust V b
    HowToComp a b = 'CompJoin a b (HowToComp a V) (HowToComp V b)

class BlubbArg a b a' b' (c :: ComputeP Type) where
    blubbArg :: Proxy c -> Stuff a b -> NotStuff a' b' -> Stuff a' b'

instance BlubbArg V V a' b' ('CompJust V V) where
    blubbArg _ x _ = case x of {}

instance (BlubbArg a' V a b l, BlubbArg V b' a b r)
    => BlubbArg a' b' a b ('CompJoin a' b' l r) where
    blubbArg _ (SLeft a) = blubbArg @a' @V (Proxy :: Proxy l) (SLeft a)
    blubbArg _ (SRight a) = blubbArg @V @b' (Proxy :: Proxy r) (SRight a)

instance BlubbArg a' V a' b' ('CompJust a' V) where
    blubbArg _ (SLeft a) NotStuff = SLeft a

instance BlubbArg V b' a' b' ('CompJust V b') where
    blubbArg _ (SRight a) NotStuff = SRight a

type Blubb' a b = (BlubbArg a b a b (HowToComp a b))

blubb' :: forall a b a' b'. (BlubbArg a b a' b' (HowToComp a b))
    => Stuff a b -> NotStuff a' b' -> Stuff a' b'
blubb' = blubbArg (Proxy :: Proxy (HowToComp a b))

{- ... but this doesn' scale well. For our boolean terms with
    5 arguments, we need ComputeP to split at least 5 ways,
    necessitating more than 10 instances, and we can't generalize it
    over all computations (since the possibilites to split are
    different).
-}
{-----------------------------------------------------------------------------}
-- Checks

-- It should now be possible to use "blubb" on Stuff a V
test1 :: Bool
test1 = let
    f :: (Blubb' a V) => Stuff a V -> Stuff a V
    f s = blubb' s NotStuff
    in f (SLeft T1) == SLeft T1

-- More generally, any combination of a and b must work
propBlubb :: (Eq a, Eq b) => Stuff a b -> (Stuff a b -> NotStuff a b -> Stuff a b) -> Bool
propBlubb s bl = s == bl s NotStuff

test2 :: Bool
test2 = propBlubb @T1 @V (SLeft T1) blubb'
    && propBlubb @V @T2 (SRight T2) blubb'

-- And this should fail to typecheck
-- fail1 :: Stuff T2 V -> Stuff T2 V
-- fail1 s = blubb s NotStuff      -- error: No instance for (Blubb1 T2)
