
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds            #-}

{-  LANGUAGE AllowAmbiguousTypes  #-}


{-# OPTIONS_GHC
    -fenable-th-splice-warnings
    -Wno-unused-imports
    -Wno-unticked-promoted-constructors
#-}


-- Testing stuff on Data.Comp.SubsumeCommon

module Compdata.SubsumeCommon where

import Data.Kind    ( Type, Constraint )
import Data.Void

{--------------------------------------------------------------------------------------------------}
-- Data.Comp.Internal.SubsumeCommon

-- | This type is used in its promoted form only. It represents
-- pointers from the left-hand side of a subsumption to the right-hand
-- side.
data Pos = Here | Le Pos | Ri Pos | Sum Pos Pos

-- | This type is used in its promoted form only. It represents
-- possible results for checking for subsumptions. 'Found' indicates a
-- subsumption was found; 'NotFound' indicates no such subsumption was
-- found. 'Ambiguous' indicates that there are duplicates on the left-
-- or the right-hand side.
data Emb = Found Pos | NotFound | Ambiguous

data Proxy a = P


type family Choose (e1 :: Emb) (r :: Emb) :: Emb where
    Choose (Found x) (Found y) = Ambiguous
    Choose Ambiguous y = Ambiguous
    Choose x Ambiguous = Ambiguous
    Choose (Found x) y = Found (Le x)
    Choose x (Found y) = Found (Ri y)
    Choose x y = NotFound


type family Sum' (e1 :: Emb) (r :: Emb) :: Emb where
    Sum' (Found x) (Found y) = Found (Sum x y)
    Sum' Ambiguous y = Ambiguous
    Sum' x Ambiguous = Ambiguous
    Sum' NotFound y = NotFound
    Sum' x NotFound = NotFound


-- | This type family takes a position type and compresses it. That
-- means it replaces each nested occurrence of
--
-- @
--   Sum (prefix (Le Here)) (prefix (Ri Here))@
-- @
---
-- with
--
-- @
--   prefix Here@
-- @
--
-- where @prefix@ is some composition of @Le@ and @Ri@. The rational
-- behind this type family is that it provides a more compact proof
-- term of a subsumption, and thus yields more efficient
-- implementations of 'inj' and 'prj'.

type family ComprPos (p :: Pos) :: Pos where
    ComprPos Here = Here
    ComprPos (Le p) = Le (ComprPos p)
    ComprPos (Ri p) = Ri (ComprPos p)
    ComprPos (Sum l r) = CombineRec (ComprPos l) (ComprPos r)


-- | Helper type family for 'ComprPos'. Note that we could have
-- defined this as a type synonym. But if we do that, performance
-- becomes abysmal. I presume that the reason for this huge impact on
-- performance lies in the fact that right-hand side of the defining
-- equation duplicates the two arguments @l@ and @r@.
type family CombineRec l r where
    CombineRec l r = CombineMaybe (Sum l r) (Combine l r)

-- | Helper type family for 'ComprPos'.
type family CombineMaybe (p :: Pos) (p' :: Maybe Pos) where
    CombineMaybe p (Just p') = p'
    CombineMaybe p p'        = p


-- | Helper type family for 'ComprPos'.
type family Combine (l :: Pos) (r :: Pos) :: Maybe Pos where
    Combine (Le l) (Le r) = Le' (Combine l r)
    Combine (Ri l) (Ri r) = Ri' (Combine l r)
    Combine (Le Here) (Ri Here) = Just Here
    Combine l r = Nothing

-- | 'Ri' lifted to 'Maybe'.
type family Ri' (p :: Maybe Pos) :: Maybe Pos where
    Ri' Nothing = Nothing
    Ri' (Just p) = Just (Ri p)

-- | 'Le' lifted to 'Maybe'.
type family Le' (p :: Maybe Pos) :: Maybe Pos where
    Le' Nothing = Nothing
    Le' (Just p) = Just (Le p)


-- | If the argument is not 'Found', this type family is the
-- identity. Otherwise, the argument is of the form @Found p@, and
-- this type family does two things: (1) it checks whether @p@ the
-- contains duplicates; and (2) it compresses @p@ using 'ComprPos'. If
-- (1) finds no duplicates, @Found (ComprPos p)@ is returned;
-- otherwise @Ambiguous@ is returned.
--
-- For (1) it is assumed that @p@ does not contain 'Sum' nested
-- underneath a 'Le' or 'Ri' (i.e. only at the root or underneath a
-- 'Sum'). We will refer to such positions below as /atomic position/.
-- Positions not containing 'Sum' are called /simple positions/.
type family ComprEmb (e :: Emb) :: Emb where
    ComprEmb (Found p) = Check (Dupl p) (ComprPos p)
    ComprEmb e = e

-- | Helper type family for 'ComprEmb'.
type family Check (b :: Bool) (p :: Pos) where
    Check False p = Found p
    Check True  p = Ambiguous

-- | This type family turns a list of /atomic position/ into a list of
-- /simple positions/ by recursively splitting each position of the
-- form @Sum p1 p2@ into @p1@ and @p2@.
type family ToList (s :: [Pos]) :: [Pos] where
    ToList (Sum p1 p2 ': s) = ToList (p1 ': p2 ': s)
    ToList (p ': s) = p ': ToList s
    ToList '[] = '[]

-- | This type checks whether the argument (atomic) position has
-- duplicates.
type Dupl s = Dupl' (ToList '[s])

-- | This type family checks whether the list of positions given as an
-- argument contains any duplicates.
type family Dupl' (s :: [Pos]) :: Bool where
    Dupl' (p ': r) = OrDupl' (Find p r) r
    Dupl' '[] = False

-- | This type family checks whether its first argument is contained
-- its second argument.
type family Find (p :: Pos) (s :: [Pos]) :: Bool where
    Find p (p ': r)  = True
    Find p (p' ': r) = Find p r
    Find p '[] = False

-- | This type family returns @True@ if the first argument is true;
-- otherwise it checks the second argument for duplicates.
type family OrDupl' (a :: Bool) (b :: [Pos]) :: Bool where
    OrDupl'  True  c  = True
    OrDupl'  False c  = Dupl' c

{--------------------------------------------------------------------------------------------------}
-- Data.Comp.Ops

infixr 6 :+:

data (f :+: g) e = Inl (f e)
                 | Inr (g e)

type family Elem (f :: Type -> Type) (g :: Type -> Type) :: Emb where
    Elem f f = Found Here
    Elem (f1 :+: f2) g =  Sum' (Elem f1 g) (Elem f2 g)
    Elem f (g1 :+: g2) = Choose (Elem f g1) (Elem f g2)
    Elem f g = NotFound

{--------------------------------------------------------------------------------------------------}
-- Our test

type ElemTest01 f g = Elem f (f :+: g)

data EF0 a = EF0    deriving Functor
data EF1 a = EF1    deriving Functor
data EF2 a = EF2    deriving Functor
data EF3 a = EF3    deriving Functor

type EFSig = EF0 :+: EF1 :+: EF2

data Some f a
    = Some (f a)

data MaybeSome f
    = NotReally
    | FUnit (f ())
    | FVoid (f Void)

sum0 :: EF0 a
sum0 = EF0

sum1 :: (EF0 :+: EF1) a
sum1 = Inr EF1

fElemTest01 :: forall f g x. (Functor f, Functor g, Elem f (f :+: g) ~ Found (Le x))
            => g Void -> f () -> g ()
fElemTest01 gv _ = vacuous gv

-- This works for concrete types EF0, EF1
elemTest01 :: EF0 ()
elemTest01 = fElemTest01 EF0 EF1

-- What if the types are undetermined?
-- elemTest02 :: (Functor f, Functor g) => f () -> g Void -> g ()
-- elemTest02 fu gv = fElemTest01 gv fu

-- Couldn't match type ‘Elem f (f :+: g)’ with ‘'Found ('Le x0)’
{- We would have to provide the additional constraint
    Elem f (f :+: g) ~ ...

Which is undecidable for undetermined f and g, because f could occur in g.
This is why we can't even do simple things in compdata like:
-}

-- Inject a term into a sum
-- injectF :: (Functor f) => Cxt h f a -> Cxt h (f :+: g) a
-- injectF = deepInject'
