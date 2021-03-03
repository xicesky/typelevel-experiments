
{-# LANGUAGE GADTs, TypeOperators, DataKinds, PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}

-- https://www.youtube.com/watch?v=6snteFntvjM
-- https://github.com/goldfirere/glambda
module Typelevel.SimpleGADTs where

{--------------------------------------------------------------------------------------------------}
-- | A very simple newtype wrapper
newtype Wrap a = Wrap a
    deriving Show

data STy ty where
    SInt    ::                      STy Int
    SBool   ::                      STy Bool
    SMaybe  :: STy ty' ->           STy (Maybe ty')
    SWrap   :: STy ty' ->           STy (Wrap ty')
    SList   :: STy ty' ->           STy [ty']
    SUnit   ::                      STy ()
    SArrow  :: STy a -> STy b ->    STy (a -> b)

deriving instance Show (STy ty)

{- ... desugares to:    -}

-- data STy ty
--     = (ty ~ Int)                    => SInt
--     | (ty ~ Bool)                   => SBool
--     | forall ty'. (ty ~ Maybe ty')  => SMaybe (STy ty)

zero :: STy ty -> ty
zero SInt           = 0
zero SBool          = False
zero (SMaybe _)     = Nothing
zero (SWrap ty)     = Wrap $ zero ty
zero (SList _)      = []
zero SUnit          = ()
zero (SArrow _ b)   = const $ zero b

eqSTy :: STy ty -> STy ty -> Bool
eqSTy  SInt        SInt       = True
eqSTy  SBool       SBool      = True
eqSTy (SMaybe x ) (SMaybe y ) = x `eqSTy` y
-- eqSTy (SInt     ) (SBool    ) = True     -- W: Inaccessible code in ...
eqSTy _           _           = False   -- Just so the function actually does sth

{--------------------------------------------------------------------------------------------------}

data HList tys where
    Nil :: HList '[]
    (:>) :: h -> HList t -> HList (h ': t)
infixr 5 :>

blah :: HList '[Bool, (), [Maybe Char], Integer, [Char]]
blah = True :> () :> [Just 'x'] :> (5:: Integer) :> "Hello" :> Nil

data Elem list elt where
    EZ :: Elem (x ': xs) x
    ES :: Elem xs x -> Elem (y ': xs) x

hlookup :: Elem tys ty -> HList tys -> ty
--hlookup _       Nil         = error "Empty List"    -- No warning
hlookup EZ      (x :> _ )   = x
hlookup (ES n)  (_ :> xs)   = hlookup n xs
--hlookup _       Nil         = error "Empty List"    -- Pattern match is redundant

-- hlookup $ ES $ ES $ EZ :: HList (y1 : y2 : ty : xs) -> ty

{--------------------------------------------------------------------------------------------------}

