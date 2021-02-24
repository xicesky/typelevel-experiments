{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# OPTIONS_GHC
    -Wno-missing-signatures
    -fenable-th-splice-warnings
#-}

module SimpleSingletonsEx01 where

import Data.Kind    ( Type )

import Data.Singletons

data List a = Nil | Cons a (List a)

data SList :: List a -> Type where
    SNil  :: SList 'Nil
    SCons :: Sing x -> SList xs -> SList ('Cons x xs)

type instance Sing = SList

instance SingKind k => SingKind (List k) where
    type Demote (List k) = List (Demote k)

    -- Instance sig: forall (xs :: List k). Sing xs -> List (Demote k)
    --    Class sig: forall (a :: List k). Sing a -> Demote (List k)
    fromSing :: Sing (xs :: List k) -> List (Demote k)
    fromSing SNil = Nil
    fromSing (SCons x xs) = fromSing x `Cons` fromSing xs

    toSing :: List (Demote k) -> SomeSing (List k)
    toSing Nil = SomeSing SNil
    toSing (Cons x xs) = case (toSing x, toSing xs) of
        (SomeSing x', SomeSing xs') -> SomeSing $ x' `SCons` xs'
