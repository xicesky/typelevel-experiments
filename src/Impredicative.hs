
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}


-- Finally getting a grasp on what impredicative types are
-- https://www.youtube.com/watch?v=ZuNMo136QqI

module Impredicative where

import Prelude
    (   Bool(..), Maybe(..), Int, Char
    ,   (+)
    )
import qualified Prelude as P

-- Just for clarification of the types
not :: Bool -> Bool
not = P.not

reverse :: forall a. [a] -> [a]
reverse = P.reverse

id :: forall a. a -> a
id = P.id

cons :: forall a. a -> [a] -> [a]
cons = (:)

listOfFunctions1 = [not, id]
-- GHC infers correctly: [Bool -> Bool]

-- Illegal: Couldn't match type ‘[a0]’ with ‘Bool’
-- listOfFunctions2 = [not, id, reverse]

experiment1 = reverse [not, id]
-- GHC infers correctly: [Bool -> Bool]

listOfIds :: [ forall a. a -> a ]
listOfIds = [id, id]

{-
Couldn't match type ‘forall a1. a1 -> a1’ with ‘a -> a’
    Expected type: [a -> a]
    Actual type: [forall a. a -> a]
-}
--experiment02 = id : listOfIds

-- Needs a type application, until we use GHC with QuickLook
experiment02 = cons @(forall a.a -> a) id listOfIds

f :: Maybe (forall a. [a] -> [a]) -> Maybe ([Int], [Char])
f (Just g) = Just (g [3], g "hello")
f Nothing  = Nothing

-- Monomorphism restriction = meh
plus = (+)
