
{-# OPTIONS_GHC -Wno-unused-imports #-}

module TermRepresentation.FindInjection where

import Prelude hiding (and, or, not, (&&), (||))
import qualified Prelude as P

import Data.Kind (Type)
import Data.Void
import Data.Proxy
--import Data.Fix (Fix(..))
-- import Data.Deriving
import Text.Show (showListWith)
import Data.Functor.Const
import Data.Functor.Classes
import Data.Functor.Foldable
import Control.Monad (ap)

{-# ANN module "HLint: ignore Use newtype instead of data" #-}
{-# ANN module "HLint: ignore Use camelCase" #-}


newtype Fix4 f a b c = Fix4 { unFix4 :: f a b c (Fix4 f a b c) }

data TermF a b c rec
    = Op a b rec rec
    | Var c

type Term = Fix4 TermF

data Injection
    = IHere
    | IDeconstruct [Injection]
    | ILift1 Injection

type family FindInjection s t :: Injection where
    FindInjection a a       = 'IHere
    FindInjection Void a    = 'IHere
    FindInjection (Fix4 f a b c) (Fix4 f a' b' c')    
                             = 'ILift1 (FindInjection1 (f a b c) (f a' b' c'))

-- type instance FindInjection a a = 'IHere
-- type instance FindInjection Void a = 'IHere
-- type instance FindInjection (Fix4 f a b c) (Fix4 f a' b' c')
--     = 'ILift1 (FindInjection1 (f a b c) (f a' b' c'))

type family FindInjection1 (s :: Type -> Type) (t :: Type -> Type) :: Injection

type instance FindInjection1 (TermF op val var) (TermF op' val' var')
    = 'IDeconstruct
    [   FindInjection op op'
    ,   FindInjection val val'
    ,   FindInjection var var'
    ]

