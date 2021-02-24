
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- https://www.youtube.com/watch?v=ZoygbBiLo-w
-- https://talks.jle.im/lambdaconf-2017/singletons/singleton-slides.html
module SimpleDataKinds where

import Data.Kind    ( Type )

{--------------------------------------------------------------------------------------------------}

data Nat = Z | S Nat
    deriving (Show, Eq)
{-
Should give us:
Nat :: BOX
Z :: Nat
S :: Nat -> Nat
-}

data Vec :: Type -> Nat -> Type where
    Nil     ::                  Vec a 'Z
    Cons    :: a -> Vec a n ->  Vec a ('S n)

deriving instance Show a => Show (Vec a b)

safeHead :: Vec a ('S n) -> a
safeHead (Cons x _) = x

safeTail :: Vec a ('S n) -> Vec a n
safeTail (Cons _ xs) = xs

exampleVec :: Vec Int ('S ('S 'Z))
exampleVec = Cons 1 $ Cons 2 Nil

{--------------------------------------------------------------------------------------------------}

data DoorState = Opened | Closed | Locked
  deriving (Show, Eq)

--data Door (s :: DoorState) = UnsafeMkDoor
data Door :: DoorState -> Type where
    UnsafeMkDoor :: Door s

deriving instance Show (Door s)


closeDoor :: Door 'Opened -> Door 'Closed
closeDoor UnsafeMkDoor = UnsafeMkDoor

-- Singleton type for DoorState
data SingDS :: DoorState -> Type where
    SOpened :: SingDS 'Opened
    SClosed :: SingDS 'Closed
    SLocked :: SingDS 'Locked

-- Explicit parameter
doorStatus' :: forall s. SingDS s -> Door s -> DoorState
doorStatus' SOpened UnsafeMkDoor = Opened
doorStatus' SClosed UnsafeMkDoor = Closed
doorStatus' SLocked UnsafeMkDoor = Locked

initializeDoor' :: forall s. SingDS s -> Door s
initializeDoor' SOpened = UnsafeMkDoor
initializeDoor' SClosed = UnsafeMkDoor
initializeDoor' SLocked = UnsafeMkDoor

-- Implicit parameter
class SingDSI s where
    singDS :: SingDS s
instance SingDSI 'Opened where
    singDS = SOpened
instance SingDSI 'Closed where
    singDS = SClosed
instance SingDSI 'Locked where
    singDS = SLocked

doorStatus :: forall s. SingDSI s => Door s -> DoorState
doorStatus = doorStatus' singDS

initializeDoor :: forall s. SingDSI s => Door s
initializeDoor = initializeDoor' singDS

myDoor0 = initializeDoor @'Opened

{--------------------------------------------------------------------------------------------------}

data SomeDoor :: Type where
    MkSomeDoor :: SingDSI s => Door s -> SomeDoor

myDoor1 = MkSomeDoor myDoor0

-- Why the fucking hell does this work
myDoor1status = case myDoor1 of MkSomeDoor d -> doorStatus d

-- But we can't get the door out now
-- Error: Couldn't match ... because type variable ‘s’ would escape its scope
--myDoor1' = case myDoor1 of MkSomeDoor d -> d
