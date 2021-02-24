
{-
Run this:
    stack ghci --ghci-options="-XPartialTypeSignatures -Wno-partial-type-signatures -Wno-unticked-promoted-constructors" \
        src/SimpleSingletons.hs
so you can test type instances like:
    :instances Sing _
Use ":k!" to evaluate types:
    >>> :k! (Sing 'Opened)
    (Sing 'Opened) :: Type
    = SDoorState 'Opened

-}

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# OPTIONS_GHC
    -Wno-missing-signatures
    -fenable-th-splice-warnings
#-}
{-  Not disabled by default:
    -Wno-incomplete-patterns
        this helps when the pattern exhaustion check fails on pattern synonyms    
-}

-- https://blog.jle.im/entry/introduction-to-singletons-1.html
-- https://www.youtube.com/watch?v=ZoygbBiLo-w
-- https://talks.jle.im/lambdaconf-2017/singletons/singleton-slides.html

module SimpleSingletons where

import Data.Kind    ( Type )

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude

{--------------------------------------------------------------------------------------------------}

$(singletons [d|
    data DoorState = Opened | Closed | Locked
        deriving (Show, Eq)
    |])
-- generates:
-- data Sing :: ... SOpened, SClosed, SLocked
-- instance SingI 'Opened where ...

--data Door (s :: DoorState) = UnsafeMkDoor
data Door :: DoorState -> Type where
    UnsafeMkDoor :: { doorMaterial :: String } -> Door s
deriving instance Show (Door s)

-- doorMaterial :: Door s -> String
-- doorMaterial (UnsafeMkDoor x) = x

closeDoor :: Door 'Opened -> Door 'Closed
closeDoor (UnsafeMkDoor x) = UnsafeMkDoor x

openDoor :: Door 'Closed -> Door 'Opened
openDoor (UnsafeMkDoor x) = UnsafeMkDoor x

lockDoor :: Door 'Closed -> Door 'Locked
lockDoor (UnsafeMkDoor x) = UnsafeMkDoor x

-- The only allowed way to make a door safely
initDoor :: String -> Door 'Closed
initDoor = UnsafeMkDoor @'Closed

{--------------------------------------------------------------------------------------------------}

-- Explicit parameter

-- "reflection"
doorStatus' :: forall s. Sing s -> Door s -> DoorState
doorStatus' s _ = fromSing s
-- doorStatus' Sing _ = fromSing (sing @s)  -- Gibt mecker...

-- doorStatus' SOpened (UnsafeMkDoor _) = Opened
-- doorStatus' SClosed (UnsafeMkDoor _) = Closed
-- doorStatus' SLocked (UnsafeMkDoor _) = Locked

-- Bad function actually
-- initializeDoor' :: forall s. Sing s -> String -> Door s
-- initializeDoor' SOpened x = UnsafeMkDoor x
-- initializeDoor' SClosed x = UnsafeMkDoor x
-- initializeDoor' SLocked x = UnsafeMkDoor x

mkDoor :: forall s. SDoorState s -> String -> Door s
mkDoor _ = UnsafeMkDoor

lockAnyDoor' :: forall (s :: DoorState). Sing s -> Door s -> Door 'Locked
lockAnyDoor' SOpened = lockDoor . closeDoor
lockAnyDoor' SClosed = lockDoor
lockAnyDoor' SLocked = id
-- lockAnyDoor' Sing = lockAnyDoor     -- Mecker: Pattern match(es) are non-exhaustive

-- Explicit to implicit
withSingDoor :: forall (s :: DoorState) r. Sing s -> (SingI s => r) -> r
withSingDoor = withSingI
-- withSingDoor sng x = case sng of
--     SOpened     -> x
--     SClosed     -> x
--     SLocked     -> x

-- And we can write this (see def of lockAnyDoor below)
lockAnyDoor'' :: forall (s :: DoorState). Sing s -> Door s -> Door 'Locked
lockAnyDoor'' sng = withSingDoor sng lockAnyDoor

{--------------------------------------------------------------------------------------------------}

-- Implicit parameter

doorStatus :: forall s. SingI s => Door s -> DoorState
doorStatus _ = fromSing (sing @s)
-- doorStatus = doorStatus' Sing
-- doorStatus = doorStatus' sing
-- doorStatus _ = case sing @s of
--     SOpened     -> Opened
--     SClosed     -> Closed
--     SLocked     -> Locked

-- initializeDoor :: forall s. SingI s => Door s
-- initializeDoor = initializeDoor' sing

lockAnyDoor :: forall s. SingI s => Door s -> Door 'Locked
lockAnyDoor = lockAnyDoor' sing

myDoor0 = mkDoor SClosed "Maple"
-- mkDoor cannot be abused
--      myDoor0' = mkDoor SClosed "Maple" :: Door 'Opened
-- yields an error: Couldn't match type ‘'Closed’ with ‘'Opened’

{--------------------------------------------------------------------------------------------------}
{-
SOpened :: SDoorState 'Opened       -- constructor
SDoorState :: DoorState -> Type     -- datatype of all doorstate singletons

-}
{--------------------------------------------------------------------------------------------------}

{-
Interesting splices:
    SDecide

Less interesting?
    PShow, SShow, PEq, SEq
    Data.Type.Equality.TestEquality
    Data.Type.Coercion.TestCoercion

Sing :: k -> Type

There is pattern synonym for Sing, but i'm not sure how it works:
    pattern Sing :: forall k (a :: k). () => SingI a => Sing a
    pattern Sing <- (singInstance -> SingInstance)
      where Sing = sing
    -- That's why GHCI would sometimes give the type of sing as
        Sing :: forall k (a :: k). SingI a => Sing a

SingI :: k -> Constraint
    sing :: forall k (a :: k). SingI a => Sing a
    -- Fetch a Sing out of a typeclass (implicit passing)

-- Kind class!
SingKind :: Type -> Constraint
    Demote :: Type -> Type
    fromSing :: forall k (a :: k). SingKind k => Sing a -> Demote k
    toSing :: SingKind k => Demote k -> SomeSing k

data DoorState_aK4U
    = Opened_aK4V | Closed_aK4W | Locked_aK4X
    deriving (Show, Eq)

data SDoorState :: DoorState_aK4U -> Type
    where
        SOpened :: SDoorState (Opened_aK4V :: DoorState_aK4U)
        SClosed :: SDoorState (Closed_aK4W :: DoorState_aK4U)
        SLocked :: SDoorState (Locked_aK4X :: DoorState_aK4U)

type instance Sing @DoorState_aK4U = SDoorState
!!  Sing 'Opened :: Type = SDoorState 'Opened

class SingKind k where  -- k = DoorState
    -- | Get a base type from the promoted kind. For example,
    -- @Demote Bool@ will be the type @Bool@. Rarely, the type and kind do not
    -- match. For example, @Demote Nat@ is @Natural@.
    type Demote k = (r :: Type) | r -> k
    -- Demote DoorState = DoorState

    -- | Convert a singleton to its unrefined version.
    fromSing :: Sing (a :: k) -> Demote k
    fromSing (SOpened :: Sing ('Opened :: DoorState)) = Opened_aK4V

    -- | Convert an unrefined type to an existentially-quantified singleton type.
    toSing   :: Demote k -> SomeSing k

instance SingKind DoorState_aK4U where
    type Demote DoorState_aK4U = DoorState_aK4U
    fromSing SOpened = Opened_aK4V
    fromSing SClosed = Closed_aK4W
    fromSing SLocked = Locked_aK4X
    toSing Opened_aK4V = SomeSing SOpened
    toSing Closed_aK4W = SomeSing SClosed
    toSing Locked_aK4X = SomeSing SLocked


-}

ex01 = fromSing SOpened == Opened
ex02 = toSing Opened    -- SomeSing SOpened :: SomeSing DoorState
ex03 = SOpened `SCons` SClosed `SCons` SNil -- ex03 :: SList '[ 'Opened, 'Closed]
-- ghci> :t SOpened `SCons` SClosed `SCons` SLocked `SCons` SNil

{--------------------------------------------------------------------------------------------------}
-- Exercises for Pt. 1

-- a function to unlock a door, but only if the user enters an odd number (as a password).
-- This has to be unsafe, we don't have any function that deals with locked doors yet
unlockDoor :: Int -> Door 'Locked -> Maybe (Door 'Closed)
unlockDoor i (UnsafeMkDoor x)
    | odd i     = Just $ UnsafeMkDoor x
    | otherwise = Nothing

-- open any door, taking a password, in “implicit Sing” style
openAnyDoor :: forall s. SingI s => Int -> Door s -> Maybe (Door 'Opened)
openAnyDoor i = case sing @s of
    SOpened -> Just
    SClosed -> Just . openDoor
    SLocked -> fmap openDoor . unlockDoor i

{--------------------------------------------------------------------------------------------------}

data SomeDoor where
    MkSomeDoor :: Sing s -> Door s -> SomeDoor

deriving instance Show SomeDoor
-- data SomeDoor :: Type where
--     MkSomeDoor :: SingI s => Door s -> SomeDoor

fromDoor :: forall (s :: DoorState). SingI s => Door s -> SomeDoor
fromDoor = MkSomeDoor (sing @s)

myDoor1 = fromDoor myDoor0
myDoor1Status = case myDoor1 of (MkSomeDoor s _) -> fromSing s

closeSomeOpenedDoor :: SomeDoor -> Maybe SomeDoor
closeSomeOpenedDoor (MkSomeDoor s d) = case s of
    SOpened     -> Just . fromDoor $ closeDoor d
    SClosed     -> Nothing
    SLocked     -> Nothing

lockAnySomeDoor :: SomeDoor -> SomeDoor
lockAnySomeDoor (MkSomeDoor s d) = fromDoor $ withSingI s (lockAnyDoor d)

-- But we can't get the door out now
-- Error: Couldn't match ... because type variable ‘s’ would escape its scope
--myDoor1' = case myDoor1 of MkSomeDoor s d -> d

-- As a fun exercise, write out the explicit isomorphism
isoSomeSingDoorState :: (DoorState -> SomeSing DoorState, SomeSing DoorState -> DoorState)
isoSomeSingDoorState = (to, from) where
    to :: DoorState -> SomeSing DoorState
    to = toSing
    -- to Opened = SomeSing (SOpened :: SDoorState 'Opened)
    -- to Closed = SomeSing SClosed
    -- to Locked = SomeSing SLocked
    from :: SomeSing DoorState -> DoorState
    from (SomeSing ds) = fromSing ds
    -- from (SomeSing SOpened) = Opened
    -- from (SomeSing SClosed) = Closed
    -- from (SomeSing SLocked) = Locked

{-
In the language of dependently typed programming, we call SomeDoor
a dependent sum, because you can imagine it basically as a sum type:
-}
data SomeDoor'
    = SDOpened (Door 'Opened)
    | SDClosed (Door 'Closed)
    | SDLocked (Door 'Locked)

-- If we only know the types at runtime...
-- mkSomeDoor :: DoorState -> String -> SomeDoor
-- mkSomeDoor Opened = fromDoor . mkDoor SOpened
-- mkSomeDoor Closed = fromDoor . mkDoor SClosed
-- mkSomeDoor Locked = fromDoor . mkDoor SLocked

-- Reification: Lifts DoorState to the type level (as long a f is polymorphic!)
-- withDoor :: forall r. DoorState -> String
--     -> (forall s. Sing s -> Door s -> r)
--     -> r
-- withDoor s m f = case s of
--     Opened -> f SOpened $ mkDoor SOpened m
--     Closed -> f SClosed $ mkDoor SClosed m
--     Locked -> f SLocked $ mkDoor SLocked m

-- And now, actually using the singletons library's power
mkSomeDoor :: DoorState -> String -> SomeDoor
mkSomeDoor (FromSing sng) = MkSomeDoor sng . mkDoor sng     -- Mecker, mecker
-- mkSomeDoor ds = withSomeSing ds $ \sng ->
--     MkSomeDoor sng . mkDoor sng
-- mkSomeDoor ds = case toSing ds of
--     SomeSing s -> MkSomeDoor s . mkDoor s

-- Then run a dependently typed function on it...
withDoor :: forall r. DoorState -> String
    -> (forall s. Sing s -> Door s -> r)
    -> r
withDoor ds m f = withSomeSing ds $ \s -> 
    f s $ mkDoor s m

{--------------------------------------------------------------------------------------------------}
-- Exercises for Pt. 2


{-  If the door is successfully unlocked (with a Just), return the unlocked
     door in a SomeDoor. Otherwise, return the original locked door (in a SomeDoor).
-}
unlockSomeDoor :: Int -> Door 'Locked -> SomeDoor
unlockSomeDoor i ld = maybe (fromDoor ld) fromDoor (unlockDoor i ld)
-- unlockSomeDoor i ld = case unlockDoor i ld of
--     Just cd     -> fromDoor cd
--     Nothing     -> fromDoor ld

--openAnyDoor :: forall s. SingI s => Int -> Door s -> Maybe (Door 'Opened)

openAnySomeDoor :: Int -> SomeDoor -> SomeDoor
openAnySomeDoor i sd@(MkSomeDoor Sing d) =      -- Mecker mecker.
    maybe sd fromDoor $ openAnyDoor i d
-- This works just fine, dear pattern checker, i promise.

-- Write the SingKind instance for the promoted kind of a custom list type
-- other file because of name clashes

{--------------------------------------------------------------------------------------------------}
