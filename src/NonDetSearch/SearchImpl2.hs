
{-# OPTIONS_GHC
    -Wno-unused-imports
#-}

{-
Ideas from Minisat: http://minisat.se/downloads/MiniSat.pdf
TODO:
    Use fused-effects https://hackage.haskell.org/package/fused-effects
    or http://hackage.haskell.org/package/polysemy
-}
module NonDetSearch.SearchImpl2 where

-- containers
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

data Constraint = Constraint
    deriving (Show, Eq, Ord)
data Clause = Clause
    deriving (Show, Eq, Ord)

newtype Variable = Variable { getVariable :: Int }
    deriving (Show, Eq, Ord)
newtype Literal = Literal { getLiteral :: Int }
    deriving (Show, Eq, Ord)

-- | Assigned literals per decision level, chronological (newest fist)
type Trail = [[Literal]]

trailSize :: Trail -> Int
trailSize = sum . fmap length

newtype ConstraintPtr = ConstraintPtr { getConstraintPtr :: Int }
    deriving (Show, Eq, Ord)

type MBool = Maybe Bool

{-----------------------------------------------------------------------------}

data Solver = Solver
    {   constraints     :: ! (Map Int Constraint)
        -- ^ List of problem constraints.
    ,   learntClauses   :: ! (Map Int Clause)
        -- ^ List of learnt clauses.
    ,   watches         :: ! (Map Literal (Set ConstraintPtr))
        -- ^ For each literal 'p', a list of constraints watching 'p'.
    ,   reason          :: ! (Map Variable ConstraintPtr)
        -- ^ For each variable, the constraint that implied its value.
    }

nConstraints :: Solver -> Int
nConstraints = Map.size . constraints

-- ...

{-----------------------------------------------------------------------------}

-- | Local solver state (may be backtracked)
data LocalSolver = LocalSolver
    {   assignments     :: [MBool]          -- FIXME need fast indexing
        -- ^ The current assignments indexed on variables.
    ,   trail           :: Trail
        -- ^ The current trail of assignments
    }

nVariables :: LocalSolver -> Int
nVariables = length . assignments

nAssigns :: LocalSolver -> Int
nAssigns = trailSize . trail

decisionLevel :: LocalSolver -> Int
decisionLevel = length . trail

{-----------------------------------------------------------------------------}

{- Note: constraint must be:
    sorted
    cleaned of dups
    non-empty / non-contradictory
-}
addConstraint :: Constraint -> Solver -> Solver
addConstraint c solver  -- NEED LENS! :(
    = let
        ptr = nConstraints solver   -- FIXME assert not Map.elem ptr
        c' = Map.insert ptr c (constraints solver)
        -- LENS here
        -- Insert watches for first two literals
        w' = Map.adjust
            (Set.insert (ConstraintPtr ptr))
            (Literal 1) (watches solver)
    in solver
        {   constraints = c'
        ,   watches = w'
        }

removeConstraint :: ConstraintPtr -> Solver -> Solver
removeConstraint = error "NYI"

{-----------------------------------------------------------------------------}

