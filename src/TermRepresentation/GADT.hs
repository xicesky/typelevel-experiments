
{-# LANGUAGE PatternSynonyms #-}

{-  Let's see how well we can represent a flexible term
    type using GADTs and recursion-schemes.
-}
module TermRepresentation.GADT where

import Prelude hiding (and, or, not, (&&), (||))
import qualified Prelude as P

import Data.Kind (Type)
import Data.Void
--import Data.Fix (Fix(..))
-- import Data.Deriving
import Text.Show (showListWith)
import Data.Functor.Const
import Data.Functor.Classes
import Data.Functor.Foldable
import Control.Monad (ap)

{-# ANN module "HLint: ignore Use newtype instead of data" #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

{-----------------------------------------------------------------------------}
-- Missing bits

-- Why doesn't recusion-schemes define an algebra type?
-- (probably because there are so many different ones)
-- We are going to mostly use cata, so here we go
type Alg f a = f a -> a

-- The ever looming void functor
type VoidF = Const Void

{-----------------------------------------------------------------------------}
-- Terms

data TermF
    :: (Type -> Type) -> Type -> Type       -- Type parameters
    -> Type                                 -- Recursive term
    -> Type
    where
    ConstT      ::                  !val ->      TermF op val var rec
    VariableT   ::                  !var ->      TermF op val var rec
    RecT        :: ProperRecT op => !(op rec) ->    TermF op val var rec

deriving instance Functor (TermF op val var)
-- deriving instance Foldable (TermF op val var)
-- deriving instance Traversable (TermF op val var)

-- I'm going to reget this, am i?
class (Show1 op, Functor op, Foldable op, Traversable op) => ProperRecT op where
    -- Something like this

data Op
    :: Type -> Type -> Type -> Type -> Type
    where
    UnaryOp     :: ProperOpTag uop =>   uop -> rec          -> Op uop bop flop rec
    BinaryOp    :: ProperOpTag bop =>   bop -> rec -> rec   -> Op uop bop flop rec
    FlatOp      :: ProperOpTag flop =>  flop -> [rec]       -> Op uop bop flop rec

deriving instance Functor (Op uop bop flop)
deriving instance Foldable (Op uop bop flop)
deriving instance Traversable (Op uop bop flop)

class (Show o, Eq o, Ord o) => ProperOpTag o where
    opPrec :: o -> Int

instance ProperOpTag Void where
    opPrec = absurd

{-----------------------------------------------------------------------------}
-- Boolean terms

data BooleanUOp = BooleanNot
    deriving (Show, Eq, Ord)
data BooleanBOp = BooleanAnd | BooleanOr
    deriving (Show, Eq, Ord)
data BooleanFlatOp = BConjunction | BDisjunction
    deriving (Show, Eq, Ord)

instance ProperOpTag BooleanBOp where
    opPrec BooleanAnd = 6
    opPrec BooleanOr = 3

instance ProperOpTag BooleanUOp where
    opPrec BooleanNot = 10

instance ProperOpTag BooleanFlatOp where
    opPrec BConjunction = 6
    opPrec BDisjunction = 3

-- Show1 instance for Op is below
instance (ProperOpTag a, ProperOpTag b, ProperOpTag c) => ProperRecT (Op a b c)

{-----------------------------------------------------------------------------}

-- newtype Fix f = Fix { unFix :: f (Fix f) }
-- newtype Fix2 f a = Fix2 { unFix2 :: f a (Fix2 f a) }

-- This would do exactly what we need
newtype Fix4 f a b c = Fix4 { unFix4 :: f a b c (Fix4 f a b c) }
type Term = Fix4 TermF

--type BooleanExpr a = Fix (TermF Bool (Op BooleanUOp BooleanBOp Void) a)
type BooleanExpr             = Term (Op BooleanUOp BooleanBOp Void) Bool

{-----------------------------------------------------------------------------}
-- Recursion-schemes base functor

type instance Base (Term op val a) = TermF op val a

instance Recursive (Term op val a) where
    project :: Term op val a -> TermF op val a (Term op val a)
    project = unFix4

instance Corecursive (Term op val a) where
    embed :: TermF op val a (Term op val a) -> Term op val a
    embed = Fix4

{-----------------------------------------------------------------------------}

instance Functor (Term op val) where
    fmap :: (a -> b) -> Term op val a -> Term op val b
    fmap f (Fix4 term) = case term of
        ConstT x    -> Fix4 $ ConstT x
        VariableT v -> Fix4 $ VariableT (f v)
        RecT op     -> Fix4 $ RecT $ (fmap . fmap) f op

instance Applicative (Term op val) where
    pure = return
    (<*>) = ap

instance Monad (Term op val) where
    return :: a -> Term op val a
    return = Fix4 . VariableT
    (>>=) :: Term op val a -> (a -> Term op val b) -> Term op val b
    Fix4 (VariableT v)  >>= f   = f v
    Fix4 (ConstT x)     >>= _   = Fix4 $ ConstT x
    Fix4 (RecT op)      >>= f   = Fix4 $ RecT $ fmap (>>= f) op

{-----------------------------------------------------------------------------}

pattern Val :: forall (op :: Type -> Type) val var.
    val -> Term op val var
pattern Var :: forall (op :: Type -> Type) val var.
    var -> Term op val var
pattern Rec :: forall (op :: Type -> Type) val var.
    () => ProperRecT op
    => op (Term op val var) -> Term op val var

pattern BUOp
    :: () => (ProperRecT (Op uop bop flop), ProperOpTag uop)
    => uop
    -> Term (Op uop bop flop) val var
    -> Term (Op uop bop flop) val var
pattern BBOp
    :: () => (ProperRecT (Op uop bop flop), ProperOpTag bop)
    => bop
    -> Term (Op uop bop flop) val var
    -> Term (Op uop bop flop) val var
    -> Term (Op uop bop flop) val var
pattern BFlOp
    :: () => (ProperRecT (Op uop bop flop), ProperOpTag flop)
    => flop
    -> [Term (Op uop bop flop) val var]
    -> Term (Op uop bop flop) val var

pattern BNot
    :: () => (ProperRecT (Op BooleanUOp b c), ProperOpTag BooleanUOp)
    => Term (Op BooleanUOp b c) val var
    -> Term (Op BooleanUOp b c) val var
pattern BAnd
    :: () => (ProperRecT (Op a BooleanBOp c), ProperOpTag BooleanBOp)
    => Term (Op a BooleanBOp c) val var
    -> Term (Op a BooleanBOp c) val var
    -> Term (Op a BooleanBOp c) val var
pattern BOr
    :: () => (ProperRecT (Op a BooleanBOp c), ProperOpTag BooleanBOp)
    => Term (Op a BooleanBOp c) val var
    -> Term (Op a BooleanBOp c) val var
    -> Term (Op a BooleanBOp c) val var

pattern Val v       = Fix4 (ConstT v)
pattern Var v       = Fix4 (VariableT v)
pattern Rec v       = Fix4 (RecT v)

pattern BUOp o a    = Fix4 (RecT (UnaryOp o a))
pattern BBOp o a b  = Fix4 (RecT (BinaryOp o a b))
pattern BFlOp o xs  = Fix4 (RecT (FlatOp o xs))

pattern BNot a      = Fix4 (RecT (UnaryOp BooleanNot a))
pattern BAnd a b    = Fix4 (RecT (BinaryOp BooleanAnd a b))
pattern BOr  a b    = Fix4 (RecT (BinaryOp BooleanOr a b))
pattern BConj xs    = Fix4 (RecT (FlatOp BConjunction xs))
pattern BDisj xs    = Fix4 (RecT (FlatOp BDisjunction xs))


{-# COMPLETE Var, Val, Rec #-}
{-# COMPLETE Var, Val, BUOp, BBOp, BFlOp #-}
{-# COMPLETE Var, Val, BNot, BAnd, BOr, BFlOp #-}
{-# COMPLETE Var, Val, BNot, BAnd, BOr, BConj, BDisj #-}

{-----------------------------------------------------------------------------}
-- Our show instance will print the expression in forms of patterns
-- This is contrary to what show usually does, but much easier to use

-- c_prec :: BooleanBOp -> Int
-- c_prec BooleanAnd = 6
-- c_prec BooleanOr  = 3

-- c_pname :: BooleanBOp -> String
-- c_pname BooleanAnd = "BAnd"
-- c_pname BooleanOr  = "BOr"

--showsOp :: (Int -> Term (Op a b c) val a -> ShowS)

instance Show1 (Op uop bop flop) where
    liftShowsPrec :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS)
        -> Int -> Op uop bop flop a -> ShowS
    liftShowsPrec showsRec _ d = let
        prec :: Int
        prec = 10   -- same precedence for everyone in show
        in \case
        UnaryOp o t     -> showParen (d > prec) $
            showString (show o ++ " ") . showsRec (prec+1) t
        BinaryOp o a b  -> showParen (d > prec) $
            showsRec (prec+1) a . showString (" `" ++ show o ++ "` ") . showsRec (prec+1) b
        FlatOp o xs     -> showParen (d > prec) $
            showString (show o ++ " [") . 
            showListWith (showsRec 0) xs .
            showString "]"

-- FIXME: Generalize & use PP
instance Show val => Show1 (Term (Op uop bop flop) val) where
    liftShowsPrec :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS)
        -> Int -> Term (Op uop bop flop) val a -> ShowS
    liftShowsPrec showsVar showsList d = let
        showsRec :: Int -> Term (Op uop bop flop) val a -> ShowS
        showsRec = liftShowsPrec showsVar showsList
        prec :: Int
        prec = 10   -- same precedence for everyone
        in \case
        Val v       -> shows v
        Var v       -> showParen (d > prec) $
            showString "Var " . showsVar d v
        Rec v       -> liftShowsPrec showsRec (showListWith (showsRec 0)) d v
        -- BNot a      -> -- let prec = 10 in
        --     showParen (d > prec) $ showString "BNot " . showrec (prec+1) a
        -- BBOp o a b   -> -- let prec = c_prec o in
        --     showParen (d > prec) $
        --     showrec (prec+1) a . showString (" `" ++ c_pname o ++ "` ") . showrec (prec+1) b

instance (Show a, Show val) => Show (Term (Op BooleanUOp BooleanBOp Void) val a) where
    showsPrec = showsPrec1

{-----------------------------------------------------------------------------}
-- Flattening



{-----------------------------------------------------------------------------}
-- Constant folding
-- This one was called "simplifyPrimitive" in the old version

-- LOCAL TYPE DEFINITION
-- FIXME: should be generalized to work on conj/disj
type BTermConstFold = Term (Op BooleanUOp BooleanBOp Void) Bool
type BTermConstFold' = Term (Op BooleanUOp BooleanBOp Void) Void

-- Dumb idea? This looks very nice because the Bool gets /factored out/!
type BooleanValue = Term VoidF Bool Void

-- class GConstantFold f where
--     -- (Term f Bool a) (Either Bool (Term f Void a))
--     gsimp :: Alg (TermF f Bool a) (Either Bool (Term f Void a))

-- instance GConstantFold VoidF where
--     gsimp :: Alg (TermF VoidF Bool a) (Either Bool (Term op Void a))
--     gsimp (ConstT b)    = Left b
--     gsimp (VariableT v) = Right $ Var v
--     gsimp (RecT void)   = absurd (getConst void)

-- instance GConstantFold (Op BooleanUOp Void Void) where
--     gsimp :: Alg (TermF (Op BooleanUOp Void Void) Bool a)
--         (Either Bool (Term (Op BooleanUOp bop flop) Void a))
--     gsimp (RecT (UnaryOp BooleanNot t)) = case t of
--         Left b      -> Left $ not b
--         Right t'    -> Right $ BNot t'  -- We could have "Right $ not t'" here, woot?

opDispatch
    :: (Op a Void Void r -> e)
    -> (Op Void b Void r -> e)
    -> (Op Void Void c r -> e)
    ->  Op a b c       r -> e
opDispatch fUOp fBOp fFlOp = \case
    UnaryOp o r     -> fUOp (UnaryOp o r)
    BinaryOp o a b  -> fBOp (BinaryOp o a b)
    FlatOp o xs     -> fFlOp (FlatOp o xs)

termFDispatch
    :: (TermF a  Void Void r -> e)
    -> (TermF VoidF b Void r -> e)
    -> (TermF VoidF Void c r -> e)
    -> TermF a b c         r -> e
termFDispatch fRec fVal fVar = \case
    ConstT v        -> fVal (ConstT v)
    VariableT v     -> fVar (VariableT v)
    RecT op         -> fRec (RecT op)

constantFold :: BTermConstFold a -> Either Bool (BTermConstFold' a)
constantFold = cata simp where
    simp :: Alg (TermF (Op BooleanUOp BooleanBOp Void) Bool a) (Either Bool (BTermConstFold' a))
    simp = termFDispatch fRec fVal fVar where
        fVal :: Alg (TermF VoidF Bool Void) (Either Bool (BTermConstFold' a))
        fVal (ConstT b) = Left b

        fVar :: Alg (TermF VoidF Void a) (Either Bool (BTermConstFold' a))
        fVar (VariableT v) = Right $ Var v

        fRec :: Alg (TermF (Op BooleanUOp BooleanBOp Void) Void Void) (Either Bool (BTermConstFold' a))
        fRec (RecT (UnaryOp BooleanNot t)) = case t of
            Left b      -> Left $ not b
            Right t'    -> Right $ BNot t'  -- We could have "Right $ not t'" here, woot?
        fRec (RecT (BinaryOp BooleanAnd l r)) = sAnd l r where
            sAnd (Right a)      (Right b)   = Right $ BAnd a b
            sAnd (Left True)    rhs         = rhs
            sAnd (Left False)   _           = Left False
            sAnd lhs            rhs         = sAnd rhs lhs -- symm.
        fRec (RecT (BinaryOp BooleanOr l r)) = sOr l r where
            sOr  (Right a)      (Right b)   = Right $ BOr a b
            sOr  (Left True)    _           = Left True
            sOr  (Left False)   rhs         = rhs
            sOr  lhs            rhs         = sOr rhs lhs -- symm.
        fRec (RecT (FlatOp void _)) = absurd void

{-----------------------------------------------------------------------------}
-- Mini logic module

-- | Anything that has boolean operations
class Boolean b where
    and :: b -> b -> b
    or :: b -> b -> b
    not :: b -> b

infixr 3 &&
(&&) :: Boolean b => b -> b -> b
(&&) = and

infixr 2 ||
(||) :: Boolean b => b -> b -> b
(||) = or

truth :: Boolean b => b -> b
truth x = x || not x

falsity :: Boolean b =>  b -> b
falsity x = x && not x

-- | Boolean arithmetic can represent truth values
class Boolean b => BooleanArithmetic b where
    -- | Represent a Haskell 'Bool' in the target language
    fromBool :: Bool -> b

    -- | Shortcut for @fromBool True@
    true :: b
    true = fromBool True

    -- | Shortcut for @fromBool False@
    false :: b
    false = fromBool False

-- FIXME: Strings are bad
-- | Boolean pre-algebra has variables (but not necessarily values)
class Boolean b => BooleanPreAlgebra b where
    -- | Represent a variable in the target algebra
    var :: String -> b

-- | Full boolean algbra has both values and variables
class (BooleanArithmetic b, BooleanPreAlgebra b) => BooleanAlgebra b

instance Boolean Bool where
    and = (P.&&)
    or = (P.||)
    not = P.not

instance BooleanArithmetic Bool where
    fromBool = id

instance Boolean b => Boolean (a -> b) where
    and a b i = and (a i) (b i)
    or  a b i = or  (a i) (b i)
    not a i   = not (a i)

instance Boolean (BooleanExpr a) where
    and a b = BAnd a b
    or a b  = BOr a b
    not a   = BNot a

instance BooleanArithmetic (BooleanExpr a) where
    fromBool = Val

instance BooleanPreAlgebra (BooleanExpr String) where
    var = Var

instance BooleanAlgebra (BooleanExpr String)

-- ∀(x ∈ s). p(x)
forAll :: Boolean b => [a] -> (a -> b) -> b
forAll s p = foldr1 and $ fmap p s

-- ∃(x ∈ s). p(x)
exists :: Boolean b => [a] -> (a -> b) -> b
exists s p = foldr1 or $ fmap p s

excludes :: Boolean b => b -> b -> b
excludes a b = not a || not b

implies :: Boolean b => b -> b -> b
implies a b = not a || b

iff :: Boolean b => b -> b -> b
iff a b = (a `implies` b) && (b `implies` a)

given :: BooleanArithmetic b => Bool -> b -> b
given True  = id
given False = const true

is :: BooleanArithmetic b => a -> (a -> Bool) -> b
is a f = if f a then true else false

existsUnique :: (Eq a, BooleanArithmetic b) => [a] -> (a -> b) -> b
existsUnique s p = foldr1 and
    [   exists s p              -- ∃(x ∈ s). p(x)
    ,   forAll s $ \x1 ->       -- ∀(x1 ∈ s).
        forAll s $ \x2 ->       -- ∀(x2 ∈ s).
        given (x1 /= x2) $      -- (x1 ≠ x2) =>
        p x1 `excludes` p x2    -- ¬p(x1) ∨ ¬p(x2)
    ]

-- This variant is nice and short, but generates irregular terms
-- (which make a nice test)
existsUnique' :: (Eq a, BooleanArithmetic b) => Boolean b => [a] -> (a -> b) -> b
existsUnique' s p = exists s $ \x ->
    forAll s $ \y ->
    p y `iff` (x `is` (== y))

{-----------------------------------------------------------------------------}

-- An actual term
demo1 :: BooleanExpr String
demo1 = BNot $
    (BNot (Var "a") `BOr` Var "b") `BAnd` BNot (Var "c" `BAnd` Var "d")

-- A demo of irregular terms with existsUnique'
demo2a :: BooleanExpr String
demo2a = existsUnique [1..3::Int] (\x -> var $ "N" ++ show x)
demo2b :: BooleanExpr String
demo2b = existsUnique' [1..3::Int] (\x -> var $ "N" ++ show x)

{-----------------------------------------------------------------------------}
-- Further ideas

-- https://hackage.haskell.org/package/compdata-0.12.1/docs/Data-Comp-Generic.html
