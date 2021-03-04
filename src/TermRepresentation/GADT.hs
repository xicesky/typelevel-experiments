
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
import Data.Functor.Classes
import Data.Functor.Foldable
import Control.Monad (ap)

{-# ANN module "HLint: ignore Use newtype instead of data" #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

{-----------------------------------------------------------------------------}

data BooleanBOp = BooleanAnd | BooleanOr
data BooleanUOp = BooleanNot
data BooleanFlatOp = Conjunction | Disjunction

data Op
    :: Type -> Type -> Type -> Type -> Type
    where
    UnaryOp     :: uop -> rec           -> Op uop bop flop rec
    BinaryOp    :: bop -> rec -> rec    -> Op uop bop flop rec
    FlatOp      :: flop -> [rec]        -> Op uop bop flop rec

deriving instance Functor (Op uop bop flop)
deriving instance Foldable (Op uop bop flop)
deriving instance Traversable (Op uop bop flop)

data TermF
    :: (Type -> Type) -> Type -> Type       -- Type parameters
    -> Type                                 -- Recursive term
    -> Type
    where
    ConstT      ::                  val ->       TermF op val var rec
    VariableT   ::                  var ->       TermF op val var rec
    RecT        :: Functor op =>    op rec ->    TermF op val var rec

deriving instance Functor (TermF val op var)
-- deriving instance Foldable (TermF val op var)
-- deriving instance Traversable (TermF val op var)

{-----------------------------------------------------------------------------}

newtype Fix f = Fix { unFix :: f (Fix f) }
newtype Fix2 f a = Fix2 { unFix2 :: f a (Fix2 f a) }

-- This would do exactly what we need
newtype Fix4 f a b c = Fix4 { unFix4 :: f a b c (Fix4 f a b c) }
type Term = Fix4 TermF

--type BooleanExpr a = Fix (TermF Bool (Op BooleanUOp BooleanBOp Void) a)
type BooleanExpr             = Fix2 (TermF (Op BooleanUOp BooleanBOp Void) Bool)

{-----------------------------------------------------------------------------}
-- Recursion-schemes base functor

type instance Base (BooleanExpr a) = TermF (Op BooleanUOp BooleanBOp Void) Bool a

instance Recursive (BooleanExpr a) where
    project :: BooleanExpr a -> TermF (Op BooleanUOp BooleanBOp Void) Bool a (BooleanExpr a)
    project = unFix2

instance Corecursive (BooleanExpr a) where
    embed :: TermF (Op BooleanUOp BooleanBOp Void) Bool a (BooleanExpr a) -> BooleanExpr a
    embed = Fix2

{-----------------------------------------------------------------------------}

instance Functor (Fix2 (TermF val op)) where
    fmap :: (a -> b) -> Fix2 (TermF val op) a -> Fix2 (TermF val op) b
    fmap f (Fix2 term) = case term of
        ConstT x    -> Fix2 $ ConstT x
        VariableT v -> Fix2 $ VariableT (f v)
        RecT op     -> Fix2 $ RecT $ (fmap . fmap) f op

instance Applicative (Fix2 (TermF val op)) where
    pure = return
    (<*>) = ap

instance Monad (Fix2 (TermF val op)) where
    return :: a -> Fix2 (TermF val op) a
    return = Fix2 . VariableT
    (>>=) :: Fix2 (TermF val op) a -> (a -> Fix2 (TermF val op) b) -> Fix2 (TermF val op) b
    Fix2 (VariableT v)  >>= f   = f v
    Fix2 (ConstT x)     >>= _   = Fix2 $ ConstT x
    Fix2 (RecT op)      >>= f   = Fix2 $ RecT $ fmap (>>= f) op

{-----------------------------------------------------------------------------}

pattern Var :: forall (op :: Type -> Type) val var.
    var -> Fix2 (TermF op val) var
pattern Val :: forall (op :: Type -> Type) val var.
    val -> Fix2 (TermF op val) var
pattern BNot
    :: Fix2 (TermF (Op BooleanUOp b c) val) var 
    -> Fix2 (TermF (Op BooleanUOp b c) val) var
pattern BOp
    :: op
    -> Fix2 (TermF (Op a op c) val) var
    -> Fix2 (TermF (Op a op c) val) var
    -> Fix2 (TermF (Op a op c) val) var
pattern BAnd
    :: Fix2 (TermF (Op a BooleanBOp c) val) var
    -> Fix2 (TermF (Op a BooleanBOp c) val) var
    -> Fix2 (TermF (Op a BooleanBOp c) val) var
pattern BOr
    :: Fix2 (TermF (Op a BooleanBOp c) val) var
    -> Fix2 (TermF (Op a BooleanBOp c) val) var
    -> Fix2 (TermF (Op a BooleanBOp c) val) var

pattern Var v       = Fix2 (VariableT v)
pattern Val v       = Fix2 (ConstT v)
pattern BNot a      = Fix2 (RecT (UnaryOp BooleanNot a))
pattern BOp o a b   = Fix2 (RecT (BinaryOp o a b))
pattern BAnd a b    = Fix2 (RecT (BinaryOp BooleanAnd a b))
pattern BOr  a b    = Fix2 (RecT (BinaryOp BooleanOr a b))

{-# COMPLETE Var, Val, BNot, BAnd, BOr #-}
{-# COMPLETE Var, Val, BNot, BOp #-}

{-----------------------------------------------------------------------------}
-- Our show instance will print the expression in forms of patterns
-- This is contrary to what show usually does, but much easier to use

c_prec :: BooleanBOp -> Int
c_prec BooleanAnd = 6
c_prec BooleanOr  = 3

c_pname :: BooleanBOp -> String
c_pname BooleanAnd = "BAnd"
c_pname BooleanOr  = "BOr"

instance Show1 BooleanExpr where
    liftShowsPrec :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> BooleanExpr a -> ShowS
    liftShowsPrec showsVar showsList d = let
        showrec :: Int -> BooleanExpr a -> ShowS
        showrec = liftShowsPrec showsVar showsList
        prec :: Int
        prec = 10   -- same precedence for everyone
        in \case
        Val v       -> shows v  -- Bool
        Var v       -> showParen (d > prec) $
            showString "Var " . showsVar d v
        BNot a      -> -- let prec = 10 in
            showParen (d > prec) $ showString "BNot " . showrec (prec+1) a
        BOp o a b   -> -- let prec = c_prec o in
            showParen (d > prec) $
            showrec (prec+1) a . showString (" `" ++ c_pname o ++ "` ") . showrec (prec+1) b

instance Show a => Show (BooleanExpr a) where
    showsPrec = showsPrec1

{-----------------------------------------------------------------------------}
-- Constant folding




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
