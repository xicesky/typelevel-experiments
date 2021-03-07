
{-# LANGUAGE PatternSynonyms #-}

{-  Let's see how well we can represent a flexible term
    type using GADTs and recursion-schemes.
-}
module TermRepresentation.GADT where

import Prelude hiding (and, or, not, (&&), (||))
import qualified Prelude as P

import GHC.TypeLits
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

{-----------------------------------------------------------------------------}
-- Missing bits

-- Why doesn't recusion-schemes define an algebra type?
-- (probably because there are so many different ones)
-- We are going to mostly use cata, so here we go
type Alg f a = f a -> a

-- The ever looming void functor
type VoidF = Const Void

{-----------------------------------------------------------------------------}
-- Terms, part 1: Term structure

data TermF
    :: (Type -> Type) -> Type -> Type       -- Type parameters
    -> Type                                 -- Recursive term
    -> Type
    where
    ConstT      ::                  val ->      TermF op val var rec
    VariableT   ::                  var ->      TermF op val var rec
    RecT        :: ProperRecT op => op rec ->   TermF op val var rec

deriving instance Functor (TermF op val var)
-- deriving instance Foldable (TermF op val var)
-- deriving instance Traversable (TermF op val var)

-- I'm going to reget this, am i?
class (Show1 op, Functor op, Foldable op, Traversable op) => ProperRecT op where
    -- Something like this

-- Dispatcher, just in case you want to make things more complicated
-- FIXME: remove, it's useles
termFDispatch
    :: (TermF a  Void Void r -> e)
    -> (TermF VoidF b Void r -> e)
    -> (TermF VoidF Void c r -> e)
    -> TermF a b c         r -> e
termFDispatch fRec fVal fVar = \case
    ConstT v        -> fVal (ConstT v)
    VariableT v     -> fVar (VariableT v)
    RecT op         -> fRec (RecT op)

-- Fixpoint
newtype Fix4 f a b c = Fix4 { unFix4 :: f a b c (Fix4 f a b c) }
type Term = Fix4 TermF

{-----------------------------------------------------------------------------}
-- Terms, part 2: Operators

data Op
    :: Type -> Type -> Type -> Type -> Type
    where
    UnaryOp     :: ProperOpTag uop =>   uop  -> rec ->         Op uop bop flop rec
    BinaryOp    :: ProperOpTag bop =>   bop  -> rec -> rec ->  Op uop bop flop rec
    FlatOp      :: ProperOpTag flop =>  flop -> [rec] ->       Op uop bop flop rec

deriving instance Functor (Op uop bop flop)
deriving instance Foldable (Op uop bop flop)
deriving instance Traversable (Op uop bop flop)

class (Show o, Eq o, Ord o) => ProperOpTag o where
    opPrec :: o -> Int

instance ProperOpTag Void where
    opPrec = absurd

instance (ProperOpTag a, ProperOpTag b, ProperOpTag c) => ProperRecT (Op a b c)

-- Dispatcher, just in case you want to make things more complicated
-- FIXME: remove, it's useles
opDispatch
    :: (Op a Void Void r -> e)
    -> (Op Void b Void r -> e)
    -> (Op Void Void c r -> e)
    ->  Op a b c       r -> e
opDispatch fUOp fBOp fFlOp = \case
    UnaryOp o r     -> fUOp (UnaryOp o r)
    BinaryOp o a b  -> fBOp (BinaryOp o a b)
    FlatOp o xs     -> fFlOp (FlatOp o xs)

{-----------------------------------------------------------------------------}
-- Specialization to boolean terms

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

type BOps = Op BooleanUOp BooleanBOp Void
type BFlOps = Op BooleanUOp Void BooleanFlatOp

type BooleanExpr            = Term BOps Bool
type BooleanExprFlat        = Term BFlOps Bool

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
-- Functor, Applicative and Monad on Variables

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
-- And a few pattern synonyms for brevity

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

pattern BConj :: () => (ProperRecT (Op a b1 BooleanFlatOp), ProperOpTag BooleanFlatOp) => [Fix4 TermF (Op a b1 BooleanFlatOp) b2 c] -> Fix4 TermF (Op a b1 BooleanFlatOp) b2 c
pattern BConj xs    = Fix4 (RecT (FlatOp BConjunction xs))
pattern BDisj :: () => (ProperRecT (Op a b1 BooleanFlatOp), ProperOpTag BooleanFlatOp) => [Fix4 TermF (Op a b1 BooleanFlatOp) b2 c] -> Fix4 TermF (Op a b1 BooleanFlatOp) b2 c
pattern BDisj xs    = Fix4 (RecT (FlatOp BDisjunction xs))


{-# COMPLETE Var, Val, Rec #-}
{-# COMPLETE Var, Val, BUOp, BBOp, BFlOp #-}
{-# COMPLETE Var, Val, BNot, BAnd, BOr, BFlOp #-}
{-# COMPLETE Var, Val, BNot, BAnd, BOr, BConj, BDisj #-}

{-----------------------------------------------------------------------------}
-- We still need some kind of injectivity constraint

data Injection
    = IHere
    | IVoid     -- annoying special case for Void
    | IBoth Injection Injection
    | IDeconstruct [Injection]
    | ILift1 Injection

{- | Find an injection s -> t

This type family has to be closed to not cause conflicts (because of Fix4).
-}
type family FindInjection s t :: Injection where
    FindInjection a a       = 'IHere
    FindInjection Void a    = 'IVoid
    FindInjection (Fix4 f a b c) (Fix4 f a' b' c')
                            = 'ILift1 (FindInjection1 (f a b c) (f a' b' c'))
    FindInjection Bool (Term op Bool var)       -- special rule #1: Bool to Term
                            = 'IHere
    FindInjection (Either a b) c                -- special rule #2: Either
                            = 'IBoth (FindInjection a c) (FindInjection b c)
    FindInjection x y       = TypeError
        (       'Text "Could not find an injection from "
        ':$$:   'Text "\t" ':<>: 'ShowType x
        ':$$:   'Text "to"
        ':$$:   'Text "\t" ':<>: 'ShowType y
        )

{- | Find an injection s a -> t a

This type family could be open to allow different implementations of Op.
-}
type family FindInjection1 (s :: Type -> Type) (t :: Type -> Type) :: Injection where
    FindInjection1 (Op uop bop flop) (Op uop' bop' flop')
        = 'IDeconstruct
        [   FindInjection uop uop'
        ,   FindInjection bop bop'
        ,   FindInjection flop flop'
        ]
    FindInjection1 (TermF op val var) (TermF op' val' var')
        = 'IDeconstruct
        [   FindInjection1 op op'
        ,   FindInjection val val'
        ,   FindInjection var var'
        ]

class GInject s t (i :: Injection) where
    gInject :: Proxy i -> s -> t

instance GInject a a 'IHere where
    gInject _ = id

instance GInject Void a 'IVoid where
    gInject _ = absurd

class GInject1 s t (i :: Injection) where
    gInject1 :: Proxy i -> s a -> t a

instance (GInject uop uop' ia, GInject bop bop' ib, GInject flop flop' ic
    , ProperOpTag uop', ProperOpTag bop', ProperOpTag flop'
    )
    => GInject1 (Op uop bop flop) (Op uop' bop' flop') ('IDeconstruct [ia, ib, ic]) where
    gInject1 _ (UnaryOp o t) = UnaryOp (gInject @uop @uop' @ia Proxy o) t
    gInject1 _ (BinaryOp o t1 t2) = BinaryOp (gInject @bop @bop' @ib Proxy o) t1 t2
    gInject1 _ (FlatOp o t) = FlatOp (gInject @flop @flop' @ic Proxy o) t

instance (GInject1 op op' ia, GInject val val' ib, GInject var var' ic
    , ProperRecT op'
    )
    => GInject1 (TermF op val var) (TermF op' val' var') ('IDeconstruct [ia, ib, ic]) where
    gInject1 _ (RecT t) = RecT (gInject1 @op @op' @ia Proxy t)
    gInject1 _ (ConstT v) = ConstT (gInject @val @val' @ib Proxy v)
    gInject1 _ (VariableT v) = VariableT (gInject @var @var' @ic Proxy v)

instance (Functor (f a b c), GInject1 (f a b c) (f a' b' c') i)
    => GInject (Fix4 f a b c) (Fix4 f a' b' c') ('ILift1 i) where
    gInject _ = go where
        go (Fix4 f) = (Fix4
            . gInject1 @(f a b c) @(f a' b' c') @i Proxy
            . fmap go
            ) f

-- FindInjection Bool (Term op Bool var)       -- special rule #1: Bool to Term
--                         = 'IHere
-- FindInjection (Either a b) c                -- special rule #2: Either
--                         = 'IBoth (FindInjection a c) (FindInjection b c)

-- special rule #1: Bool to Term
instance GInject Bool (Term op Bool var) 'IHere where
    gInject _ = Val

-- special rule #2: Either
instance (GInject a c l, GInject b c r)
    => GInject (Either a b) c ('IBoth l r) where
    gInject _ (Left v)  = gInject @a @c @l Proxy v
    gInject _ (Right v) = gInject @b @c @r Proxy v

type (s :<: t) = (GInject s t (FindInjection s t))

inject :: forall s t. (s :<: t) => s -> t
inject = gInject @s @t @(FindInjection s t) Proxy

{-----------------------------------------------------------------------------}
-- Our show instance will print the expression in forms of patterns
-- This is contrary to what show usually does, but much easier to use

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

-- instance (Show var, Show val) => Show (Term BOps val var) where
--     showsPrec = showsPrec1

instance (Show var, Show1 (Term (Op uop bop flop) val)) => Show (Term (Op uop bop flop) val var) where
    showsPrec = showsPrec1

{-----------------------------------------------------------------------------}
-- Flattening

flatten' :: Term BOps val var -> Term BFlOps val var
flatten' = cata flat where
    flat :: Alg (TermF BOps val var) (Term BFlOps val var)
    flat (ConstT v) = Val v
    flat (VariableT v) = Var v
    flat (RecT (UnaryOp BooleanNot t)) = BNot t
    flat (RecT (BinaryOp BooleanAnd a b)) = case (a, b) of
        (BConj l, BConj r)  -> BConj (l ++ r)
        (BConj l, rhs    )  -> BConj (l ++ [rhs])
        (lhs    , BConj r)  -> BConj (lhs : r)
        (lhs    , rhs    )  -> BConj [lhs, rhs]
    flat (RecT (BinaryOp BooleanOr a b)) = case (a, b) of
        (BDisj l, BDisj r)  -> BDisj (l ++ r)
        (BDisj l, rhs    )  -> BDisj (l ++ [rhs])
        (lhs    , BDisj r)  -> BDisj (lhs : r)
        (lhs    , rhs    )  -> BDisj [lhs, rhs]
    flat (RecT (FlatOp op _)) = absurd op

{- | 'flatten'' Generalized to arbitrary inputs.

Sometimes GHC will try to fix 'val' and 'var' to arbitrary types. You can avoid
that by using type applications, e.g.:

>>> flatten @Bool @String $ constantFold demo2b
-}
flatten :: forall val var t. (t :<: Term BOps val var) => t -> Term BFlOps val var
flatten = flatten' . inject

{-----------------------------------------------------------------------------}
-- Constant folding
-- This function was once called "simplifyPrimitive"

-- Dumb idea? This looks very nice because the Bool gets /factored out/ in the type!
type BooleanValue = Term VoidF Bool Void

{- | Fold constants in a term.

TODO: Create a version that works on flattened terms.
-}
constantFold' :: Term BOps Bool a -> Either Bool (Term BOps Void a)
constantFold' = cata $ termFDispatch fRec
    (\(ConstT b) -> Left b)
    (\(VariableT v) -> Right $ Var v)
    where
    fRec :: Alg (TermF (Op BooleanUOp BooleanBOp Void) Void Void) (Either Bool (Term BOps Void a))
    fRec (ConstT x) = absurd x
    fRec (VariableT x) = absurd x
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

-- Generalized to arbitrary inputs
constantFold :: (t a :<: Term BOps Bool a) => t a -> Either Bool (Term BOps Void a)
constantFold = constantFold' . inject

{-----------------------------------------------------------------------------}
-- Renaming variables is easy now?

renameVars :: (a -> b) -> Term op val a -> Term op val b
renameVars = fmap

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
