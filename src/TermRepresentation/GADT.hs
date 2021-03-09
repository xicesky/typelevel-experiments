
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
-- import Control.Monad (ap)

import Data.Bool (bool)
import Data.Foldable (toList)
import Data.Traversable (foldMapDefault)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer

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

deriving instance (Eq (op r), Eq val, Eq var) => Eq (TermF op val var r)
deriving instance Functor (TermF op val var)
-- deriving instance Foldable (TermF op val var)
-- deriving instance Traversable (TermF op val var)

-- I'm going to reget this, am i?
class (Show1 op, Eq1 op, Functor op, Foldable op, Traversable op) => ProperRecT op where
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
    opName :: o -> String
    opName = show

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
    opName BooleanAnd = "BAnd"
    opName BooleanOr = "BOr"

instance ProperOpTag BooleanUOp where
    opPrec BooleanNot = 10
    opName BooleanNot = "BNot"

instance ProperOpTag BooleanFlatOp where
    opPrec BConjunction = 6
    opPrec BDisjunction = 3
    opName BConjunction = "BConj"
    opName BDisjunction = "BDisj"

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
-- Equality of terms

instance Eq1 (f a b c) => Eq (Fix4 f a b c) where
    (==) (Fix4 fa) (Fix4 fb) = eq1 fa fb

instance Eq1 (Op a b c) where
    liftEq :: (x -> x' -> Bool) -> Op a b c x -> Op a b c x' -> Bool
    liftEq f (UnaryOp o x) (UnaryOp o' x') = (o == o') && f x x'
    liftEq f (BinaryOp o a b) (BinaryOp o' a' b')
        = (o == o') && f a a' && f b b'
    liftEq f (FlatOp o xs) (FlatOp o' xs')
        = (o == o') && liftEq f xs xs'
    liftEq _ _ _ = False

instance (Eq val, Eq var) => Eq1 (TermF op val var) where
    liftEq _ (ConstT a) (ConstT b) = a == b
    liftEq _ (VariableT a) (VariableT b) = a == b
    liftEq f (RecT ra) (RecT rb) = liftEq f ra rb
    liftEq _ _ _ = False

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
-- Foldable, Traversable for TermF and Term

instance Foldable (TermF op val var) where
   foldMap = foldMapDefault

instance Traversable (TermF op val var) where
    traverse :: Applicative f => (a -> f b) -> TermF op val var a -> f (TermF op val var b)
    traverse f = \case
        (ConstT v)      -> pure (ConstT v)
        (VariableT v)   -> pure (VariableT v)
        (RecT op)       -> RecT <$> traverse f op

instance Foldable (Term op val) where
   foldMap = foldMapDefault

instance Traversable (Term op val) where
    traverse :: Applicative f => (a -> f b) -> Term op val a -> f (Term op val b)
    traverse f = \case
        (Val v) -> pure (Val v)
        (Var v) -> Var <$> f v
        (Rec v) -> Rec <$> traverse (traverse f) v

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


-- FIXME: Fix4 can actually even be an instance of Show2
instance Show2 (f a b) => Show1 (Fix4 f a b) where
    liftShowsPrec :: forall c. (Int -> c ->  ShowS) -> ([c] -> ShowS)
        -> Int -> Fix4 f a b c -> ShowS
    liftShowsPrec showC showListC = go where
        go :: Int -> Fix4 f a b c -> ShowS
        go d (Fix4 f) = liftShowsPrec2 showC showListC go (showListWith (go 0)) d f

instance Show1 (f a b c) => Show (Fix4 f a b c) where
    showsPrec :: Int -> Fix4 f a b c -> ShowS
    showsPrec d (Fix4 f) = liftShowsPrec showsPrec showList d f

instance Show1 (Op uop bop flop) where
    liftShowsPrec :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS)
        -> Int -> Op uop bop flop a -> ShowS
    liftShowsPrec showsRec _ d = let
        prec :: Int
        prec = 10   -- same precedence for everyone in show
        in \case
        UnaryOp o t     -> showParen (d > prec) $
            showString (opName o ++ " ") . showsRec (prec+1) t
        BinaryOp o a b  -> showParen (d > prec) $
            showsRec (prec+1) a . showString (" `" ++ opName o ++ "` ") . showsRec (prec+1) b
        FlatOp o xs     -> showParen (d > prec) $
            showString (opName o) .
            showListWith (showsRec 0) xs

-- FIXME: Generalize & use PP
instance Show val => Show2 (TermF op val) where
    liftShowsPrec2 :: forall var a.
           (Int -> var -> ShowS) -> ([var] -> ShowS)
        -> (Int -> a -> ShowS) -> ([a] -> ShowS)
        -> Int -> TermF op val var a -> ShowS
    liftShowsPrec2 showVar _ showA showAL = go where
        prec :: Int
        prec = 10   -- same precedence for everyone
        go :: Int -> TermF op val var a -> ShowS
        go d = \case
            ConstT v    -> showParen (d > prec) $
                showString "Val " . shows v
            VariableT v -> showParen (d > prec) $
                showString "Var " . showVar d v
            RecT v      -> liftShowsPrec showA showAL d v

instance (Show val, Show var) => Show1 (TermF op val var) where
    liftShowsPrec = liftShowsPrec2 showsPrec showList

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
    fRec :: Alg (TermF BOps Void Void) (Either Bool (Term BOps Void a))
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
    fRec (RecT (FlatOp op _)) = absurd op

-- Generalized to arbitrary inputs
constantFold :: (t a :<: Term BOps Bool a) => t a -> Either Bool (Term BOps Void a)
constantFold = constantFold' . inject

{-----------------------------------------------------------------------------}

invertOp :: BooleanBOp -> BooleanBOp
invertOp BooleanAnd = BooleanOr
invertOp BooleanOr = BooleanAnd

type Literal a = (Bool, a)

type BNOps = Op Void BooleanBOp Void

pushNegations' :: Term BOps Void a -> Term BNOps Void (Bool, a)
pushNegations' term = cata pushNeg term True where
    pushNeg :: Alg (TermF BOps Void a) (Bool -> Term BNOps Void (Bool, a))
    pushNeg (ConstT x) = absurd x
    pushNeg (VariableT x) = \b -> Var (b, x)
    pushNeg (RecT (UnaryOp BooleanNot t)) = t . not
    pushNeg (RecT (BinaryOp op l r)) = \b ->
        BBOp (bool invertOp id b op) (l b) (r b)
    pushNeg (RecT (FlatOp op _)) = absurd op

{-----------------------------------------------------------------------------}
-- Flattening

type BNFlOps = Op Void Void BooleanFlatOp

flatten' :: forall uop val var. ProperOpTag uop
     => Term (Op uop BooleanBOp Void) val var -> Term (Op uop Void BooleanFlatOp) val var
flatten' = cata flat where
    flat :: Alg (TermF (Op uop BooleanBOp Void) val var) (Term (Op uop Void BooleanFlatOp) val var)
    flat (ConstT v) = Val v
    flat (VariableT v) = Var v
    --flat (RecT (UnaryOp op _)) = absurd op
    flat (RecT (UnaryOp op t)) = BUOp op t
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
flatten :: forall val var t. (t :<: Term BNOps val var) => t -> Term BNFlOps val var
flatten = flatten' . inject

{-----------------------------------------------------------------------------}

simplify :: (t a :<: Term BOps Bool a) => t a -> Term BNFlOps Void (Bool, a)
simplify term = case constantFold term of
    Left True -> BConj []
    Left False -> BDisj []
    Right b -> (flatten . pushNegations') b

{-----------------------------------------------------------------------------}
-- Transform to CNF by distribution (inefficient)

data Conjunction e = Conjunction [e]
    deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Boolean disjunctions of arbitrary length
-- a.k.a. "flattened" or expressions
data Disjunction e = Disjunction [e]
    deriving (Show, Eq, Functor, Foldable, Traversable)

type CNF lit = Conjunction (Disjunction lit)

instance Applicative Conjunction where
    pure = Conjunction . pure
    (<*>) (Conjunction a) (Conjunction b)
        = Conjunction (a <*> b)

instance Applicative Disjunction where
    pure = Disjunction . pure
    (<*>) (Disjunction a) (Disjunction b)
        = Disjunction (a <*> b)

distributeDisjunction :: Disjunction (Conjunction e) -> Conjunction (Disjunction e)
distributeDisjunction = sequenceA       -- Well, isn't this easy.

joinConjunction :: Conjunction (Conjunction e) -> Conjunction e
joinConjunction (Conjunction xs) = -- Monad.join
    Conjunction [y | Conjunction x <- xs, y <- x]

joinDisjunction :: Disjunction (Disjunction e) -> Disjunction e
joinDisjunction (Disjunction xs) = -- Monad.join
    Disjunction [y | Disjunction x <- xs, y <- x]

distributeToCNF :: forall a. Term BNFlOps Void a -> CNF a
distributeToCNF = cata distr where
    distr :: Alg (TermF BNFlOps Void a) (CNF a)
    distr (ConstT x) = absurd x
    distr (VariableT x) = (pure . pure) x
    distr (RecT (UnaryOp op _)) = absurd op
    distr (RecT (BinaryOp op _ _)) = absurd op
    distr (RecT (FlatOp op xs)) = case op of
        BConjunction -> joinConjunction $ Conjunction xs
        BDisjunction -> fmap joinDisjunction . distributeDisjunction $ Disjunction xs

moo1 :: Term BNFlOps Void Int
moo1 = BConj[BDisj[Var 1,Var 2],BDisj[Var 3,Var 4]]

moo2 :: Term BNFlOps Void Int
moo2 = BDisj[BConj[Var 1,Var 2],BConj[Var 3,Var 4]]

toCNF :: (t a :<: Term BOps Bool a) => t a -> CNF (Literal a)
toCNF = distributeToCNF . simplify

{-----------------------------------------------------------------------------}
-- Substitutions

appTerm :: Term op val (Term op val var) -> Term op val var
appTerm (Val x) = Val x
appTerm (Var x) = x
appTerm (Rec f) = Rec $ fmap appTerm f

substVars :: (var -> Term op val var') -> Term op val var -> Term op val var'
substVars f = appTerm . fmap f

{-----------------------------------------------------------------------------}
-- Handling mapped variables

type MappedNames name = (Map Int name, Map name Int)

{- The variables numbers HAVE TO start with 1, because we will
    use signs in CNF to indicate negation
-}
mkMappedNames :: Ord name => [name] -> MappedNames name
mkMappedNames nList = (Map.fromList $ zip [1..] nList, Map.fromList $ zip nList [1..])

mappedHasName :: Ord name => MappedNames name -> name -> Bool
mappedHasName (_, m) name = Map.member name m

mappedInsert :: (Ord name, Show name) => Int -> name -> MappedNames name -> MappedNames name
mappedInsert i name (iton, ntoi)
    | Map.member i iton     = error $ "Index " ++ show i ++ " already exists"
    | Map.member name ntoi  = error $ "Name " ++ show name ++ " already exists"
    | otherwise             = (Map.insert i name iton, Map.insert name i ntoi)

-- FIXME: This is useless because it only works for terms
-- It should work for arbitrary functors
data Context name op val = Context
    {   getMappedNames :: MappedNames name
    ,   getTerm :: Term op val Int
    }

getNameMap :: Context name op val -> Map Int name
getNameMap = fst . getMappedNames

getIndexMap :: Context name op val ->  Map name Int
getIndexMap = snd . getMappedNames

deriving instance (Show name, Show val) => Show (Context name op val)
deriving instance (Eq name, Eq val) => Eq (Context name op val)

-- queryIndex :: Context name op val -> name -> Int
-- queryIndex ctx = fst . (Map.!) (getInfoMap ctx)

buildContext :: forall name op val. Ord name => Term op val name -> Context name op val
buildContext t = let
    mappedNames :: MappedNames name
    mappedNames = mkMappedNames (toList t)
    indexNames :: name -> Int
    indexNames = (Map.!) (snd mappedNames)
    in Context mappedNames (fmap indexNames t)

destroyContext :: forall name op val. Ord name => Context name op val -> Term op val name
destroyContext (Context mappedNames t) = let
    remapNames :: Int -> name
    remapNames = (Map.!) (fst mappedNames)
    in fmap remapNames t

-- TODO: Could be much more efficient
cRenameVars :: (Ord a, Ord b) => (a -> b) -> Context a op val -> Context b op val
cRenameVars rename = buildContext . fmap rename . destroyContext


-- FIXME: For now, we just use "String" as name, generalize later

{- | Class of "actually useful" variable names

Where "actually useful" means you can generate new ones.
-}
-- class (Show n, Ord n) => VarName n where
--     {- | Given a "set" of existing names, generate a new one

--     >>> f (mkFreshName f) == False
--     -}
--     mkFreshName :: (n -> Bool) -> n

--     refreshName :: (n -> Bool) -> n -> n
--     refreshName e _ = mkFreshName e

--     mkFreshHint :: (n -> Bool) -> String -> n
--     mkFreshHint e _ = mkFreshName e

--     refreshHint :: (n -> Bool) -> String -> n -> n
--     refreshHint e _ _ = mkFreshName e

findFreshName :: MappedNames String -> String -> String
findFreshName m prefix = head $ dropWhile exists' varnames where
    suffixes :: [String]
    suffixes = "" : ([replicate k ['a'..'z'] | k <- [1..]] >>= sequence)
    varnames :: [String]
    varnames = (prefix++) <$> suffixes
    exists' :: String -> Bool
    exists' = mappedHasName m

{-----------------------------------------------------------------------------}
-- Monad for fresh names

-- Not "splitable" for now
data FreshState = FreshState
    {   fsNextIndex :: Int
    ,   fsPrefix :: String
    ,   fsNames :: MappedNames String
    }
    deriving (Show, Eq)

fsMkFreshName :: String -> FreshState -> (Int, FreshState)
fsMkFreshName prefix (FreshState index p names) = let
    name :: String
    name = findFreshName names prefix
    in (index, FreshState (index+1) p (mappedInsert index name names))

newtype FreshT m a = FreshT { toStateT :: StateT FreshState m a }
    --deriving (Functor, Monad, MonadTrans, MonadIO)

deriving instance Functor m => Functor (FreshT m)
deriving instance Monad m => Applicative (FreshT m)
deriving instance Monad m => Monad (FreshT m)
deriving instance MonadTrans FreshT

deriving instance MonadIO m => MonadIO (FreshT m)
-- ... and so on... implement as we need it

class MonadFresh m where
    freshName :: String -> m Int

instance Monad m => MonadFresh (FreshT m) where
    freshName prefix = FreshT $ do
        state (fsMkFreshName prefix)

-- FIXME: get some proper names for those functions, these here are horrible

runFreshT :: Monad m => FreshT m a -> MappedNames String -> m (a, MappedNames String)
runFreshT fresh mapped = let
    maxI :: Int
    maxI = maximum $ 0 : Map.keys (fst mapped)
    initState :: FreshState
    initState = FreshState (maxI+1) "" mapped
    in do
        (a, FreshState _ _ mapped') <- runStateT (toStateT fresh) initState
        return (a, mapped')

withFreshT :: forall m op val. Monad m
    => Context String op val
    -> (Term op val Int -> FreshT m (Term op val Int))
    -> m (Context String op val)
withFreshT (Context mapped term) f = let
    result :: m (Term op val Int, MappedNames String)
    result = runFreshT (f term) mapped
    in do
        (term', mapped') <- result
        return $ Context mapped' term'

withFresh :: Context String op val
    -> (Term op val Int -> FreshT Identity (Term op val Int))
    -> Context String op val
withFresh ctx f = runIdentity (withFreshT ctx f)

newFresh :: FreshT Identity (Term op val Int) -> Context String op val
newFresh f = runIdentity $ do
    (term, mapped) <- runFreshT f (mkMappedNames [])
    return $ Context mapped term

testFreshT :: BooleanExpr String
testFreshT = destroyContext $ newFresh $ do
    a1 <- freshName "a"
    b <- freshName "b"
    a2 <- freshName "a"
    a3 <- freshName "a"
    return $ Var a1 `BAnd` BNot (Var b) `BOr` Var a2 `BOr` Var a3

{-----------------------------------------------------------------------------}
-- Tseitin-Transformation

litNeg :: Literal a -> Literal a
litNeg (b, v) = (not b, v)

cnf_just :: Literal a -> CNF (Literal a)
cnf_just a = pure $ pure a

cnf_iff :: Literal a -> Literal a -> CNF (Literal a)
cnf_iff a b = Conjunction               -- a ⇔ b ≡
    [   Disjunction [ litNeg a, b ]     -- a ⇒ b ∧
    ,   Disjunction [ a, litNeg b ]     -- a ⇐ b
    ]

cnf_iff_and :: Literal a -> Literal a -> Literal a -> CNF (Literal a)
cnf_iff_and z a b = Conjunction
    [   Disjunction [ litNeg z, a ]             -- z ⇒ a
    ,   Disjunction [ litNeg z, b ]             -- z ⇒ b
    ,   Disjunction [ z, litNeg a, litNeg b ]   -- ¬z ⇒ ¬a ∨ ¬b
    ]

cnf_iff_or :: Literal a -> Literal a -> Literal a -> CNF (Literal a)
cnf_iff_or z a b = Conjunction
    [   Disjunction [ litNeg z, a, b ]          -- z ⇒ a ∨ b
    ,   Disjunction [ z, litNeg a ]             -- ¬z ⇒ ¬a
    ,   Disjunction [ z, litNeg b ]             -- ¬z ⇒ ¬b
    ]

cnf_all :: [CNF a] -> CNF a
cnf_all = joinConjunction . Conjunction

tseitinTransformM :: forall m. Monad m => Term BOps Void Int -> FreshT m (CNF (Bool, Int))
tseitinTransformM term = do
    (zTerm, cnf) <- cata tt term
    return $ cnf_all [cnf, cnf_just zTerm]
    where
    tt :: Alg (TermF BOps Void Int) (FreshT m (Literal Int, CNF (Literal Int)))
    tt t = sequenceA t >>= \case
        ConstT v    -> absurd v
        VariableT v -> return ((True, v), Conjunction [])
        RecT (UnaryOp BooleanNot (v, cnf)) -> return (litNeg v, cnf)
        RecT (BinaryOp BooleanAnd (va, cnfa) (vb, cnfb)) ->
            freshName "zA_" >>= \z -> let
            t' = cnf_all
                [   cnfa
                ,   cnfb
                ,   cnf_iff_and (True, z) va vb
                ]
            in return ((True, z), t')
        RecT (BinaryOp BooleanOr (va, cnfa) (vb, cnfb)) ->
            freshName "zO_" >>= \z -> let
            t' = cnf_all
                [   cnfa
                ,   cnfb
                ,   cnf_iff_or (True, z) va vb
                ]
            in return ((True, z), t')
        RecT (FlatOp op _) -> absurd op

-- tseitinTransform' :: Term BOps Bool a -> Either Bool (Term BOps Void a)
tseitinTransform' :: Term BOps Void String -> CNF (Literal String)
tseitinTransform' t = let
    (Context nmap iterm) = buildContext t
    result :: (CNF (Literal Int), MappedNames String)
    result = runIdentity $ runFreshT (tseitinTransformM iterm) nmap
    (cnf, (iton, _)) = result
    in (fmap . fmap . fmap) (iton Map.!) cnf 

toCNF2 :: Term BOps Bool String -> CNF (Literal String)
toCNF2 term = case constantFold term of
    Left True   -> Conjunction []
    Left False  -> Conjunction [ Disjunction [] ]
    Right term' -> tseitinTransform' term'

{-----------------------------------------------------------------------------}

type DimacsWriter a = WriterT [String] Identity a

--instance Show a => Show (DimacsWriter a) where

dimacsComment :: String -> DimacsWriter ()
dimacsComment s = tell ["c " ++ s]

dimacsProblemLine :: String -> Int -> Int -> DimacsWriter ()
dimacsProblemLine format nVars nClauses = tell
    [   "p "
    ++  format
    ++  " "
    ++  show nVars
    ++  " "
    ++  show nClauses
    ]

dimacsClause :: [Int] -> DimacsWriter ()
dimacsClause xs = tell [
        P.foldr (\x r -> shows x . showString " " . r) id xs "0"
    ]

-- cnfToDimacs' :: CNF (Literal String) -> DimacsWriter ()
-- cnfToDimacs' = let
--     (Context nmap iterm) = buildContext t

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
    [   exists s p              --   ∃(x ∈ s). p(x)
    ,   forAll s $ \x1 ->       -- ∧ ∀(x1 ∈ s).
        forAll s $ \x2 ->       --   ∀(x2 ∈ s).
        given (x1 /= x2) $      --   (x1 ≠ x2) =>
        p x1 `excludes` p x2    --   ¬p(x1) ∨ ¬p(x2)
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

demo2c :: Term BNFlOps Void (Bool, String)
demo2c = simplify demo2b
--demo2c = flatten @Bool @String $ constantFold demo2b

{-----------------------------------------------------------------------------}
-- Further ideas

-- https://hackage.haskell.org/package/compdata-0.12.1/docs/Data-Comp-Generic.html
