{-# LANGUAGE DeriveDataTypeable, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts, UndecidableInstances #-} 
module ContractTypes
    where

-- to define the exception
import Control.Exception
import Data.Typeable

data Currency = EUR | DKK | SEK | USD | GBP | JPY
-- good enough with only FX derivatives. Otherwise we could add this:
-- "... | Stock String | Equity String"
-- These are just tags, not used in expressions / arithmetics
-- (otherwise we might want a GADT for them)

ppCur EUR = "EUR"
ppCur DKK = "DKK"
ppCur SEK = "SEK"
ppCur USD = "USD"
ppCur GBP = "GBP"
ppCur JPY = "JPY"

-- submodule expression starts here
type Var = String

-- Expression GADT:
data ExprG a where
    I :: Int    -> ExprG Int
    R :: Double -> ExprG Double
    B :: Bool   -> ExprG Bool
    V :: Var    -> ExprG a
    -- Pairs:
    Pair :: (ExprG a -> ExprG b) -> ExprG (a,b)
    Fst :: ExprG (a,b) -> ExprG a
    Snd :: ExprG (a,b) -> ExprG b
    -- observables and external choices
    Obs :: (String, Int) -> ExprG Double
    ChosenBy :: (String, Int) -> ExprG Bool
    -- accumulator. Acc(f,i,a) := f/i(...(f/2(f/1(a))))
    Acc :: (Var, ExprG a) -> Int -> ExprG a
    -- unary op.s: only "not"
    Not :: ExprG Bool -> ExprG Bool
    -- binary op.s, by type: +-*/ max min < = |
    -- on numerical arguments: +-*/ max min
    Arith :: Num a => AOp -> ExprG a -> ExprG a -> ExprG a
    Less  :: Ord a => ExprG a -> ExprG a -> ExprG Bool
    Equal :: Eq a  => ExprG a -> ExprG a -> ExprG Bool
    Or    :: ExprG Bool -> ExprG Bool -> ExprG Bool

data AOp = Plus | Minus | Times | Max | Min
         deriving (Show)

-- Bool indicating infix operators
ppOp :: AOp -> (String,Bool)
ppOp Plus   = ("+", True)
ppOp Minus  = ("-", True)
ppOp Times  = ("*", True)
ppOp Max    = ("max", False)
ppOp Min    = ("min", False)

-- reading operators
instance Read AOp where
    readsPrec _ ('+':rest) = [(Plus,rest)]
    readsPrec _ ('-':rest) = [(Minus,rest)]
    readsPrec _ ('*':rest) = [(Times,rest)]
    readsPrec _ ('m':'a':'x':rest) = [(Max,rest)]
    readsPrec _ ('m':'i':'n':rest) = [(Min,rest)]
    readsPrec _ _ = []

-- just some aliases
type BoolE = ExprG Bool
type IntE = ExprG Int
type RealE = ExprG Double

-- smart constructors and operators (for export):
-- TODO make these "smarter".
(!+!) = Arith Plus
(!-!) = Arith Minus
(!*!) = Arith Times

(!<!) :: Ord a => ExprG a -> ExprG a -> ExprG Bool
(!<!) = Less

(!=!) :: Eq a => ExprG a -> ExprG a -> ExprG Bool
(!=!) = Equal

(!|!) = Or

-- actually, we only need those:
instance (Decompose (ExprG a), Num (Content (ExprG a)), Num a) =>
    Num (ExprG a) where
    (+) = Arith Plus
    (*) = Arith Times
    (-) = Arith Minus
    negate = Arith Minus (fromInteger 0)
    abs a = (constr a) (abs (content a))
    signum a = (constr a) (signum (content a))
    fromInteger n = (constr (undefined :: ExprG a)) (fromInteger n)
-- there's a pattern... f a = (constr a) (f (content a))

-- enabled with this - slightly weird - helper class
class Num a => Decompose a where
    type Content a
    constr  :: a -> (Content a -> a)
    content :: Num (Content a) => a -> Content a

instance Decompose (ExprG Int) where
    type Content (ExprG Int) = Int
    constr _  = I
    content x = evalX emptyEnv x

instance Decompose (ExprG Double) where
    type Content (ExprG Double) = Double
    constr  _ = R
    content x = evalX emptyEnv x

obs      = Obs
chosenBy = ChosenBy
i = I -- :: Int  -> IntE
r = R -- :: Double -> RealE
b = B -- :: Bool -> BoolE
v = V -- :: String -> ExprG a

data EvalExc = Eval String deriving (Read,Show,Typeable)
instance Exception EvalExc

type Env = (String, Int) -> RealE -- missing ExprG Bool for choice...

emptyEnv :: Env
emptyEnv = \_ -> throw (Eval "no bindings")

-- evalR :: Env -> RealE -> Double
-- evalI :: Env -> IntE -> Int
-- evalB :: Env -> BoolE -> Bool
-- evalI = evalX
-- evalR = evalX
-- evalB = evalX

-- ExprG evaluator. Types checked statically, no checks required.
-- Assumes that the expr _can_ be evaluated, required fixings known
evalX :: Env -> ExprG a -> a
evalX env e = undefined
{-
       case e of
         V s -> error ("variable " ++ s)
         I _ -> e
         R _ -> e
         B _ -> e
         Obs u -> case env u of
                    Obs u' -> if u == u' then throw $ Eval "unresolved observable"
                              else eval env (Obs u')
                    e'     -> eval env e'
         BinOp opr e1 e2 -> 
              case (eval env e1, eval env e2) of
                (I i1, I i2) -> binopII opr i1 i2
                (R r1, R r2) -> binopRR opr r1 r2
                (B b1, B b2) -> binopBB opr b1 b2
                _ -> error "eval.BinOp: difference in argument types"
         UnOp "not" e1 -> 
             case eval env e1 of
               B b -> B (not b)
               _   -> error "eval.UnOp.not - wrong argument type"
         UnOp opr  _   -> error ("eval.UnOp: unsupported operator: " ++ opr)

evalR env e = case eval env e of
                R r -> r
                _   -> error "evalR: expecting real"
evalI env e = case eval env e of
                I i -> i
                _   -> error "evalI: expecting real"
evalB env e = case eval env e of
                B b -> b
                _   -> error "evalB: expecting real"

type Party = String

data Contract =
       TransfOne Currency Party Party
     | Scale RealE Contract
     | Transl IntE Contract
     | All [Contract]
     | If BoolE Contract Contract
     | Iter IntE (Var -> Contract) -- how to use it?
     | CheckWithin BoolE IntE Contract Contract 
     -- if cond::BoolE becomes true within time::IntE then contract1 in effect. 
     -- otherwise (time expired, always false) contract2 in effect
-}
