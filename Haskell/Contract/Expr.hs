{-# LANGUAGE DeriveDataTypeable, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts, UndecidableInstances #-} 
module Contract.Expr
    ( Currency(..), Var
    , Expr(..), AOp(..)  -- constructors exported, for internal use
    , BoolE, IntE, RealE -- for re-export
    -- constructors for interface
    , i, r, b, v, pair, first, second, acc, obs, chosenBy
    -- operators, unless in NUm instance
    , (!<!), (!=!), (!|!), maxx, minn, nott
    -- predicates, expression translate, hash
    , certainExp, translExp, hashExp
    -- evaluation
    , eval -- for internal use only
    , evalI, evalR, evalB, simplifyExp
    -- some pp leftovers
    , ppReal, ppOp
    ) where

-- to define the exception
import Control.Exception
import Data.Typeable

-- for name supply
import System.IO.Unsafe(unsafePerformIO)
import Control.Concurrent

-- for pretty-printer
import Text.Printf

import Contract.Date
import Contract.Hash
import Contract.Environment

-------------------------------------------------------------------------------

-- | Currency type. These are just tags and not used in expressions/arithmetics
-- (and should probably not be here; not really used that much in our code.)
data Currency = EUR | DKK | SEK | USD | GBP | JPY | NOK
              deriving (Eq, Show, Read)
-- good enough with only FX derivatives. Otherwise we could add this:
-- "... | Stock String | Equity String"

-- ppCur not needed, use "show"
-- ppCur EUR = "EUR"
-- ppCur DKK = "DKK"
-- ppCur SEK = "SEK"
-- ppCur USD = "USD"
-- ppCur GBP = "GBP"
-- ppCur JPY = "JPY"

type Var = String

-- Expression GADT:
data Expr a where
    I :: Int    -> Expr Int
    R :: Double -> Expr Double
    B :: Bool   -> Expr Bool
    V :: Var    -> Expr a
    -- Pairs:
    Pair :: Expr a -> Expr b -> Expr (a,b)
    Fst :: Expr (a,b) -> Expr a
    Snd :: Expr (a,b) -> Expr b
    -- observables and external choices
    Obs :: (String, Int) -> Expr Double
    ChosenBy :: (String, Int) -> Expr Bool
    -- accumulator. Acc(f,i,a) := f(f/-1(...(f/2-i(f/1-i(a/-i)))))
    Acc :: (Var, Expr a) -> Int -> Expr a -> Expr a
    -- unary op.s: only "not"
    Not :: Expr Bool -> Expr Bool
    -- binary op.s, by type: +-*/ max min < = |
    -- on numerical arguments: +-*/ max min
    Arith :: (NumE a, Num a) => AOp -> Expr a -> Expr a -> Expr a
    Less  :: Ord a => Expr a -> Expr a -> Expr Bool
    Equal :: Eq a  => Expr a -> Expr a -> Expr Bool
    Or    :: Expr Bool -> Expr Bool -> Expr Bool

-- | Supported arithmetic operations as a data type
data AOp = Plus | Minus | Times | Div | Max | Min
         deriving (Eq,Show)

-- | Aliases for the expression types we use
type BoolE = Expr Bool
type IntE = Expr Int
type RealE = Expr Double

-- | arithmetics smart constructor, trying to optimise by evaluating constants
arith :: (Num a, NumE a) => AOp -> Expr a -> Expr a -> Expr a
arith op (I i1) (I i2) = I (opsem op i1 i2)
arith op (R r1) (R r2) = R (opsem op r1 r2)
arith Plus e1 e2  = Arith Plus  e1 e2
arith Minus e1 e2 = Arith Minus e1 e2
arith Times e1 e2 = Arith Times e1 e2
arith Div e1 e2 = Arith Div e1 e2
arith Max e1 e2   = Arith Max   e1 e2
arith Min e1 e2   = Arith Min   e1 e2

-- | semantics of the arithmetic operators, for 'arith' smart constructor
opsem :: (Ord a, Num a, NumE a) => AOp -> a -> a -> a
opsem Plus = (+)
opsem Minus = (-)
opsem Times = (*)
opsem Max = max
opsem Min = min
opsem Div = divide -- overloaded using NumE helper class below


-- | Expression equality is defined using hashExpr (considering commutativity)
instance Eq (Expr a) where
     e1 == e2 = hashExp [] e1 0 == hashExp [] e2 0

-- | Computes hash of an expression, for syntactic comparisons. 
-- Considers commutativity by symmetric hashing for commutative operations.
hashExp :: [Var] -> Expr a -> Hash -> Hash -- need to give an explicit type
hashExp vs e a = 
    let ps = hashPrimes
    in case e of
         V v -> case index v vs of
                  Just i -> hash (ps!!0) (hash i a)
                  Nothing -> hash (ps!!0) (hashStr v a)
         I i -> hash (ps!!1) (hashSigned i a)
         R r -> hash (ps!!2) (hashStr (ppReal r) a)
         B True -> hash (ps!!3) a
         B False -> hash (ps!!4) a
         Pair e1 e2 -> hash (ps!!5) (hashExp vs e1 (hashExp vs e2 a))
         Fst e -> hash (ps!!6) (hashExp vs e a)
         Snd e -> hash (ps!!7) (hashExp vs e a)
         Obs (s,i) -> hash (ps!!8) (hashStr s (hash i a))
         ChosenBy (p,i) -> hash (ps!!9) (hashStr p (hash i a))

         Acc (v,e1) i e2 
             -> hash (ps!!10) (hash i (hashExp (v:vs) e1 (hashExp vs e2 a)))
         Not e1 -> hash (ps!!11) (hashExp vs e1 a)
         Arith op e1 e2 | op `elem` [Plus,Times,Max,Min] -- symmetric! (commutative)
             -> hashStr (fst $ ppOp op) (hashExp vs e1 0 + hashExp vs e2 0 + a)
                        | otherwise -- not symmetric
             -> hashStr (fst $ ppOp op) $ hashExp vs e1 $ hashExp vs e2 a
        -- symmetric!
         Equal e1 e2 -> hashStr "=" (hashExp vs e1 0 + hashExp vs e2 0 + a)
         Or e1 e2    -> hashStr "|" (hashExp vs e1 0 + hashExp vs e2 0 + a)
        -- not symmetric!
         Less e1 e2 -> hash (ps!!12) (hashExp vs e1 (hashExp vs e2 a))

----------------------------------------

-- | Num instance, enabling us to write 'e1 + e2' for Expr a with Num a
instance (NumE a, Num a) =>
    Num (Expr a) where
    (+) = arith Plus
    (*) = arith Times
    (-) = arith Minus
    negate = arith Minus (fromInteger 0)
    abs a = undefined -- needs expression-if: if (a !<! 0) then (0 - a) else a
    signum a = undefined -- needs expression-if: if (a !=! 0) then 0 else if (a !<! 0) then -1 else 1
    fromInteger n = constr (fromInteger n)
-- there's a pattern... f a = (constr a) (f (content a))

-- | Num instances are possible through this - slightly weird - helper
-- class which extracts constructors and values from an expression.
-- We also use this class to overload division (truncating on 'IntE',
-- conventional on 'RealE')
class Num a => NumE a where
    constr  :: a -> Expr a
    divide :: a -> a -> a

-- NB do we _ever_ use Int expressions? Maybe dump this whole weird thing
instance NumE Int where
    constr = I
    divide = div

instance NumE Double where
    constr = R
    divide = (/)

-- | Fractional instance for Expr Double, enables fractional literals
instance (NumE a, Fractional a) => Fractional (Expr a) where
    (/) = arith Div
    -- recip x = 1 / x -- default
    fromRational x = constr (fromRational x)

-- the smart constructors of the interface

i = I -- :: Int  -> IntE
r = R -- :: Double -> RealE
b = B -- :: Bool -> BoolE
v = V -- :: String -> Expr a
pair = Pair
first  = Fst
second  = Snd
obs      = Obs
chosenBy = ChosenBy
(!<!) :: Ord a => Expr a -> Expr a -> Expr Bool
(!<!) = Less
(!=!) :: Eq a => Expr a -> Expr a -> Expr Bool
(!=!) = Equal
-- (!|!) :: Expr Bool -> Expr Bool -> Expr Bool
(!|!) = Or

infixl 4 !<!
infixl 4 !=!
infixl 3 !|!

-- +, -, * come from the Num instance
maxx,minn :: (NumE a, Num a) => Expr a -> Expr a -> Expr a
maxx = arith Max -- instance magic would require an Ord instance...
minn = arith Min -- ...which requires an Eq instance

nott = Not

acc :: (Expr a -> Expr a) -> Int -> Expr a -> Expr a
acc _ 0 a = a
acc f i a = let v = newName "v" 
            in Acc (v,f (V v)) i a
-- using a unique supply, the quick way...
{-# NOINLINE idSupply #-}
idSupply :: MVar Int
idSupply = unsafePerformIO (newMVar 1)
newName :: String -> String
newName s = unsafePerformIO (do next <- takeMVar idSupply
 	                        putMVar idSupply (next+1)
	                        return (s ++ show next))

----------------------------------------------------------------

-- | Does an expression contain any observables or choices?
certainExp :: Expr a -> Bool
certainExp e = case e of
                 V _ -> False       --  if variables are used only for functions in Acc, we could return true here!
                 I _ -> True
                 R _ -> True
                 B _ -> True
                 Pair e1 e2 -> certainExp e1 && certainExp e2
                 Fst e -> certainExp e
                 Snd e -> certainExp e
                 Acc (v,e) i a -> certainExp e && certainExp a
                 Obs _ -> False
                 ChosenBy _ -> False
                 Not e1 -> certainExp e1
                 Arith _ e1 e2 -> certainExp e1 && certainExp e2
                 Less e1 e2 -> certainExp e1 && certainExp e2
                 Equal e1 e2 -> certainExp e1 && certainExp e2
                 Or e1 e2 -> certainExp e1 && certainExp e2

-- | translating an expression in time
translExp :: Expr a -> Int -> Expr a
translExp e 0 = e
translExp e d = 
    case e of
      I _-> e
      R _ -> e
      B _ -> e
      V _ -> e
      Pair e1 e2 -> pair (translExp e1 d) (translExp e2 d)
      Fst e -> Fst (translExp e d)
      Snd e -> Snd (translExp e d)
      Acc (v,e) i a -> Acc (v, translExp e d) i (translExp a d)
      Obs (s,t) -> obs (s,t+d)
      ChosenBy (p,t) -> chosenBy (p,t+d)
      Not e -> Not (translExp e d)
      Arith op e1 e2 -> Arith op (translExp e1 d) (translExp e2 d)
      Less e1 e2 -> Less (translExp e1 d) (translExp e2 d)
      Equal e1 e2 -> Equal (translExp e1 d) (translExp e2 d)
      Or e1 e2 -> Or (translExp e1 d) (translExp e2 d)

--------------------------------------------------------------
-- Evaluation of expressions:

data EvalExc = Eval String deriving (Read,Show,Typeable)
instance Exception EvalExc

evalI :: Env -> IntE -> Int
evalR :: Env -> RealE -> Double
evalB :: Env -> BoolE -> Bool
evalI env e = case eval env e of {I n -> n; _ -> throw (Eval "evalI failed")} 
evalR env e = case eval env e of {R n -> n; _ -> throw (Eval "evalR failed")} 
evalB env e = case eval env e of {B n -> n; _ -> throw (Eval "evalB failed")} 

-- Expr evaluator. Types checked statically, no checks required.
-- Assumes that the expr _can_ be evaluated, required fixings known
eval :: Env -> Expr a -> Expr a
eval env e = 
       case e of
         I _ -> e
         R _ -> e
         B _ -> e
         V s -> error ("missing variable env.")
         --
         Pair e1 e2 -> Pair (eval env e1) (eval env e2)
         Fst e ->
            (case eval env e of
               Pair v _ -> v
               e -> Fst e)
         Snd e ->
            (case eval env e of
               Pair _ v -> v
               e -> Snd e)
         --
         Obs u -> case env u of
                    Just r  -> R r
                    Nothing -> e
         ChosenBy (p,i) -> case env (p,i) of -- Hack: False is Double 0 in env.
                             Just r  -> B (r /= 0)
                             Nothing -> e
         --
         Acc (v,e) i a -> let a' = eval (promote env (- i)) a
                          in if i <= 0 then a
                              else if certainExp a'
                                   then error "missing variable env"
                                   -- eval (addV (v,eval env a') env) (Acc (v,translExp e 1) (i-1) e)
                                   else Acc (v,e) i a'
         --
         Not e' -> case eval env e' of
                     B b -> B (not b)
                     e'' -> Not e''
         Arith op e1 e2 -> arith op (eval env e1) (eval env e2)
         Less e1 e2 -> case (eval env e1, eval env e2) of
                          (I i1, I i2) -> B (i1 < i2)
                          (R r1, R r2) -> B (r1 < r2)
                          (ee1, ee2)   -> Less ee1 ee2
         Equal e1 e2 -> case (eval env e1, eval env e2) of
                          (I i1, I i2) -> B (i1 == i2)
                          (R r1, R r2) -> B (r1 == r2)
                          (B b1, B b2) -> B (b1 == b2)
                          (ee1, ee2)   -> Equal ee1 ee2
         Or e1 e2 -> case (eval env e1, eval env e2) of
                         (B b1, B b2) -> B (b1 || b2)
                         (B True, _ ) -> B True
                         (_, B True ) -> B True
                         (bb1, bb2)   -> Or bb1 bb2

-- | simplify an expression, using an environment
simplifyExp :: Env -> Expr a -> Expr a
simplifyExp env e = eval env e

-- | pretty-printer for operations. The Bool value indicates an infix operator.
ppOp :: AOp -> (String,Bool)
ppOp Plus   = ("+", True)
ppOp Minus  = ("-", True)
ppOp Times  = ("*", True)
ppOp Div    = ("/", True)
ppOp Max    = ("max ", False)
ppOp Min    = ("min ", False)

-- | real numbers printed with four decimal places (FX fashion)
ppReal :: Double -> String
ppReal = printf "%.4f"
