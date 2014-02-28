{-# LANGUAGE DeriveDataTypeable, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts, UndecidableInstances #-} 
module Contract.Expr
    ( Currency(..), Var
    , ExprG(..)    -- constructors exported, for internal use
    , BoolE, IntE, RealE -- for re-export
    -- constructors for interface
    , i, r, b, v, pair, first, second, acc, obs, chosenBy
    -- operators, unless in NUm instance
    , (!<!), (!=!), (!|!), maxx, minn, nott
    -- predicates, expression translate, hash
    , certainExp, translExp, hashExp
    -- pretty-printer (also std. printer for real numbers)
    , ppExp, ppReal
    -- environments
    , Env, MEnv(..), emptyEnv, emptyFrom
    , addFix, addFixing, addFixings
    , promote, promoteEnv
    -- evaluation
    , eval -- for internal use only
    , evalI, evalR, evalB, simplifyExp
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

-------------------------------------------------------------------------------

-- | Currency type. These are just tags and not used in expressions/arithmetics.
data Currency = EUR | DKK | SEK | USD | GBP | JPY
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
data ExprG a where
    I :: Int    -> ExprG Int
    R :: Double -> ExprG Double
    B :: Bool   -> ExprG Bool
    V :: Var    -> ExprG a
    -- Pairs:
    Pair :: ExprG a -> ExprG b -> ExprG (a,b)
    Fst :: ExprG (a,b) -> ExprG a
    Snd :: ExprG (a,b) -> ExprG b
    -- observables and external choices
    Obs :: (String, Int) -> ExprG Double
    ChosenBy :: (String, Int) -> ExprG Bool
    -- accumulator. Acc(f,i,a) := f/i(...(f/2(f/1(a))))
    Acc :: (Var, ExprG a) -> Int -> ExprG a -> ExprG a
    -- unary op.s: only "not"
    Not :: ExprG Bool -> ExprG Bool
    -- binary op.s, by type: +-*/ max min < = |
    -- on numerical arguments: +-*/ max min
    Arith :: Num a => AOp -> ExprG a -> ExprG a -> ExprG a
    Less  :: Ord a => ExprG a -> ExprG a -> ExprG Bool
    Equal :: Eq a  => ExprG a -> ExprG a -> ExprG Bool
    Or    :: ExprG Bool -> ExprG Bool -> ExprG Bool

-- | Show instance for debugging (cannot be derived automatically for GADTs)
instance Show (ExprG a) where
    show (I n) = "I " ++ show n
    show (R r) = "R " ++ ppReal r
    show (B b) = "B " ++ show b
    show (V v) = "V " ++ show v
    show (Pair e1 e2) = "Pair " ++ par (show e1) ++ par (show e2)
    show (Fst e) = "Fst " ++ par (show e)
    show (Snd e) = "Snd " ++ par (show e)
    show (Obs (s,i)) = "Obs " ++ par (show s ++ "," ++ show i)
    show (ChosenBy (p,i)) = "ChosenBy " ++ par (show p ++ "," ++ show i)
    show (Acc (v,e) i a) = "Acc " ++ unwords [par (show v ++ "," ++ show e),
                                             show i, par (show a)]
    show (Not e) = "Not " ++ par (show e)
    show (Arith op e1 e2) = "Arith " ++ unwords [show op, par (show e1),
                                                 par (show e2)]
    show (Less e1 e2) = "Less " ++ unwords [par (show e1), par (show e2)]
    show (Equal e1 e2) = "Equal " ++ unwords [par (show e1), par (show e2)]
    show (Or e1 e2) = "Or " ++ unwords [par (show e1), par (show e2)]

-- parenthesis around a string
par s = "(" ++ s ++ ")"

-- | Supported arithmetic operations as a data type
data AOp = Plus | Minus | Times | Max | Min
         deriving (Show)

-- | pretty-printer for operations. The Bool value indicates an infix operator.
ppOp :: AOp -> (String,Bool)
ppOp Plus   = ("+", True)
ppOp Minus  = ("-", True)
ppOp Times  = ("*", True)
ppOp Max    = ("max ", False)
ppOp Min    = ("min ", False)

-- | Operators can be read in
instance Read AOp where
    readsPrec _ ('+':rest) = [(Plus,rest)]
    readsPrec _ ('-':rest) = [(Minus,rest)]
    readsPrec _ ('*':rest) = [(Times,rest)]
    readsPrec _ ('m':'a':'x':rest) = [(Max,rest)]
    readsPrec _ ('m':'i':'n':rest) = [(Min,rest)]
    readsPrec _ _ = []

-- | Aliases for the expression types we use
type BoolE = ExprG Bool
type IntE = ExprG Int
type RealE = ExprG Double

-- | arithmetics smart constructor, trying to optimise by evaluating constants
arith :: Num a => AOp -> ExprG a -> ExprG a -> ExprG a
arith op (I i1) (I i2) = I (opsem op i1 i2)
arith op (R r1) (R r2) = R (opsem op r1 r2)
arith Plus e1 e2  = Arith Plus  e1 e2
arith Minus e1 e2 = Arith Minus e1 e2
arith Times e1 e2 = Arith Times e1 e2
arith Max e1 e2   = Arith Max   e1 e2
arith Min e1 e2   = Arith Min   e1 e2

-- | semantics of the arithmetic operators, for 'arith' smart constructor
opsem :: (Ord a, Num a) => AOp -> a -> a -> a
opsem Plus = (+)
opsem Minus = (-)
opsem Times = (*)
opsem Max = max
opsem Min = min

-- | Expression equality is defined using hashExpr (considering commutativity)
instance Eq (ExprG a) where
     e1 == e2 = hashExp [] e1 0 == hashExp [] e2 0

-- | Computes hash of an expression, for syntactic comparisons. Considers commutativity by symmetric hashing scheme for commutative operations.
hashExp :: [Var] -> ExprG a -> Hash -> Hash -- need to give an explicit type
hashExp vs e a = 
    let ps = hashPrimes
    in case e of
         V v -> case index v vs of
                  Just i -> hash (ps!!0) (hash i a)
                  Nothing -> hash (ps!!0) (hashStr v a)
         I i -> hash (ps!!1) (hash i a)
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
        -- not symmetric!
         Less e1 e2 -> hash (ps!!12) (hashExp vs e1 (hashExp vs e2 a))
         Arith Minus e1 e2 -> hash (ps!!13) (hashExp vs e1 (hashExp vs e2 a))
        -- symmetric! (commutative)
         Arith op e1 e2 
             -> hashStr (fst (ppOp op)) (hashExp vs e1 (hashExp vs e2 a))
         Equal e1 e2 -> hashStr "=" (hashExp vs e1 (hashExp vs e2 a))
         Or e1 e2    -> hashStr "|" (hashExp vs e1 (hashExp vs e2 a))

----------------------------------------

-- | Num instance, enabling us to write 'e1 + e2' for ExprG a with Num a
instance (Decompose (ExprG a), Num (Content (ExprG a)), Num a) =>
    Num (ExprG a) where
    (+) = arith Plus
    (*) = arith Times
    (-) = arith Minus
    negate = arith Minus (fromInteger 0)
    abs a = (constr a) (abs (content a))
    signum a = (constr a) (signum (content a))
    fromInteger n = (constr (undefined :: ExprG a)) (fromInteger n)
-- there's a pattern... f a = (constr a) (f (content a))

-- | Num instances are possible through this - slightly weird - helper
-- class which extracts constructors and values from an expression
class Num a => Decompose a where
    type Content a
    constr  :: a -> (Content a -> a)
    content :: Num (Content a) => a -> Content a

-- NB do we _ever_ use Int expressions? Maybe dump this whole weird thing
instance Decompose (ExprG Int) where
    type Content (ExprG Int) = Int
    constr _  = I
    content x = evalI emptyEnv x

instance Decompose (ExprG Double) where
    type Content (ExprG Double) = Double
    constr  _ = R
    content x = evalR emptyEnv x

-- the smart constructors of the interface

i = I -- :: Int  -> IntE
r = R -- :: Double -> RealE
b = B -- :: Bool -> BoolE
v = V -- :: String -> ExprG a
pair = Pair
first  = Fst
second  = Snd
obs      = Obs
chosenBy = ChosenBy
(!<!) :: Ord a => ExprG a -> ExprG a -> ExprG Bool
(!<!) = Less
(!=!) :: Eq a => ExprG a -> ExprG a -> ExprG Bool
(!=!) = Equal
-- (!|!) :: ExprG Bool -> ExprG Bool -> ExprG Bool
(!|!) = Or

infixl 4 !<!
infixl 4 !=!
infixl 3 !|!

-- +, -, * come from the Num instance
maxx,minn :: Num a => ExprG a -> ExprG a -> ExprG a
maxx = arith Max -- instance magic would require an Ord instance...
minn = arith Min -- ...which requires an Eq instance

nott = Not

acc :: (ExprG a -> ExprG a) -> Int -> ExprG a -> ExprG a
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
certainExp :: ExprG a -> Bool
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
translExp :: ExprG a -> Int -> ExprG a
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

-----------------------------------------------------------------
-- Pretty-print an expression (not the same as the Show instance)

-- | real numbers printed with four decimal places (FX fashion)
ppReal :: Double -> String
ppReal = printf "%.4f"

-- | internal: print an expression, using an int printing function
ppExp0 :: (Int -> String) -> ExprG a -> String
ppExp0 ppInt e = 
    case e of
           V s -> s
           I i -> ppInt i
           R r -> ppReal r
           B b -> show b
           Pair e1 e2 -> par (ppExp0 ppInt e1 ++ "," ++ ppExp0 ppInt e2)
           Fst e -> "first" ++ par (ppExp0 ppInt e)
           Snd e -> "second" ++ par (ppExp0 ppInt e)
           Acc f i e -> "acc" ++ par(ppFun f ++ "," ++ show i ++ "," ++ ppExp e)
           Obs (s,off) -> "Obs" ++ par (s ++ "@" ++ ppInt off)
           ChosenBy (p,i) -> "Chosen by " ++ p ++ " @ " ++ ppInt i
           Not e1 -> "not" ++ par (ppExp e1)
           Arith op e1 e2 -> let (c,infx) = ppOp op
                             in if infx then par(ppExp e1 ++ c ++ ppExp e2)
                                else c ++ par (ppExp e1) ++ ' ':par(ppExp e2)
           Less e1 e2 -> par(ppExp0 ppInt e1 ++ " < " ++ ppExp0 ppInt e2)
           Equal e1 e2 -> par(ppExp0 ppInt e1 ++ "==" ++ ppExp0 ppInt e2)
           Or e1 e2 ->  par(ppExp e1 ++ "||" ++ ppExp e2)
    where ppExp e = ppExp0 ppInt e
          ppFun (v,e) = "\\" ++ v ++ " -> " ++ ppExp e

-- | pretty-printing an expression, using normal printer for Int
ppExp = ppExp0 show

--------------------------------------------------------------
-- Evaluation of expressions:

data EvalExc = Eval String deriving (Read,Show,Typeable)
instance Exception EvalExc

-- | An environment is a partial mapping from (String, Int) to Double. The keys carry an identifying string and an offset value (days), yielding a Double value.
type Env = (String, Int) -> Maybe Double -- Hack: should use Bool for choice

-- | an empty environment. 
emptyEnv :: Env
emptyEnv = \(s,i) -> if s == "Time" then Just (fromIntegral i) else Nothing

-- ideas:
-- unify :: Env -> Env -> Env

-- envFrom :: String -> (Int -> Double) -> Env
-- envFrom s f = ...

-- | A managed environment is an environment together with a start date.
data MEnv = Env Date Env

-- | an empty managed environment, from a given start date
emptyFrom :: Date -> MEnv
emptyFrom d = Env d emptyEnv

-- | promoting an environment by a given date offset into the future (or past, if negative)
promote :: Env -> Int -> Env
promote e i = e . (\(s,x) -> (s,x+i))

-- | promoting a managed environment by a given date offset. See 'promote'
promoteEnv :: MEnv -> Int -> MEnv
promoteEnv (Env d e) i = Env d (promote e i)

-- | adding a fixing to an environment.
-- New values take precedence with this definition
addFix :: (String, Int, Double) -> Env -> Env
addFix (s,d,r) e = \x -> if x == (s,d) then Just r else e x

-- | adding a fixing to a managed environment
addFixing :: (String, Date, Double) -> MEnv -> MEnv
addFixing (s,d,r) (Env e_d e_f) = 
    let off = dateDiff e_d d
    in Env e_d (\x -> if x == (s,off) then Just r else e_f x)


addFixings :: (String, Date) -> [Double] -> MEnv -> MEnv
addFixings (s,d) [] e = e
addFixings (s,d) vs (Env e_d e_f) =
    let l = length vs
        o = dateDiff e_d d
        f (s',n) = if s == s' && n >= o && n < l + o
                     then Just (vs!!(n-o)) else e_f (s',n)
    in Env e_d f

evalI :: Env -> IntE -> Int
evalR :: Env -> RealE -> Double
evalB :: Env -> BoolE -> Bool
evalI env e = case eval env e of {I n -> n; _ -> throw (Eval "evalI failed")} 
evalR env e = case eval env e of {R n -> n; _ -> throw (Eval "evalR failed")} 
evalB env e = case eval env e of {B n -> n; _ -> throw (Eval "evalB failed")} 

-- ExprG evaluator. Types checked statically, no checks required.
-- Assumes that the expr _can_ be evaluated, required fixings known
eval :: Env -> ExprG a -> ExprG a
eval env e = 
       case e of
         I _ -> e
         R _ -> e
         B _ -> e
         V s -> error ("missing variable env.")
         --
         Pair e1 e2 -> Pair (eval env e1) (eval env e2)
         Fst e -> Fst (eval env e)
         Snd e -> Snd (eval env e)
         --
         Obs u -> case env u of
                    Just r  -> R r
                    Nothing -> e
         ChosenBy (p,i) -> case env (p,i) of -- Hack: False is Double 0 in env.
                             Just r  -> B (r /= 0)
                             Nothing -> e
         --
         Acc (v,e) i a -> let a' = eval env a
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
simplifyExp env e = eval env e

