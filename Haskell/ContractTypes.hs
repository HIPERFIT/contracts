{-# LANGUAGE DeriveDataTypeable #-} 
module ContractTypes
    where

-- to define the exception
import Control.Exception
import Data.Typeable

data Currency = EUR | DKK | SEK | USD | GBP | JPY
-- good enough with only FX derivatives. Otherwise we could add this:
-- "... | Stock String | Equity String"

ppCur EUR = "EUR"
ppCur DKK = "DKK"
ppCur SEK = "SEK"
ppCur USD = "USD"
ppCur GBP = "GBP"
ppCur JPY = "JPY"

-- submodule expression starts here
type Var = String

type BoolE = Expr Bool
type IntE = Expr Int
type RealE = Expr Double

var :: Var -> Expr a

type BinOpT a = Expr a -> Expr a -> Expr a

(!+!) :: Num a => BinOpT a
(!-!) :: Num a => BinOpT a
(!*!) :: Num a => BinOpT a
(!<!) :: Expr a -> Expr a -> Expr Bool
(!=!) :: Expr a -> Expr a -> Expr Bool
(!|!) :: BinOpT Bool
obs :: (String, Int) -> Expr a
i :: Int  -> IntE
r :: Double -> RealE
b :: Bool -> BoolE

data EvalExc = Eval String deriving (Read,Show,Typeable)
instance Exception EvalExc

type Env = (String, Int) -> RealE -- nicer if it was Expr a

evalR :: Env -> RealE -> Double
evalI :: Env -> IntE -> Int
evalB :: Env -> BoolE -> Bool

-- general:
evalX :: Env -> Expr a -> a
evalX = undefined
-- all these evaluators assume that the expr _can_ be evaluated,
-- i.e. all required fixings are known

data Expr0 = I Int | R Double | B Bool | V Var 
           | BinOp String Expr0 Expr0 | UnOp String Expr0 | Obs (String,Int)
type Expr a = Expr0

{- should be using a GADT instead
data ExprG a where
    I :: Int    -> ExprG Int
    R :: Double -> ExprG Double
    B :: Bool   -> ExprG Bool
    V :: Var    -> ExprG a
    ... should this split up the operators according to their phantom types?
-}

-- infix !+! !-! !*! !<! !=! !|!
x !+! y = BinOp "+" x y
x !-! y = BinOp "-" x y
x !*! y = BinOp "*" x y
x !<! y = BinOp "<" x y
x !=! y = BinOp "=" x y
x !|! y = BinOp "|" x y

obs = Obs
var = V
i = I
r = R
b = B

binopII opr i1 i2 =
    case opr of
      "+" -> I (i1+i2)
      "-" -> I (i1-i2) 
      "*" -> I (i1*i2) 
      "<" -> B (i1<i2) 
      "=" -> B (i1==i2) 
      _   -> error ("binopII: operator not supported: " ++ opr)
binopRR opr r1 r2 =
       case opr of
         "+" -> R (r1+r2)
         "-" -> R (r1-r2) 
         "*" -> R (r1*r2) 
         "<" -> B (r1<r2) 
         "=" -> B (r1==r2) 
         _   -> error ("binopRR: operator not supported: " ++ opr)
binopBB opr b1 b2 =
       case opr of
         "=" -> B (b1==b2)
         _   -> error ("binopBB: operator not supported: " ++ opr)

eval env e =
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
