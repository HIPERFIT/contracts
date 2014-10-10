{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module SyntaxContract (
-- Real expression combinators
Currency,
Observable,
Party,
Elem,
Vars,

BinOp,
Cmp,
BoolOp,
Rexp,
Rexp',
rLit,
rAdd,
rMult,
rSubt,
rMin,
rMax,
obs,
rAcc,

-- Boolean expression combinators
Bexp,
Bexp',
bAcc,
bLit,
bNot,
rLt,
rLte,
rEq,

-- Contract combinators
Contract,
zero,
transfOne,
scale,
both,
translate,
ifWithin,

-- Operations on contracts
Inp,
ObsEnv,
ChoiceEnv,
Env,
obsEnvEmpty,
choiceEnvEmpty,
envEmpty,
specialise,
horizon,

Trans,
advance
) where

import qualified Contract as C

type BinOp = C.BinOp
type Cmp = C.Cmp
type BoolOp = C.BoolOp
type Vars = C.Vars

class Elem v a where inj :: v -> a
instance Elem v (Vars a v) where inj = C.New 
instance Elem v a => Elem v (Vars a v') where inj = C.Old . inj

type Choice = C.Choice
type Observable = C.Observable
type Currency = C.Currency
type Party = C.Party

type Rexp = C.Rexp
type Rexp' = C.Rexp'
type Bexp = C.Bexp
type Bexp' = C.Bexp'

-- Contract combinators
type Contract = C.Contract
zero :: Contract
zero = C.Zero
transfOne :: (Currency,Party,Party) -> Contract
transfOne(a,b,c) = C.TransfOne a b c
translate :: (Int, Contract) -> Contract
translate(a,b) = C.transl a b
both :: (Contract,Contract) -> Contract
both(a,b) = C.Both a b
ifWithin :: (Bexp, Int, Contract, Contract) -> Contract
ifWithin(a,b,c,d) = C.IfWithin a b c d
scale :: (Rexp, Contract) -> Contract
scale(a,b) = C.Scale a b

-- Real (double) expressions
racc :: (forall v. v -> Rexp' (Vars a v)) -> Int -> (Rexp' a) -> Rexp' a
racc f l z = C.RAcc (f ()) l z

rvar :: (Elem v a) => v -> Rexp' a
rvar v = C.RVar (inj v)

-- | HOAS combinator for building an accumulator
rAcc :: (forall v. (forall a'. Elem v a' => Rexp' a') 
        -> Rexp' (Vars a v)) -> Int -> (Rexp' a) -> Rexp' a
rAcc f l z = racc (\ x -> f  (rvar x)) l z

rLit :: Double -> Rexp
rLit = C.RLit

rAdd :: (Rexp,Rexp) -> Rexp
rAdd(a,b) = C.RBin C.Add a b

rMult :: (Rexp,Rexp) -> Rexp
rMult(a,b) = C.RBin C.Mult a b

rSubt :: (Rexp,Rexp) -> Rexp
rSubt(a,b) = C.RBin C.Subt a b

rMin :: (Rexp,Rexp) -> Rexp
rMin(a,b) = C.RBin C.Min a b

rMax :: (Rexp,Rexp) -> Rexp
rMax(a,b) = C.RBin C.Max a b

rNeg :: Rexp -> Rexp
rNeg = C.RNeg

obs :: (Observable,Int) -> Rexp
obs(a,b) = C.Obs a b

-- Boolean expressions
bacc :: (forall v. v -> Bexp' (Vars a v)) -> Int -> (Bexp' a) -> Bexp' a
bacc f l z = C.BAcc (f ()) l z

bvar :: (Elem v a) => v -> Bexp' a
bvar v = C.BVar (inj v)

bAcc :: (forall v. (forall a'. Elem v a' => Bexp' a') 
        -> Bexp' (Vars a v)) -> Int -> (Bexp' a) -> Bexp' a
bAcc f l z = bacc (\ x -> f  (bvar x)) l z

bLit :: Bool -> Bexp
bLit = C.BLit

bNot :: Bexp -> Bexp
bNot = C.BNot

rLt :: (Rexp, Rexp) -> Bexp
rLt(a,b) = C.RCmp C.LT a b

rLte :: (Rexp, Rexp) -> Bexp
rLte(a,b) = C.RCmp C.LTE a b

rEq :: (Rexp, Rexp) -> Bexp
rEq(a,b) = C.RCmp C.EQ a b

bChoice :: (Choice,Int) -> Bexp
bChoice(a,b) = C.BChoice a b

bAnd :: (Bexp,Bexp) -> Bexp
bAnd(a,b) = C.BOp C.And a b

bOr :: (Bexp,Bexp) -> Bexp
bOr(a,b) = C.BOp C.Or a b

horizon :: Contract -> Int
horizon = C.horizon

type Trans = Party -> Party -> Currency -> Double
advance :: Contract -> Env -> Maybe(Contract,Trans)
advance = C.redFun

type Inp a = Int -> Observable -> Maybe a
type ObsEnv = Inp Double
type ChoiceEnv = Inp Bool
type Env = (ObsEnv, ChoiceEnv)
specialise :: Contract -> Env -> Contract
specialise = C.specialise

obsEnvEmpty :: ObsEnv
obsEnvEmpty = C.obs_empty

envEmpty :: Env
envEmpty = C.ext_empty

choiceEnvEmpty :: ChoiceEnv
choiceEnvEmpty = C.choices_empty

deriving instance Show BinOp
deriving instance Show C.Cmp
deriving instance Show C.BoolOp
deriving instance Show C.ZeroT
deriving instance (Show a, Show v) => Show (Vars a v)
deriving instance Show a => Show (C.Rexp' a) 
deriving instance Show a => Show (C.Bexp' a) 
deriving instance Show Contract
