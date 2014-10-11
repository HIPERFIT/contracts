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
BinOp(Add,Mult,Subt,Div,Min,Max),
Cmp(EQ,LT,LTE),
BoolOp(And,Or),
Rexp,
Rexp',
rLit,
rBin,
rObs,
rAcc,

-- Boolean expression combinators
Bexp,
Bexp',
bAcc,
bLit,
bNot,
rCmp,
bObs,
bBin,

-- Contract combinators
Contract,
zero,
transfer,
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
specialize,
horiz,

Trans,
advance
) where

import Contract as C hiding (Env,Inp,Trans)

class Elem v a where inj :: v -> a
instance Elem v (Vars a v) where inj = C.New 
instance Elem v a => Elem v (Vars a v') where inj = C.Old . inj


-- Contract combinators
zero :: Contract
zero = C.Zero
transfer :: Currency -> Party -> Party -> Contract
transfer = C.TransfOne
translate :: Int -> Contract -> Contract
translate = C.transl
both :: Contract -> Contract -> Contract
both = C.Both
ifWithin :: Bexp -> Int -> Contract -> Contract -> Contract
ifWithin = C.IfWithin
scale :: Rexp -> Contract -> Contract
scale = C.Scale

-- Real (double) expressions
racc :: (forall v. v -> Rexp' (Vars a v)) -> Int -> (Rexp' a) -> Rexp' a
racc f l z = C.RAcc (f ()) l z

rvar :: (Elem v a) => v -> Rexp' a
rvar v = C.RVar (inj v)

-- | HOAS combinator for building an accumulator
rAcc :: (forall v. (forall a'. Elem v a' => Rexp' a') 
        -> Rexp' (Vars a v)) -> Int -> (Rexp' a) -> Rexp' a
rAcc f l z = racc (\ x -> f  (rvar x)) l z

rLit :: Double -> Rexp' a
rLit = C.RLit

rBin :: BinOp -> Rexp' a -> Rexp' a -> Rexp' a
rBin = C.RBin

rNeg :: Rexp' a -> Rexp' a
rNeg = C.RNeg

rObs :: Observable -> Int -> Rexp' a
rObs = C.Obs

-- Boolean expressions
bacc :: (forall v. v -> Bexp' (Vars a v)) -> Int -> (Bexp' a) -> Bexp' a
bacc f l z = C.BAcc (f ()) l z

bvar :: (Elem v a) => v -> Bexp' a
bvar v = C.BVar (inj v)

bAcc :: (forall v. (forall a'. Elem v a' => Bexp' a') 
        -> Bexp' (Vars a v)) -> Int -> (Bexp' a) -> Bexp' a
bAcc f l z = bacc (\ x -> f  (bvar x)) l z

bLit :: Bool -> Bexp' a
bLit = C.BLit

bNot :: Bexp' a -> Bexp' a
bNot = C.BNot

rCmp :: Cmp -> Rexp -> Rexp -> Bexp' a
rCmp = C.RCmp

bObs :: Choice -> Int -> Bexp' a
bObs = C.BChoice

bBin :: BoolOp -> Bexp' a -> Bexp' a -> Bexp' a
bBin = C.BOp

horiz :: Contract -> Int
horiz = C.horizon

type Trans = Party -> Party -> Currency -> Double
advance :: Contract -> Env -> Maybe(Contract,Trans)
advance = C.redFun

type Inp a = Int -> Observable -> Maybe a
type ObsEnv = Inp Double
type ChoiceEnv = Inp Bool
type Env = (ObsEnv, ChoiceEnv)
specialize :: Contract -> Env -> Contract
specialize = C.specialise

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
