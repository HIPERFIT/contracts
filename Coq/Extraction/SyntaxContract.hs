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
rNeg,
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
-- (||), (&&), true, false,

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

-- internal helpers for variables in expressions
class Elem v a where inj :: v -> a
instance Elem v (Vars a v) where inj = C.New 
instance Elem v a => Elem v (Vars a v') where inj = C.Old . inj


-- Contract combinators
zero :: Contract
zero = C.Zero

-- | Contract atom: transfer an asset from one party to another
transfer :: Currency -> Party -> Party -> Contract
transfer = C.TransfOne
-- combine with Scale in this API?

-- | move a contract into the future by a given amount of days. The
-- smart constructor merges successive translations into one.
translate :: Int -> Contract -> Contract
translate n c | n < 0 = error "translate: negative duration"
translate n1 (C.Transl n2 c) = C.transl (n1+n2) c -- generate?
translate n  (C.Zero) = zero
translate n     c     = C.transl n c

-- | combine two contracts
both :: Contract -> Contract -> Contract
both c1 C.Zero = c1
both C.Zero c2 = c2
-- if we had an Eq Contract instance:
-- both c1 c2 | c1 == c2  = C.Scale 2 c1
both c1 c2 = C.Both c1 c2

-- | iterated conditional contract: for the given amount of days,
-- check repeatedly whether the given boolean-valued expression is
-- true, and branch into the first contract argument in this case.
-- After the given amount of days, branch into the second one.
ifWithin :: Bexp -> Int -> Contract -> Contract -> Contract
ifWithin b n | n < 0 = error "ifWithin: negative duration"
             | n == 0 = maybe (C.IfWithin b 0) 
                              ifThenElse (bsem' b noVars (nothing,nothing))
    where ifThenElse True  c1 c2 = c1
          ifThenElse False c1 c2 = c2

-- | scale a contract by a real-valued expression. This smart
-- constructor aggregates multiple scalings and evaluates the given
-- expression before the scaled contract is constructed.
scale :: Rexp -> Contract -> Contract
scale e1 (C.Scale e2 c) = C.Scale (e1*e2) c -- generate?
scale e c = maybe (C.Scale e c) (\x -> if x == 0 then C.Zero else C.Scale (RLit x) c)
                  (rsem' e noVars nothing)

-- internal: empty environment
-- nothing :: C.Inp a
nothing _ _ = Nothing
-- internal: empty var. environment
-- noVars :: Env a v
noVars = C.Empty undefined

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

-- pretty number literals

-- | Num instance, enabling us to write 'e1 + e2' for RExp
instance Num (Rexp' a) where
    (+) = arith Add
    (*) = arith Mult
    (-) = arith Subt
    negate = arith Subt (fromInteger 0)
    abs a = undefined -- needs expression-if: if (a !<! 0) then (0 - a) else a
    signum a = undefined -- needs expression-if: if (a !=! 0) then 0 else if (a !<! 0) then -1 else 1
    fromInteger n = RLit (fromInteger n)

-- | Fractional instance enables fractional literals
instance Fractional Rexp where
    (/) = arith Div
    -- recip x = 1 / x -- default
    fromRational = RLit . fromRational

-- pre-evaluation of expressions if possible
arith :: BinOp -> Rexp' a -> Rexp' a -> Rexp' a
arith op (RLit x) (RLit y) = RLit (opsem op x y)
arith op e_x e_y = RBin op e_x e_y

-- | semantics of the arithmetic operators, for 'arith' smart constructor
opsem :: (Num a, Fractional a, Ord a) => BinOp -> a -> a -> a
opsem Add = (+)
opsem Subt = (-)
opsem Mult = (*)
opsem Div  = (/)
opsem Max = max
opsem Min = min

-- Bool literals and "pretty" operations are not as easy as numbers.
-- The following code works, but will generate name conflicts in the
-- importing modules (which import Prelude automatically)
-- We could define our own (|) and (&), though.

-- (||), (&&) :: Bexp' a -> Bexp' a -> Bexp' a
-- a || (BLit P.True) = BLit P.True
-- (BLit P.True) || b = BLit P.True
-- a || (BLit P.False) = a
-- (BLit P.False) || b = b
-- -- (BLit a) || (BLit b) = BLit (a P.|| b)
-- a || b = BOp Or a b

-- a && (BLit P.False) = BLit P.False
-- (BLit P.False) && b = BLit P.False
-- a && (BLit P.True) = a
-- (BLit P.True) && b = b
-- -- (BLit a) && (BLit b) = BLit (a P.&& b)
-- a && b = BOp And a b

-- false, true :: Bexp' ZeroT
-- false = BLit P.False
-- true  = BLit P.Tru
