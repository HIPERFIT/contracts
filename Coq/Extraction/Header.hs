{-# LANGUAGE GADTs #-}
module Contract (
-- Real expression combinators
Rexp,
rLit,
rBin,
rNeg,
obs,
-- rAcc,

-- Boolean expression combinators
Bexp,

-- Contract combinators
Contract,
zero,
transfOne,
scale,
both,
translate,
ifWithin,

-- Operations on contracts
Obs0,
Choices,
Ext,
obs_empty,
choices_empty,
ext_empty,
specialise,
horizon,

ppRexp, ppBexp

) where

import Prelude hiding (EQ, LT)

data Env a v where
  Empty :: (v -> a) -> Env a v
  Extend :: a -> Env a v -> Env a (Succ v)

count :: Env a v -> Int
count (Empty _) = 0
count (Extend _ e) = 1 + count e 

data PEnv a v v' where
  PEmpty :: (v -> a) -> PEnv a v v
  PExtend :: a -> PEnv a v v' -> PEnv a (Succ v) v'
  PSkip :: PEnv a v v' -> PEnv a (Succ v) (Succ v')

data ZeroT

unsafeCoerce = id

zero = Zero
transfOne(a,b,c) = TransfOne a b c
scale(a,b) = Scale a b
both(a,b) = Both a b
translate(a,b) = Transl a b
ifWithin(a,b,c,d) = IfWithin a b c d

ppBinOp :: BinOp -> String
ppBinOp b = 
  case b of
    Add -> "Add";
    Mult -> "Mult";
    Subt -> "Subt";
    Min -> "Min";
    Max -> "Max"

ppCmp :: Cmp -> String
ppCmp c =
  case c of
    EQ -> "EQ";
    LT -> "LT";
    LTE -> "LTE"

ppBoolOp :: BoolOp -> String
ppBoolOp b =
  case b of
    And -> "And";
    Or -> "Or"

ppRexp' :: Env Int a -> Rexp' a -> String
ppRexp' vars re =
  case re of
    RLit r -> show r;
    RBin op e1 e2 -> ppBinOp op ++ "(" ++ ppRexp' vars e1 ++ "," ++ ppRexp' vars e2 ++ ")";
    RNeg e0 -> "(- " ++ ppRexp' vars e0 ++ ")";
    Obs obs t -> "Obs(" ++ show obs ++ "," ++ show t ++ ")";
    RVar v -> "RVar(" ++ show (lookupEnv vars v) ++ ")";
    RAcc f l z ->
     let x = count vars in
     "RAcc(fn v" ++ show x ++ " -> " ++
           ppRexp' (Extend x (unsafeCoerce vars)) f ++ "," ++
           show l ++ "," ++
           ppRexp' vars z ++ ")"

ppBexp' :: Env Int a -> Bexp' a -> String
ppBexp' vars be =
  case be of
    BLit b -> show b;
    BChoice c i -> "Choice(" ++ show c ++ "," ++ show i ++ ")";
    RCmp c e1 e2 -> "(" ++ ppRexp e1 ++ " " ++ ppCmp c ++ " " ++ ppRexp e2 ++ ")";
    BNot e -> "Not(" ++ ppBexp' vars e ++ ")"
    BOp b e1 e2 -> "(" ++ ppBexp' vars e1 ++ " " ++ ppBoolOp b ++ " " ++ ppBexp' vars e2 ++ ")";
    BVar v -> "BVar(" ++ show (lookupEnv vars v) ++ ")";
    BAcc f l z ->
     let x = count vars in
     "BAcc(fn v" ++ show x ++ " -> " ++
        ppBexp' (Extend x (unsafeCoerce vars)) f ++ "," ++
        show l ++ "," ++
        ppBexp' vars z ++ ")"

ppRexp :: Rexp -> String
ppRexp e = ppRexp' (Empty zero1) e
 
ppBexp :: Bexp -> String
ppBexp e = ppBexp' (Empty zero1) e

pp :: Contract -> String
pp c =
  case c of
   Zero -> "zero";
   TransfOne c0 p1 p2 -> "transfOne(" ++ c0 ++ "," ++ p1 ++ "," ++ p2 ++ ")";
   Scale e c0 -> "scale(" ++ ppRexp e ++ "," ++ pp c0 ++ ")";
   Transl l c0 -> "transl(" ++ show l ++ "," ++ pp c0 ++ ")";
   Both c1 c2 -> "both(" ++ pp c1 ++ "," ++ pp c2 ++ ")";
   IfWithin b l c1 c2 -> "ifWithin(" ++ ppBexp b ++ "," ++ show l ++ "," ++ pp c1 ++ "," ++ pp c2 ++ ")"

instance Show Contract where show = pp

-- instance Show Rexp where show = ppRexp

-- instance Show Bexp where show = ppBexp

rLit = RLit
rBin(a,b,c) = RBin a b c
rNeg = RNeg
obs(a,b) = Obs a b
