{-# LANGUAGE GADTs #-}

module Contract where

import Prelude hiding (EQ, LT)

data Vars a v =
   Old a
 | New v

type Succ a = Vars a ()

zero1 :: a1
zero1 =
  Prelude.error "absurd case"

data Env a x where
   Empty :: (x -> a) -> Env a x
   Extend :: a -> Env a x -> Env a (Succ x)

lookupEnv :: (Env a1 a2) -> a2 -> a1
lookupEnv e =
  case e of {
   Empty f -> f;
   Extend b r -> (\v ->
    case v of {
     Old v' -> lookupEnv r v';
     New u -> b})}

type Observable = String

type Currency = String

type Party = String

type Choice = String

data BinOp =
   Add
 | Mult
 | Subt
 | Min
 | Max

data Cmp =
   EQ
 | LT
 | LTE

data BoolOp =
   And
 | Or

data Rexp' x =
   RLit Int
 | RBin BinOp (Rexp' x) (Rexp' x)
 | RNeg (Rexp' x)
 | Obs Observable Int
 | RVar x
 | RAcc (Rexp' (Succ x)) Int (Rexp' x)

type Rexp = Rexp' ()

data Bexp =
   BLit Bool
 | BChoice Choice Int
 | RCmp Cmp Rexp Rexp
 | BNot Bexp
 | BOp BoolOp Bexp Bexp

data Contract =
   Zero
 | TransfOne Currency Party Party
 | Scale Rexp Contract
 | Transl Int Contract
 | Both Contract Contract
 | IfWithin Bexp Int Contract Contract

type Inp a = Int -> Observable -> Maybe a

type Obs0 = Inp Int

type Choices = Inp Bool

adv_inp :: Int -> (Inp a1) -> Inp a1
adv_inp d e x =
  e ((+) d x)

type Env0 = (,) Obs0 Choices

rBinOp :: BinOp -> Int -> Int -> Int
rBinOp op =
  case op of {
   Add -> (+);
   Mult -> (*);
   Subt -> (-);
   Min -> (\x y ->
    case (<=) x y of {
     True -> x;
     False -> y});
   Max -> (\x y ->
    case (<=) x y of {
     True -> y;
     False -> x})}

option_map2 :: (a1 -> a2 -> a3) -> (Maybe a1) -> (Maybe a2) -> Maybe a3
option_map2 f o1 o2 =
  case o1 of {
   Just a ->
    case o2 of {
     Just b -> Just (f a b);
     Nothing -> Nothing};
   Nothing -> Nothing}

acc :: (Int -> a1 -> a1) -> Int -> a1 -> a1
acc f n z =
  (\fO fS n -> if n==0 then fO () else fS (n-1))
    (\_ ->
    z)
    (\n' ->
    f n (acc f n' z))
    n

rsem' :: (Rexp' a1) -> (Env (Maybe Int) a1) -> Obs0 -> Maybe Int
rsem' e vars rho =
  case e of {
   RLit r -> Just r;
   RBin op e1 e2 ->
    option_map2 (rBinOp op) (rsem' e1 vars rho) (rsem' e2 vars rho);
   RNeg e0 -> fmap ((-) 0) (rsem' e0 vars rho);
   Obs obs t -> rho t obs;
   RVar v -> lookupEnv vars v;
   RAcc f l z ->
    let {rho' = adv_inp (negate (id l)) rho} in
    acc (\m x ->
      rsem' f (Extend x vars) (adv_inp (id m) rho')) l
      (rsem' z vars rho')}

bBinOp :: BoolOp -> Bool -> Bool -> Bool
bBinOp op =
  case op of {
   And -> (&&);
   Or -> (||)}

rCompare :: Cmp -> Int -> Int -> Bool
rCompare cmp =
  case cmp of {
   EQ -> (==);
   LT -> (\x y -> not ((<=) y x));
   LTE -> (<=)}

bsem :: Bexp -> Env0 -> Maybe Bool
bsem e rho =
  case e of {
   BLit r -> Just r;
   BChoice choice z -> snd rho z choice;
   RCmp cmp e1 e2 ->
    option_map2 (rCompare cmp) (rsem' e1 (Empty (\_ -> zero1)) (fst rho))
      (rsem' e2 (Empty (\_ -> zero1)) (fst rho));
   BNot e0 -> fmap not (bsem e0 rho);
   BOp op e1 e2 -> option_map2 (bBinOp op) (bsem e1 rho) (bsem e2 rho)}

type Trans = Party -> Party -> Currency -> Int

empty_trans' :: Trans
empty_trans' p1 p2 c =
  0

singleton_trans' :: String -> String -> String -> Int -> Trans
singleton_trans' p1 p2 c r p1' p2' c' =
  case (&&) ((==) p1 p1') ((&&) ((==) p2 p2') ((==) c c')) of {
   True -> r;
   False -> 0}

add_trans' :: Trans -> Trans -> Trans
add_trans' t1 t2 p1 p2 c =
  (+) (t1 p1 p2 c) (t2 p1 p2 c)

scale_trans' :: Int -> Trans -> Trans
scale_trans' s t p1 p2 c =
  (*) (t p1 p2 c) s

adv_rexp :: Int -> (Rexp' a1) -> Rexp' a1
adv_rexp d e =
  case e of {
   RBin op e1 e2 -> RBin op (adv_rexp d e1) (adv_rexp d e2);
   RNeg e' -> RNeg (adv_rexp d e');
   Obs o i -> Obs o ((+) d i);
   RAcc f n z -> RAcc (adv_rexp d f) n (adv_rexp d z);
   x -> x}

redFun :: Contract -> Env0 -> Maybe ((,) Contract Trans)
redFun c rho =
  case c of {
   Zero -> Just ((,) Zero empty_trans');
   TransfOne c0 p1 p2 -> Just ((,) Zero (singleton_trans' c0 p1 p2 (succ 0)));
   Scale e c0 ->
    case redFun c0 rho of {
     Just p ->
      case p of {
       (,) c' t ->
        case rsem' e (Empty (\_ -> zero1)) (fst rho) of {
         Just v -> Just ((,) (Scale (adv_rexp (pred 0) e) c')
          (scale_trans' v t));
         Nothing -> Nothing}};
     Nothing -> Nothing};
   Transl l c0 ->
    (\fO fS n -> if n==0 then fO () else fS (n-1))
      (\_ ->
      redFun c0 rho)
      (\l' -> Just ((,) (Transl l' c0)
      empty_trans'))
      l;
   Both c1 c2 ->
    case redFun c1 rho of {
     Just p ->
      case p of {
       (,) c1' t1 ->
        case redFun c2 rho of {
         Just p0 ->
          case p0 of {
           (,) c2' t2 -> Just ((,) (Both c1' c2') (add_trans' t1 t2))};
         Nothing -> Nothing}};
     Nothing -> Nothing};
   IfWithin b l c1 c2 ->
    case bsem b rho of {
     Just b0 ->
      case b0 of {
       True -> redFun c1 rho;
       False ->
        (\fO fS n -> if n==0 then fO () else fS (n-1))
          (\_ ->
          redFun c2 rho)
          (\l' -> Just ((,) (IfWithin b l' c1 c2)
          empty_trans'))
          l};
     Nothing -> Nothing}}

horizon :: Contract -> Int
horizon c =
  case c of {
   Scale r c' -> horizon c';
   Transl l c' -> (+) l (horizon c');
   Both c1 c2 -> max (horizon c1) (horizon c2);
   IfWithin b l c1 c2 -> (+) l (max (horizon c1) (horizon c2));
   _ -> 0}

