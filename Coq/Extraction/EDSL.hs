{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module EDSL (
-- * Data types used in contracts
Asset (..),
Party (..),

Exp,
acc,
ife,
-- * Real expression combinators
RExp,
rLit,
rObs,


-- * Boolean expression combinators
BExp,
false, true,
(!<!), (!<=!), (!=!), (!>!), (!>=!), (!&!), (!|!),
bNot,
bObs,

-- * Contract combinators
ContrHoas,
Contr,
zero,
transfer,
scale,
(#),
both,
(&),
translate,
(!),
ifWithin,
iff,
letc,

-- * Operations on contracts
ObsLabel (..),
RealObs (..),
BoolObs (..),
ExtEnvP,
FMap,
horizon,
advance,
specialise,
hasType,

mkExtEnvP,

ExpHoas,
R, B,

) where


import Contract hiding (Exp,Contr,specialise,horizon,map)
import qualified Contract as C
import PrettyPrinting
import Data.Maybe

import qualified Data.Map as Map

instance Show C.Contr where
    show = ppContr 0 []

instance Show C.Exp where
    show = ppExp 0 []



toVar :: Int -> Var
toVar 0 = V1
toVar n = VS (toVar (n-1))

data R
data B

class ExpHoas' exp where
    ife :: exp B -> exp t -> exp t -> exp t
    opE :: Op -> [exp t'] -> exp t
    obs :: ObsLabel -> Int -> exp t
    acc :: (exp t -> exp t) -> Int -> exp t -> exp t

newtype DB t = DB {unDB :: Int -> C.Exp}

instance ExpHoas' DB where
    ife b e1 e2 = DB (\ i -> OpE Cond [unDB b i, unDB e1 i, unDB e2 i])
    opE op args = DB (\ i -> OpE op (map (($ i) . unDB) args))
    obs l t = DB (\_ -> Obs l t)
    acc f t e = DB (\i -> let v = \ j -> VarE (toVar (j-(i+1))) 
                          in Acc (unDB (f (DB v)) (i+1)) t (unDB e i))


rLit :: Double -> RExp
rLit r = opE (RLit r) []

instance Num (DB R) where
    x + y = opE Add [x,y]
    x * y = opE Mult [x,y]
    x - y = opE Sub [x,y]
    abs x = ife (x !<! 0) (- x) x
    signum x = ife (x !<! 0) (- 1) (ife (x !>! 0) 1 0)
    fromInteger i = rLit (fromInteger i)

instance Fractional (DB R) where
    fromRational r = rLit (fromRational r)
    x / y =  opE Div [x,y]
    


class (Num (exp R), Fractional (exp R), ExpHoas' exp) => ExpHoas exp

instance ExpHoas DB

type Exp t = forall exp . ExpHoas exp => exp t


rObs :: ExpHoas exp => RealObs -> Int -> exp R
rObs l i = obs (LabR l) i

type RExp = Exp R
type BExp = Exp B

(!=!) :: ExpHoas exp => exp R -> exp R -> exp B
x !=! y = opE Equal [x, y]

(!<!) :: ExpHoas exp => exp R -> exp R -> exp B
x !<! y = opE Less [x, y]

(!<=!) :: ExpHoas exp => exp R -> exp R -> exp B
x !<=! y = opE Leq [x, y]


(!>!) :: ExpHoas exp => exp R -> exp R -> exp B
(!>!) = (!<!)

(!>=!) :: ExpHoas exp => exp R -> exp R -> exp B
(!>=!) = (!<=!)


(!&!) :: ExpHoas exp => exp B -> exp B -> exp B
x !&! y = opE And [x, y]

(!|!) :: ExpHoas exp => exp B -> exp B -> exp B
x !|! y = opE Or [x, y]

bNot :: ExpHoas exp => exp B -> exp B
bNot x =  opE Not [x]

bObs :: ExpHoas exp => BoolObs -> Int -> exp B
bObs l i = obs (LabB l) i


false :: BExp
false = opE (BLit False) []

true :: BExp
true = opE (BLit True) []



newtype CDB = CDB {unCDB :: Int -> C.Contr}

class ExpHoas exp => ContrHoas exp contr | exp -> contr, contr -> exp where
    zero :: contr
    letc :: exp t -> (exp t -> contr) -> contr
    scale :: exp R -> contr -> contr
    both :: contr -> contr -> contr
    transfer :: Party -> Party -> Asset -> contr
    translate :: Int -> contr -> contr
    ifWithin :: exp B -> Int -> contr -> contr -> contr
    fromClosed :: C.Contr -> contr


instance ContrHoas DB CDB where
    zero = CDB (\_-> Zero)
    letc e c = CDB (\i -> let v = \ j -> VarE (toVar (j-(i+1))) 
                          in Let (unDB e i) (unCDB (c (DB v)) (i+1)))
    transfer p1 p2 a = CDB (\_-> Transfer p1 p2 a)
    scale e c = CDB (\i -> Scale (unDB e i) (unCDB c i))
    translate t c = CDB (\i -> Translate t (unCDB c i))
    both c1 c2 = CDB (\i -> Both (unCDB c1 i) (unCDB c2 i))
    ifWithin e t c1 c2 = CDB (\i -> If (unDB e i) t (unCDB c1 i) (unCDB c2 i))

    fromClosed c = CDB (const c)
    

type Contr = forall exp contr . ContrHoas exp contr => contr

fromHoas :: Contr -> C.Contr
fromHoas t = unCDB t 0

toHoas :: C.Contr -> Contr
toHoas c = fromClosed c

(&) :: ContrHoas exp contr => contr -> contr -> contr
(&) = both

(!) :: ContrHoas exp contr => Int -> contr -> contr
(!) = translate

(#) :: ContrHoas exp contr => exp R -> contr -> contr
(#) = scale


iff :: ContrHoas exp contr => exp B -> contr -> contr -> contr
iff e  = ifWithin e 0

horizon :: Contr -> Int
horizon c = C.horizon (fromHoas c)

advance :: Contr -> ExtEnvP -> (Contr, FMap)
advance c env = let (c',t) = fromJust (redfun (fromHoas c) [] env)
                in (toHoas c', t)

specialise :: Contr -> ExtEnvP -> Contr
specialise c = toHoas . C.specialise (fromHoas c) []

mkExtEnvP :: [(RealObs, Int,Double)] -> [(BoolObs, Int,Bool)] -> ExtEnvP
mkExtEnvP rs bs = env
    where real (l,i,r) = ((l,i),RVal r)
          bool (l,i,r) = ((l,i),BVal r)
          tabR = Map.fromList (map real rs)
          tabB = Map.fromList (map bool bs)
          env (LabR l) i = Map.lookup (l,i) tabR
          env (LabB l) i = Map.lookup (l,i) tabB


hasType :: Contr -> Bool
hasType = C.has_type . fromHoas
