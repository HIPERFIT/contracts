{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module EDSL (
-- * Data types used in contracts
Asset,
Party,

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
reifyExp,

-- * Contract combinators
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
reifyContr,

-- * Operations on contracts
ObsLabel (..),
ExtEnv,
Trans,
horizon,
advance,
specialise,

mkExtEnvP,

R, B

) where


import Contract hiding (Exp,Contr,specialise)
import qualified Contract as C
import PrettyPrinting

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


newtype Exp t = Exp {unExp :: Int -> C.Exp}


ife :: Exp B -> Exp t -> Exp t -> Exp t
opE :: Op -> [Exp t'] -> Exp t
obs :: ObsLabel -> Int -> Exp t
acc :: (Exp t -> Exp t) -> Int -> Exp t -> Exp t

ife b e1 e2 = Exp (\ i -> OpE Cond [unExp b i, unExp e1 i, unExp e2 i])
opE op args = Exp (\ i -> OpE op (map (($ i) . unExp) args))
obs l t = Exp (\_ -> Obs l t)
acc f t e = Exp (\i -> let v = \ j -> VarE (toVar (j-(i+1))) 
                      in Acc (unExp (f (Exp v)) (i+1)) t (unExp e i))


rLit :: Double -> RExp
rLit r = opE (RLit r) []

instance Num (Exp R) where
    x + y = opE Add [x,y]
    x * y = opE Mult [x,y]
    x - y = opE Sub [x,y]
    abs x = ife (x !<! 0) (- x) x
    signum x = ife (x !<! 0) (- 1) (ife (x !>! 0) 1 0)
    fromInteger i = rLit (fromInteger i)

instance Fractional (Exp R) where
    fromRational r = rLit (fromRational r)
    x / y =  opE Div [x,y]
    




reifyExp :: Exp t -> C.Exp
reifyExp t = unExp t 0


rObs :: String -> Int -> Exp R
rObs l i = obs (LabR l) i

type RExp = Exp R
type BExp = Exp B

(!=!) :: Exp R -> Exp R -> Exp B
x !=! y = opE Equal [x, y]

(!<!) :: Exp R -> Exp R -> Exp B
x !<! y = opE Less [x, y]

(!<=!) :: Exp R -> Exp R -> Exp B
x !<=! y = opE Leq [x, y]


(!>!) :: Exp R -> Exp R -> Exp B
(!>!) = (!<!)

(!>=!) :: Exp R -> Exp R -> Exp B
(!>=!) = (!<=!)


(!&!) :: Exp B -> Exp B -> Exp B
x !&! y = opE And [x, y]

(!|!) :: Exp B -> Exp B -> Exp B
x !|! y = opE Or [x, y]

bNot :: Exp B -> Exp B
bNot x =  opE Not [x]

bObs :: String -> Int -> Exp B
bObs l i = obs (LabB l) i


false :: BExp
false = opE (BLit False) []

true :: BExp
true = opE (BLit True) []



newtype Contr = Contr {unContr :: Int -> C.Contr}


zero :: Contr
letc :: Exp t -> (Exp t -> Contr) -> Contr
scale :: Exp R -> Contr -> Contr
both :: Contr -> Contr -> Contr
transfer :: Party -> Party -> Asset -> Contr
translate :: Int -> Contr -> Contr
ifWithin :: Exp B -> Int -> Contr -> Contr -> Contr



zero = Contr (\_-> Zero)
letc e c = Contr (\i -> let v = \ j -> VarE (toVar (j-(i+1))) 
                      in Let (unExp e i) (unContr (c (Exp v)) (i+1)))
transfer p1 p2 a = Contr (\_-> Transfer p1 p2 a)
scale e c = Contr (\i -> Scale (unExp e i) (unContr c i))
translate t c = Contr (\i -> Translate t (unContr c i))
both c1 c2 = Contr (\i -> Both (unContr c1 i) (unContr c2 i))
ifWithin e t c1 c2 = Contr (\i -> If (unExp e i) t (unContr c1 i) (unContr c2 i))
    

reifyContr :: Contr -> C.Contr
reifyContr t = unContr t 0

(&) :: Contr -> Contr -> Contr
(&) = both

(!) :: Int -> Contr -> Contr
(!) = translate

(#) :: Exp R -> Contr -> Contr
(#) = scale


iff :: Exp B -> Contr -> Contr -> Contr
iff e  = ifWithin e 0


advance :: C.Contr -> ExtEnv -> Maybe (C.Contr, Trans)
advance c = redFun c []

specialise :: C.Contr -> ExtEnvP -> C.Contr
specialise c = C.specialise c []

mkExtEnvP :: [(RealObs, Int,Double)] -> [(BoolObs, Int,Bool)] -> ExtEnvP
mkExtEnvP rs bs = env
    where real (l,i,r) = ((l,i),RVal r)
          bool (l,i,r) = ((l,i),BVal r)
          tabR = Map.fromList (map real rs)
          tabB = Map.fromList (map bool bs)
          env (LabR l) i = Map.lookup (l,i) tabR
          env (LabB l) i = Map.lookup (l,i) tabB
