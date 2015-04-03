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
(!<!), (!<=!), (!=!), (!/=!), (!>!), (!>=!), (!&!), (!|!),
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
printContr,
showContr,

mkExtEnvP,

ExpHoas,
R, B,

) where

import Contract hiding (Exp,Contr,specialise,horizon,map)
import qualified Contract as C
import HOAS
import qualified Data.Map as Map
import Data.Maybe


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

printContr :: Contr -> IO ()
printContr = putStrLn . showContr

showContr :: Contr -> String
showContr = show . fromHoas
