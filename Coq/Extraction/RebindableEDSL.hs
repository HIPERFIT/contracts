{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}

module RebindableEDSL
    (
     -- * comparison operators                            
     (<), (<=), (==), (/=), (>), (>=), 
     -- * Boolean operators
     (&&), (||), not,

     -- * do notation
     (>>=), 
     (>>),
     wait ,
     max,
     min,

     module P,
     ifThenElse,
     within,
     module EDSL,
) where


import EDSL
import Prelude as P (Int,Integer,error, Num(..), Fractional(..), fail, return, Bool(..))
 

infix  4  ==, /=, <, <=, >=, >  
infixr 3  &&  
infixr 2  || 
infix  1  `within`


max :: ExpHoas exp => exp R -> exp R -> exp R
max x y = if x < y then y else x

min :: ExpHoas exp => exp R -> exp R -> exp R
min x y = if x < y then x else y

(/=) :: ExpHoas exp => exp R -> exp R -> exp B
(/=) = (!/=!)


(==) :: ExpHoas exp => exp R -> exp R -> exp B
(==) = (!=!)

(<) :: ExpHoas exp => exp R -> exp R -> exp B
(<) = (!<!)

(<=) :: ExpHoas exp => exp R -> exp R -> exp B
(<=) = (!<=!)


(>) :: ExpHoas exp => exp R -> exp R -> exp B
(>) = (!>!)

(>=) :: ExpHoas exp => exp R -> exp R -> exp B
(>=) = (!>=!)


(&&) :: ExpHoas exp => exp B -> exp B -> exp B
(&&) = (!&!)

(||) :: ExpHoas exp => exp B -> exp B -> exp B
(||) = (!|!)

not :: ExpHoas exp => exp B -> exp B
not = bNot



(>>=) :: ContrHoas exp contr => exp t -> (exp t -> contr) -> contr
(>>=) = letc

newtype Wait = Wait Int

wait :: Int -> Wait
wait = Wait

data Within exp = Within (exp B) Int

within :: ExpHoas exp => exp B -> Int -> Within exp
within = Within

class IfThenElse b c where
    ifThenElse :: b -> c -> c -> c

instance ExpHoas exp => IfThenElse (exp B) (exp t) where
    ifThenElse = ife

instance ContrHoas exp contr => IfThenElse (exp B) contr where
    ifThenElse = iff


instance ContrHoas exp contr => IfThenElse (Within exp) contr where
    ifThenElse (Within b l) = ifWithin b l


(>>) :: ContrHoas exp contr => Wait -> contr -> contr
Wait n >> c = translate n c
