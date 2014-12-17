{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}

module RebindableEDSL
    (
     -- * comparison operators                            
     (<), (<=), (==), (>), (>=), 
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
     module EDSL
) where


import EDSL
import Prelude as P (Int,Integer,error, Num(..), Fractional(..), fail, return, Bool(..))


max :: Exp R -> Exp R -> Exp R
max x y = if x < y then y else x

min :: Exp R -> Exp R -> Exp R
min x y = if x < y then x else y


(==) :: Exp R -> Exp R -> Exp B
(==) = (!=!)

(<) :: Exp R -> Exp R -> Exp B
(<) = (!<!)

(<=) :: Exp R -> Exp R -> Exp B
(<=) = (!<=!)


(>) :: Exp R -> Exp R -> Exp B
(>) = (!>!)

(>=) :: Exp R -> Exp R -> Exp B
(>=) = (!>=!)


(&&) :: Exp B -> Exp B -> Exp B
(&&) = (!&!)

(||) :: Exp B -> Exp B -> Exp B
(||) = (!|!)

not :: Exp B -> Exp B
not = bNot



(>>=) :: Exp t -> (Exp t -> Contr) -> Contr
(>>=) = letc

newtype Wait = Wait Int

wait :: Int -> Wait
wait = Wait

data Within = Within BExp Int

within :: Exp B -> Int -> Within
within = Within

class IfThenElse b c where
    ifThenElse :: b -> c -> c -> c

instance IfThenElse (Exp B) (Exp t) where
    ifThenElse = ife

instance IfThenElse (Exp B) Contr where
    ifThenElse = iff


instance IfThenElse Within Contr where
    ifThenElse (Within b l) = ifWithin b l


(>>) :: Wait -> Contr -> Contr
Wait n >> c = translate n c
