{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
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
import Prelude as P (Int,Integer,error, Num(..), Fractional(..), fail, return, Bool(..), otherwise)
import qualified Prelude
 

infix  4  ==, /=, <, <=, >=, >  
infixr 3  &&  
infixr 2  || 
infix  1  `within`

class Eq a b | a -> b where
    (==) :: a -> a -> b
    (/=) :: a -> a -> b

instance ExpHoas exp => Eq (exp R) (exp B) where
    (==) = (!=!)
    (/=) = (!/=!)

instance Eq Int Bool where
    (==) = (Prelude.==)
    (/=) = (Prelude./=)

class Eq a b => Ord a b | a -> b where
    (<),(>=), (>), (<=) :: a -> a -> b

class Max a where
    max,min :: a -> a -> a

instance ExpHoas exp => Ord (exp R) (exp B) where
    (<) = (!<!)
    (<=) = (!<=!)
    (>) = (!>!)
    (>=) = (!>=!)

instance ExpHoas exp => Max (exp R) where
    max x y = if x !<! y then y else x
    min x y = if x !<! y then y else x

instance Ord Int Bool where
    (<) = (Prelude.<)
    (<=) = (Prelude.<=)
    (>) = (Prelude.>)
    (>=) = (Prelude.>=)

instance Prelude.Ord a => Max a where
    max = Prelude.max
    min = Prelude.min

class Boolean b where
    (&&) :: b -> b -> b
    (||) :: b -> b -> b
    not :: b -> b

instance ExpHoas exp => Boolean (exp B) where
    (&&) = (!&!)
    (||) = (!|!)
    not = bNot


instance Boolean Bool where
    (&&) = (Prelude.&&)
    (||) = (Prelude.||)
    not = Prelude.not


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

instance IfThenElse Bool a where
    ifThenElse True  x _ = x
    ifThenElse False _ y = y


instance ExpHoas exp => IfThenElse (exp B) (exp t) where
    ifThenElse = ife

instance ContrHoas exp contr => IfThenElse (exp B) contr where
    ifThenElse = iff


instance ContrHoas exp contr => IfThenElse (Within exp) contr where
    ifThenElse (Within b l) = ifWithin b l


(>>) :: ContrHoas exp contr => Wait -> contr -> contr
Wait n >> c = translate n c
