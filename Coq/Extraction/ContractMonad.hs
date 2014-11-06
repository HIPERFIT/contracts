{-# LANGUAGE FlexibleInstances #-}

module ContractMonad where

import SyntaxContract
import Control.Monad.Reader(liftM2)

data CM a = CM ((a->Int->Contract)->Int->Contract)

--instance Applicative CM where
--  pure a = CM (\k i -> k a i)
--  CM a <*> CM b = \ f -> 

instance Monad CM where
   return a = CM (\k i -> k a i)
   CM f >>= g = 
     CM (\k i -> f (\a i' -> 
                      case g a of
                         CM h -> h k i') i)
   f >> m = f >>= (\ _ -> m)

-- time-dependent expressions:

type Re = Int -> Rexp
type Be = Int -> Bexp

rObserve :: Observable -> CM Re
rObserve s = CM (\k i -> k (\d -> rObs s (i-d)) i)

litRe :: Double -> Re
litRe d = \ i -> rLit d

litBe :: Bool -> Be
litBe True = \ i -> true
litBe False = \i -> false

-- JB are the next definitions used anywhere? Commenting them out for now.

-- this definition will need crafting another Num/Fractional instance
-- binRe :: BinOp -> Re -> Re -> Re
-- binRe bop re1 re2 = \ i -> rBin bop (re1 i) (re2 i)

-- pointwise extension of Num a to functions from Int. Maybe too
-- general, might make for some funny error messages to users...
instance Num a => Num (Int -> a) where
    (+) = liftM2 (+)
    (*) = liftM2 (*)
    (-) = liftM2 (-)
    negate = liftM2 (-) (const (fromInteger 0))
    abs a = undefined -- needs expression-if: if (a !<! 0) then (0 - a) else a
    signum a = undefined -- needs expression-if: if (a !=! 0) then 0 else if (a !<! 0) then -1 else 1
    fromInteger n = const (fromInteger n)

-- Reader monad liftM2: (a->a->a) -> (b->a) -> (b->a) -> (b->a)
-- liftM2 op f g = \b -> op (f b) (g b)

-- this will need explicit definitions for all Bool operators defined
-- binBe :: BoolOp -> Be -> Be -> Be
-- binBe bop be1 be2 = \ i -> bBin bop (be1 i) (be2 i)

notBe :: Be -> Be
notBe be = \ i -> bNot (be i)

negRe :: Re -> Re
negRe re = \ i -> negate (re i)

-- again, this will require explicit definitions for all operators defined
-- cmpRe :: Cmp -> Re -> Re -> Be
-- cmpRe cmp re1 re2 = \ i -> rCmp cmp (re1 i) (re2 i)

-- monad operations:

bObserve :: Observable -> CM Be
bObserve s = CM (\k i -> k (\d -> bObs s (i-d)) i)

transf :: Party -> Party -> Re -> Currency -> CM ()
transf a b m c = 
   CM (\k i -> both (scale (m i) (transfer a b c)) (k () i))

wait :: Int -> CM ()
wait t = CM (\k i -> translate t (k () (i+t)))

skip :: CM ()
skip = return ()

terminate :: CM ()
terminate = CM (\k i -> zero)

ifm :: Be -> CM a -> CM a -> CM a
ifm b (CM m1) (CM m2) = 
  CM (\k i -> ifWithin (b i) 0 (m1 k i) (m2 k i))

toContract :: CM () -> Contract
toContract (CM m) = m (\ _ _ -> zero) 0  
   
