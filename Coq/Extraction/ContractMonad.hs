module ContractMonad where

import SyntaxContract

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

type Re = Int -> Rexp
type Be = Int -> Bexp

rObserve :: Observable -> CM Re
rObserve s = CM (\k i -> k (\d -> rObs s (i-d)) i)

litRe :: Double -> Re
litRe d = \ i -> rLit d

litBe :: Bool -> Be
litBe b = \ i -> bLit b

binRe :: BinOp -> Re -> Re -> Re
binRe bop re1 re2 = \ i -> rBin bop (re1 i) (re2 i)

binBe :: BoolOp -> Be -> Be -> Be
binBe bop be1 be2 = \ i -> bBin bop (be1 i) (be2 i)

notBe :: Be -> Be
notBe be = \ i -> bNot (be i)

negRe :: Re -> Re
negRe re = \ i -> rNeg (re i)

cmpRe :: Cmp -> Re -> Re -> Be
cmpRe cmp re1 re2 = \ i -> rCmp cmp (re1 i) (re2 i)

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

toContract :: CM () -> Contract
toContract (CM m) = m (\ _ _ -> zero) 0  
   
ifm :: Be -> CM a -> CM a -> CM a
ifm b (CM m1) (CM m2) = 
  CM (\k i -> ifWithin (b i) 0 (m1 k i) (m2 k i))

