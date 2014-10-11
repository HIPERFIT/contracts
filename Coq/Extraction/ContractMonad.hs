
import SyntaxContract

data CM a = CM ((a->Int->Contract)->Int->Contract)
instance Monad CM where
   return a = CM (\k i -> k a i)
   CM f >>= g = 
     CM (\k i -> f (\a i' -> 
                      case g a of
                         CM h -> h k i') i)
   f >> m = f >>= (\ _ -> m)

rObserve :: Observable -> CM Rexp
rObserve s = CM (\k i -> k (rObs s i) i)
bObserve :: Observable -> CM Bexp
bObserve s = CM (\k i -> k (bObs s i) i)

transf :: Party -> Party -> Currency -> CM ()
transf a b c = 
   CM (\k i -> both (transfer a b c) (k () i))

wait :: Int -> CM ()
wait t = CM (\k i -> translate t (k () i))

skip :: CM ()
skip = return ()

terminate :: CM ()
terminate = CM (\k i -> zero)

ifm :: Bexp -> CM a -> CM a -> CM a
ifm b (CM m1) (CM m2) = 
  CM (\k i -> ifWithin b 0 (m1 k i) (m2 k i))

toContract :: CM () -> Contract
toContract (CM m) = m (\k i -> zero) 0  

