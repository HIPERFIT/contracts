
import SyntaxContract

data CM a = CM ((a -> Int -> Contract) -> Int -> Contract)
instance Monad CM where
   return a = CM (\k i -> k a i)
   CM f >>= g = 
     CM (\k i -> f (\a i' -> 
                      case g a of
                         CM h -> h k i') i)
   f >> m = f >>= (\ _ -> m)

observe :: Observable -> CM Rexp
observe s = CM (\k i -> k (obs(s,i)) i)
transf :: (Party,Party,Currency) -> CM ()
transf a = CM (\k i -> both(transfOne a, k () i))
wait :: Int -> CM ()
wait t = CM (\k i -> translate(t, k () i))
skip :: CM ()
skip = return ()
terminate :: () -> CM ()
terminate () = CM (\k i -> zero)
toContr :: CM Contract -> Contract
toContr (CM m) = m (\ _ _ -> zero) 0  
   
