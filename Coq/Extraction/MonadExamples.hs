import ContractMonad
import SyntaxContract as SC

import Contract(adv_ext) -- hack

m = "ME"
y = "YOU"
eur = "EUR"

c1 :: Contr
c1 = toContract
  (rObserve "Carlsberg" >>= \ a -> wait 5 >> transf m y a eur)

c2 = toContract
  (rObserve "Carlsberg" >>= \ a -> 
   wait 5 >>
   rObserve "Carlsberg" >>= \ b -> 
   transf m y a eur >>
   transf y m b eur)


e = (\ obs i -> if obs == LabR "Carlsberg" then Just 23.0
                else Nothing)

-- c2' = SC.specialize c2 e

pp :: Maybe(Contr,Trans) -> String
pp Nothing = "Nothing"
pp (Just (c,t)) = "New Contract: " ++ show c ++ "\nTrans: " ++ show (t "ME" "YOU" "EUR")


advanceN :: Int -> ExtEnv -> Contr -> Maybe Contr
advanceN 0 e c = Just c
advanceN n e c =
  case SC.advance c e of
      Just (c,t) -> advanceN (n-1) (adv_ext 1 e) c;
      Nothing -> Nothing

r  = advanceN 5 e c2
r' = advanceN 6 e c2 -- Nothing?


-- r2 = SC.specialize r SC.envEmpty

