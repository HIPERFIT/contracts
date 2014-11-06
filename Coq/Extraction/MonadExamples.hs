import ContractMonad
import SyntaxContract as SC

import Contract(adv_ext) -- hack

m = "ME"
y = "YOU"
eur = "EUR"

c1 = toContract
  (rObserve "Carlsberg" >>= \ a -> wait 5 >> transf m y a eur)

c2 = toContract
  (rObserve "Carlsberg" >>= \ a -> 
   wait 5 >>
   rObserve "Carlsberg" >>= \ b -> 
   transf m y a eur >>
   transf y m b eur)

e = (\ i obs -> if obs == "Carlsberg" then Just 23.0
                else Nothing,
     choiceEnvEmpty)

c2' = SC.specialize c2 e

pp :: Maybe(Contract,Trans) -> String
pp Nothing = "Nothing"
pp (Just (c,t)) = "New Contract: " ++ show c ++ "\nTrans: " ++ show (t "ME" "YOU" "EUR")


advanceN :: Int -> Env -> Contract -> Maybe Contract
advanceN 0 e c = Just c
advanceN n e c =
  case SC.advance c e of
      Just (c,t) -> advanceN (n-1) (adv_ext 1 e) c;
      Nothing -> Nothing

r  = advanceN 5 e c2
r' = advanceN 6 e c2 -- Nothing?


-- r2 = SC.specialize r SC.envEmpty

