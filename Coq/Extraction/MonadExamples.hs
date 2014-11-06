import ContractMonad
import SyntaxContract as SC

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

e = (\ i obs -> if i == 0 && obs == "Carlsberg" then Just 23.0
                else Nothing,
     choiceEnvEmpty)

c2' = SC.specialize c2 e

pp :: Maybe(Contract,Trans) -> String
pp Nothing = "Nothing"
pp (Just (c,t)) = "New Contract: " ++ show c ++ "\nTrans: " ++ show (t "ME" "YOU" "EUR")


advanceN :: Int -> Contract -> Contract
advanceN 0 c = c
advanceN n c =
  case SC.advance c SC.envEmpty of
      Just (c,t) -> advanceN (n-1) c;
      Nothing -> c

r = advanceN 6 c2
r2 = SC.specialize r SC.envEmpty

