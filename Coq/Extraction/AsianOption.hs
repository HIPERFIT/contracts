import SyntaxContract

iff be c1 c2 = ifWithin be 0 c1 c2

option = translate 90 (iff (bObs "X" 0) trade zero)
trade  = scale (rLit 100) (both (transfer "Y" "X" "USD") pay)
pay    = scale rate (transfer "X" "Y" "DKK")
rate   = rBin Div (rAcc (\r -> rBin Add r (rObs "FX USD/DKK" 0)) 
                        30 (rLit 0)
                  )
                  (rLit 30) 
