import SyntaxContract

option = translate 90 (iff (bObs "X" 0) trade zero)
trade  = scale 100 (both (transfer "Y" "X" "USD") pay)
pay    = scale rate (transfer "X" "Y" "DKK")
rate :: RExp
rate   = (acc (\r -> r + (rObs "FX USD/DKK" 0))  30 0) / 30
