import EDSL

option :: Contr
option = translate 90 (iff (bObs "X" 0) trade zero)
    where trade  = scale 100 (both (transfer "Y" "X" "USD") pay)
          pay    = scale rate (transfer "X" "Y" "DKK")
          rate   = (acc (\r -> r + (rObs "FX USD/DKK" 0))  30 0) / 30
