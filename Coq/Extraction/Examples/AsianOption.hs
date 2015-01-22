{-# LANGUAGE RebindableSyntax #-}

import RebindableEDSL

option :: Contr
option = 90 ! if bObs "X" 0 
              then 100 # (transfer "Y" "X" "USD" & 
                          (rate # transfer "X" "Y" "DKK"))
              else zero
    where rate   = (acc (\r -> r + rObs "FX USD/DKK" 0)  30 0) / 30

american :: Contr
american = if bObs "X" 0 `within` 90 
           then 100 # (transfer "Y" "X" "USD" & 
                       (6.23 # transfer "X" "Y" "DKK"))
           else zero
