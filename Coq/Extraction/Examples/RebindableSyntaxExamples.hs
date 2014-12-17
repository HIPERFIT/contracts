{-# LANGUAGE RebindableSyntax #-}

import RebindableEDSL

ex1 :: Contr
ex1 = do b <- rObs "DKK/USD" 0 > 5 && bObs "foo" 0
         wait 4
         if b `within` 10 then zero else
             acc (\r -> r + (acc (\r' -> if not b then r else r') 0 0)) 1 10 # transfer "A" "B" "C"

env = mkExtEnvP [][("foo",0,True)] 

spec1 = specialise (reifyContr ex1) env
