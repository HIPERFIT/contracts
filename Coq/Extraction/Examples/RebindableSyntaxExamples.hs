{-# LANGUAGE RebindableSyntax #-}

module RebindableSyntaxExamples where

import RebindableEDSL

ex1 :: Contr
ex1 = do b <- rObs (FX DKK USD) 0 > 5 && bObs (Decision X "foo") 0
         wait 4
         if b `within` 10 then zero else
             acc (\r -> r + (acc (\r' -> if not b then r else r') 0 0)) 1 10 # transfer X Y USD

env = mkExtEnvP [][(Decision X "foo",0,True)] 

spec1 :: Contr
spec1 = specialise ex1 env
