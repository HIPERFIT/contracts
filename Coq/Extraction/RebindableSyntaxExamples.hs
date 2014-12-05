{-# LANGUAGE RebindableSyntax #-}

import RebindableSyntaxContract

ex1 :: Contr
ex1 = do b <- rObs "DKK/USD" 0 > 5 && bObs "foo" 0
         wait 4
         if b then zero else
             scale (acc (\r -> r + (acc (\r' -> if b then r else r') 0 0)) 0 0) zero
