{-# LANGUAGE RebindableSyntax #-}

module Examples where

import RebindableEDSL

-- Silly example to test the interaction of binders on contract and
-- expression level.

ex1 :: Contr
ex1 = letc 0 (\ b -> scale (acc (\r -> r + (acc (\r' -> b) 0 0)) 0 0) zero)
