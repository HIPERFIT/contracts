{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

module DualBarrier where

import RebindableEDSL

-- dual barrier knock-out FX option
--
-- If either of the two barriers is hit within the maturity, the
-- contract is cancelled otherwise party X may exercise the FX option
-- at maturity with the given strike.

dualBarrier :: Exp R -> Exp R -> Exp R -> Exp R -> Int -> Contr
dualBarrier lower upper strike notional maturity = 
    if rObs (FX EUR DKK) 0 <= lower || rObs (FX CHF DKK) 0 >= upper `within` maturity
    then zero
    else if bObs (Decision X "exercise") 0
         then notional # (transfer Y X USD & 
              (strike # transfer X Y DKK))
         else zero


ex :: Contr
ex = dualBarrier 1 2 3 4 10
