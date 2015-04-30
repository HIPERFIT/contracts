{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

module KnockoutOption where

import RebindableEDSL

-- knock-out barrier option
--

knockout :: Exp R -> Exp R -> Exp R -> Int -> Contr
knockout barrier strike notional maturity = 
    if rObs (FX EUR DKK) 0 <= barrier `within` maturity
    then zero
    else if bObs (Decision X "exercise") 0
         then notional # (transfer Y X EUR & 
              (strike # transfer X Y DKK))
         else zero
