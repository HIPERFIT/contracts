{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

module ChooserOption where

import RebindableEDSL

strike :: Exp R
strike = 6.5

contract :: Contr
contract = do price <- rObs (FX DKK USD) 60
              payout <- ife (bObs (Decision X "call option") 30)
                         (max (price - strike) 0)
                         (max (strike - price) 0)
              60 ! (payout # transfer Y X DKK)
