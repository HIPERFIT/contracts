{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

module CDSSimple where

-- Simple credit default swap for a zero coupon bond.

import RebindableEDSL

-- Credit default swap parametrised by the maturity (in days), the
-- currency, the premium and the settlement as well as the buyer and
-- the seller of the CDS and the reference entity.

cds :: Int -> Asset -> Exp R -> Exp R -> Party -> Party -> Party -> Contr
cds maturity cur premium settle buyer seller ref = 
    payment & settlement
    where payment = premium # transfer buyer seller cur
          settlement = if bObs (Default ref) 0 `within` maturity
                       then settle # transfer seller buyer cur
                       else zero

-- zero coupon bond

bond :: Int -> Asset -> Exp R -> Party -> Party -> Contr
bond maturity cur nom holder issuer = if bObs (Default issuer) 0 `within` maturity
                                      then zero 
                                      else nom # transfer issuer holder cur



bondCDSExample :: Contr
bondCDSExample = bond 30 DKK 1000 Y X & cds 30 DKK 10 900 Y Z X

env1 = mkExtEnvP [] [(Default X,n,False) | n <- [0..30]]
env2 = mkExtEnvP [] [(Default X,n,n==15) | n <- [0..30]]

spec1 :: Contr
spec1 = specialise bondCDSExample env1

spec2 :: Contr
spec2 = specialise bondCDSExample env2
