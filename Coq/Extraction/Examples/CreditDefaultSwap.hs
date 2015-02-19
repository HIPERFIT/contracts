{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

import RebindableEDSL

-- Credit default swap parametrised by the maturity (in months), the
-- currency, the premium and the settlement as well as the buyer and
-- the seller of the CDS and the reference entity.

cds :: Int -> Asset -> Exp R -> Exp R -> Party -> Party -> Party -> Contr
cds months cur premium settle buyer seller ref = 
    payment months & settlement
    where payment i | i <= 0    = zero
                    | otherwise = (premium # transfer buyer seller cur) &  
                                  (30 ! payment (i-1))
          settlement = if bObs (Default ref) 0 `within` 30 * months
                       then settle # transfer seller buyer cur
                       else zero


-- A bond contract parametrised by the maturity (in months), the
-- currency, the interest and the nominal as well as the holder and
-- the issuer of the bond.

bond :: Int -> Asset -> Exp R -> Exp R -> Party -> Party -> Contr
bond months cur inter nom holder issuer = payment months
    where payment i | i <= 0     = nom # transfer issuer holder cur
                    | otherwise  = 
                        inter # transfer issuer holder cur &
                        if bObs (Default issuer) 0 `within` 30
                        then zero
                        else payment (i-1)


bondCDSExample :: Contr
bondCDSExample = bond 12 DKK 10 1000 X Y & cds 12 DKK 9 1000 Y Z X
