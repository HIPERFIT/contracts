{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

import RebindableEDSL

-- Credit default swap parametrised by the maturity (in months), the
-- currency, the premium and the settlement as well as the buyer and
-- the seller of the CDS and the reference entity.

cds :: Int -> Asset -> Exp R -> Exp R -> Party -> Party -> Party -> Contr
cds months cur premium comp buyer seller ref = 
    step months
    where step i = if (i <= 0) then zero else
                      (premium # transfer buyer seller cur) &  
                      if bObs (Default ref) 0 `within` 30 * months
                      then comp # transfer seller buyer cur
                      else 30 ! step (i-1)


-- A bond contract parametrised by the maturity (in months), the
-- currency, the interest and the nominal as well as the holder and
-- the issuer of the bond.

bond :: Int -> Asset -> Exp R -> Exp R -> Party -> Party -> Contr
bond months cur inter nom holder issuer = step months
    where step i = if i <= 0 then nom # transfer issuer holder cur
          else inter # transfer issuer holder cur &
               if bObs (Default issuer) 0 `within` 30
               then zero
               else step (i-1)


bondCDSExample :: Contr
bondCDSExample = bond 12 DKK 10 1000 X Y & cds 12 DKK 9 1000 Y Z X 
