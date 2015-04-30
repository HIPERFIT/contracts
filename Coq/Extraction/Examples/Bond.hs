{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

module Bond where

import RebindableEDSL

-- bond

-- A bond contract parametrised by the maturity (in months), the
-- currency, the interest and the nominal as well as the holder and
-- the issuer of the bond.

bond :: Int -> Asset -> Exp R -> Exp R -> Party -> Party -> Contr
bond months cur inter nom holder issuer = payment months
    where payment :: Int -> Contr
          payment i | i < 1     = nom # transfer issuer holder cur
                    | otherwise = (inter # transfer issuer holder cur) &  
                                  (30 ! payment (i-1))


exampleBond :: Contr
exampleBond = bond 12 DKK 10 1000 X Y
