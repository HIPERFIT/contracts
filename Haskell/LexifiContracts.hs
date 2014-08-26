
-- contracts from Lexifi, used with the generic pricing engine

module LexifiContracts
    where

-- MEMO: clean up imports and exports of umbrella file "Contract.hs"
import Contract
import Contract.Type
import Contract.Date
import Contract.Expr

-- European option on DJ_Eurostoxx_50, starting 
european :: MContract
european = (start, -- 2011-12-09
            transl duration -- on 2012-11-30
                (scale (maxx 0 (obs (idx,0) - strike))
                        (transfOne EUR "them" "us")))
            where start    = at "2011-12-09" :: Date
                  duration = dateDiff start (at "2012-11-30")
                             -- MEMO this fct. should be called "daysBetween"
                  idx      = "DJ_Eurostoxx_50"
                  strike   = 4000

-- worst-off contract on five fixed dates (chain of iff)
worstOff :: MContract
worstOff = (start, foldr mkDateCheck endCase (zip dDiffs premiums))
    where start  = at "2012-01-27"
          dates  = map (\s -> at (show s ++ "-01-27")) [2013..2017]
          dDiffs   = zipWith dateDiff (start:dates) dates
          premiums = [1150.0, 1300.0, 1450.0, 1600.0, 1750]
          -- on the five dates (offset): one below initial spot => pay premium
          mkDateCheck (offset, premium) cont
              = transl offset $ iff barrier (collectEUR premium) cont
          barrier = nott (foldl1 minn (zipWith mkDiff idxs spots) !<! 0)
          -- MEMO we should have <= , > and >= as smart constructors
          mkDiff idx spot = obs (idx, 0) - spot
           -- MEMO we should have RealE division.
          idxs   = [ "DJ_Eurostoxx_50", "Nikkei_225", "SP_500" ]
          spots  = [ 3758.05, 11840, 1200 ]
          -- if end (date 5) reached: pay 1000 if all above 0.75,
          -- otherwise pay the fraction of the worst (HOW? no division)
          endCase = iff (allAbove 0.75) (collectEUR 1000) 
                        (collectEUR (1000 * minRatio))
          minRatio = error "cannot define minimum ratio without division"
          allAbove d = nott (foldl1 (!|!) 
                             (zipWith (fractionSmaller d) idxs spots))
           {- 0.75 < minimum [ obs(id,0) / sp | (id, sp) <- zip idxs spots ]
                               <==> 
              and [ 0.75 * sp !<! obs (id, 0) | (id, sp) <- zip idxs spots ]
                               <==> 
            not (or [obs(id, 0) !<! 0.75 * sp | (id, sp) <- zip idxs spots]) -}
          fractionSmaller d idx spot = obs(idx, 0) !<! d * spot
          collectEUR amount = scale amount (transfOne EUR "them" "us")

--
