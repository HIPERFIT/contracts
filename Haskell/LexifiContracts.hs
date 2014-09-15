-- contracts from Lexifi, used with the generic pricing engine

module LexifiContracts
    where

-- MEMO: clean up imports and exports of umbrella file "Contract.hs"
import Contract
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
          minRatio = foldl1 minn 
                            (zipWith (\id sp -> obs(id,0) / sp) idxs spots)
          allAbove d = nott (foldl1 (!|!) 
                             (zipWith (fractionSmaller d) idxs spots))
           {- 0.75 < minimum [ obs(id,0) / sp | (id, sp) <- zip idxs spots ]
                               <==> 
              and [ 0.75 * sp !<! obs (id, 0) | (id, sp) <- zip idxs spots ]
                               <==> 
            not (or [obs(id, 0) !<! 0.75 * sp | (id, sp) <- zip idxs spots]) -}
          fractionSmaller d idx spot = obs(idx, 0) !<! d * spot
          collectEUR amount = scale amount (transfOne EUR "them" "us")

-- barrier of 0.7*start on 3 indexes, monitored over 367 days from
-- start payment scaled (by fraction, cannot implement it now) if any
-- barrier breached and at least one end index lower than at start
barrierRevConvert :: MContract
barrierRevConvert = (start,
                     both (transl 367 (collectEUR 100))
                          (iff breached
                           (transl 367 
                            (iff (oneBelow 1) (collectEUR minRatio) (collectEUR 1000)))
                           zero))
    where start = at "2012-01-27"
          idxs   = [ "DJ_Eurostoxx_50", "Nikkei_225", "SP_500" ]
          spots  = [ 3758.05, 11840, 1200 ]
          oneBelow d = foldl1 (!|!) (zipWith (fractionSmaller d) idxs spots)
          fractionSmaller d idx spot = obs(idx, 0) !<! d * spot
          minRatio = foldl1 minn 
                            (zipWith (\id sp -> obs(id,0) / sp) idxs spots)
          -- barrier check is accumulated (MEMO: does !|! shortcut evaluation?)
          breached = acc (\x -> x !|! oneBelow 0.7) 366 (oneBelow 0.7)
                                                   -- now till day 367
          collectEUR amount = scale amount (transfOne EUR "them" "us")
          -- same indexes, spot prices, helpers as in contract above

