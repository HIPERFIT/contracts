module Contract.FXInstrument
    where

import Contract
import Contract.Expr

-- | ad-hoc convention for FX rate observables
fxRate :: Currency -> Currency -> String
fxRate c1 c2 = "FX " ++ show c1 ++ '/':show c2

fxForward :: Party -> Party       -- ^ buyer, seller
          -> (Currency, Currency) -- ^ FX currency pair
          -> RealE -> RealE       -- ^ amount, strike
          -> Int -> Contract      -- ^ days to maturity
fxForward buyer seller (buyCur, otherCur) amount strike 0
    = scale amount (allCs [ transfOne buyCur seller buyer
                          , scale strike (transfOne otherCur buyer seller)])
fxForward buyer seller (buyCur, otherCur) amount strike days
    = if days > 0 then
          transl days (fxForward buyer seller (buyCur,otherCur) amount strike 0)
      else error "fxForward into the past"

-- some tags for recurring alternatives
data OptionKind = Call | Put
data BarrierKind = Up | Down


-- vanilla options (explicit choice, not readily settled)
vanillaFx :: OptionKind -> Party -> Party
          -> (Currency, Currency)
          -> RealE -> RealE
          -> Int -> Contract
vanillaFx Call buyer seller (buyCur, otherCur) amount strike expiry
    = transl expiry
       (iff cond 
            (fxForward buyer seller (buyCur, otherCur) amount strike 0)
            zero)
      where cond = chosenBy (buyer ++ ":Call",0)
      --           strike !<! obs (rate,0)
      --    rate = fxRate buyCur otherCur
vanillaFx Put buyer seller (sellCur, otherCur) amount strike expiry
    = transl expiry
       (iff cond 
            (fxForward buyer seller (sellCur, otherCur) amount strike 0)
            zero)
      where cond = chosenBy (seller ++ ":Call",0)
      --           obs (rate,0) !<! strike
      --    rate = fxRate buyCur otherCur

-- | touch option: payment if a barrier is hit by an observable within a time
fxTouch :: Party -> Party -> Currency   -- ^ parties, settling currency
        -> RealE -> (Currency,Currency) -- ^ amount, FX cross
        -> RealE -> BarrierKind -> Int  -- ^ barrier, direction, expiry
        -> Contract
fxTouch buyer seller curSettle amount (cur1,cur2) barrier kind expiry
    = checkWithin cond expiry
                  (scale amount (transfOne curSettle buyer seller))
                  zero
      where cond = case kind of
                     Up   -> barrier !<! obs (rate,0)
                     Down -> obs (rate,0) !<! barrier
            rate = fxRate cur1 cur2

-- | no-touch option: payment if a barrier is _not_ breached
fxNoTouch :: Party -> Party -> Currency   -- ^ parties, settling currency
          -> RealE -> (Currency,Currency) -- ^ amount, FX cross
          -> RealE -> BarrierKind -> Int  -- ^ barrier, direction, expiry
          -> Contract
fxNoTouch buyer seller curSettle amount (cur1,cur2) barrier kind expiry
    = checkWithin cond expiry
                  zero
                  (scale amount (transfOne curSettle buyer seller))
      where rate = fxRate cur1 cur2
            cond = case kind of
                     Up   -> barrier !<! obs (rate,0)
                     Down -> obs (rate,0) !<! barrier
             {- -- when including == case:
                Up   -> not (obs (rate,0) !<! barrier)
                Down -> not (barrier !<! obs (rate,0) -}
            
-- ... not done yet: single/double barrier in/out contracts
