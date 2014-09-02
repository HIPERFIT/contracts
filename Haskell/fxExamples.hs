
import Contract
import Contract.FXInstrument
import Contract.Transform
import Contract.Analysis

today = at "2014-09-02"

halfY = oneY `div` 2
oneY  = 365

-- 
touchOptions 
    = (today, 
       allCs [ fxTouch   "C" "us" USD   40000 (USD,SEK) 6.90 Up   halfY
             , fxTouch   "D" "us" USD   60000 (USD,SEK) 6.15 Down oneY
             , fxNoTouch "A" "us" USD  140000 (USD,SEK) 6.70 Up   halfY
             , fxNoTouch "B" "us" USD  160000 (USD,SEK) 6.25 Down oneY
             ])

-- One touch option will be triggered (barrier up 6.9).
-- Two no-touch options will be canceled (barriers up 6.7, down 6.25).
env = fixings "FX USD/SEK" today
      [6.6, 6.7, 6.8, 6.9, 6.8, 6.7, 6.6, 6.5, 6.4, 6.3, 6.2, 6.1]

allTouch' = simplify env touchOptions

run =  (putStrLn . ppCashflows . cashflows) allTouch'

{-
*Main> run
2014-09-05 Certain [C->us] USD 40000.0000
2014-09-13 Certain [D->us] USD 60000.0000

-}

trs = (putStrLn . ppTriggers . branchBounds) touchOptions
