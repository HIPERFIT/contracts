structure portfolio = struct

local open Currency Instruments
in

(* single barrier options: directly taken from table *)

val singleBarriers =
    [ fxSingleBarrierOut "us" "A" (USD,SEK) Call Down 10E6 6.60 6.25 180 (* 6 months *)
    , fxSingleBarrierOut "A" "us" (USD,SEK) Call Down 15E6 6.40 6.25 180 (* 6 months *)
    , fxSingleBarrierIn  "B" "us" (USD,SEK) Put  Up   50E6 6.40 6.80 360 (* 1 year *)
    , fxSingleBarrierOut "C" "us" (USD,SEK) Call Down  5E6 6.30 6.70 360 (* 1 year *)
    , fxSingleBarrierIn  "D" "us" (USD,SEK) Put  Down 50E6 6.70 6.20 360 (* 1 year *)
    ]

val doubleBarriers =
    [ fxDoubleBarrierIn  "A" "us" (USD,SEK) Call  5E6 6.60 (6.20,6.80) 90 (* 3 months *)
    , fxDoubleBarrierOut "B" "us" (USD,SEK) Call 10E6 6.40 (6.20,6.80) 90
    , fxDoubleBarrierOut "B" "us" (USD,SEK) Put   8E6 6.50 (6.20,6.80) 90
    , fxDoubleBarrierIn  "D" "us" (USD,SEK) Put  40E6 6.30 (6.10,6.70) 360 (* 1 year *)
    ]
    
(* Asian options: not yet handled (needs observable average computation) *)

val touchOptions =
    [ fxBarrierTouch   "C" "us" USD (0.04 * 10E6) (USD,SEK) 6.90 Up   180 (* 6 months *)
    , fxBarrierTouch   "D" "us" USD (0.03 * 20E6) (USD,SEK) 6.15 Down 360 (* 12 months*) 
    , fxBarrierNoTouch "A" "us" USD (0.07 * 20E6) (USD,SEK) 6.70 Up   180 (* 6 months*) 
    , fxBarrierNoTouch "B" "us" USD (0.08 * 20E6) (USD,SEK) 6.25 Down 360 (* 12 months*) 
    ]

val vanillas =
    [ vanillaFx Call "us" "F" (USD,SEK) 10E6 6.60 90  (* 3 months *)
    , vanillaFx Put  "us" "F" (USD,SEK) 10E6 6.30 180 (* 6 months *)
    , vanillaFx Put  "F" "us" (USD,SEK) 10E6 6.30 360 (* 12 months *)
    , vanillaFx Put  "us" "F" (USD,SEK) 10E6 6.30 720 (* 24 months *)
    ]

val forwards = 
    [ fxForward "us" "G" (USD,SEK) 60E6 6.55 180 (* 6 months *)
    ]

(* everything together (using "all" constructor) is the portfolio *)
val fxPortfolio = Contract.all (singleBarriers @ doubleBarriers @
                                touchOptions @ vanillas @ forwards)

end

end
