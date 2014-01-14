structure Instruments = struct

exception Error of string

local open Currency Contract in

infix !+! !-! !*! !<! !=! !|! 

fun fxRate c1 c2 = "FX " ^ ppCur c1   (* an ad hoc conven- *)
                   ^ "/" ^ ppCur c2   (* tion for rates    *)

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), date of transaction 
   (string,currency) -> (string,currency) 
   -> real -> real -> days -> Contract.t
*) 
fun fxForward buyer seller (buyCurr, otherCurr) amount strike 0 =
            scale (R amount, 
                   all [ transfOne (buyCurr, seller, buyer)
                        , scale ((R strike),
                                 transfOne (otherCurr, buyer, seller))]
                  )
  | fxForward buyer seller (buyCurr, otherCurr) amount strike days =
    if days > 0 then 
        transl (days, fxForward buyer seller (buyCurr, otherCurr) amount strike 0)
    else raise Error "fxForward into the past"


(* all following split into put and call, so we use a tag type *)
datatype OptionKind = Call | Put

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), expiry (days)
   OptionKind -> (string,currency) -> (string,currency) 
   -> real -> real -> int -> days -> Contract.t
*) 
fun vanillaFx Call 
        buyer seller (buyCurr,otherCurr) amount strike expiry =
    let val rate    = fxRate buyCurr otherCurr
        val cond    = chosenBy (buyer ^ ":Call-option",0)
                      (* R strike !<! obs (rate, 0) *)
                      (* option taken depending on price > strike *)
                      (* offset "0", Transl supposed to move obs date offset!*)
    in transl (expiry,iff (cond, fxForward buyer seller
                                           (buyCurr, otherCurr)
                                           amount strike 0    , zero))
    end
  | vanillaFx Put
        seller buyer (sellCurr,otherCurr) amount strike expiry =
    let val rate    = fxRate sellCurr otherCurr
        val cond    = chosenBy (seller ^ ":Put-option",0)
                      (* obs (rate, 0) !<! R strike *)
                      (* option taken depending on price < strike *)
                      (* assumes transl moves obs date offset (see previous) *)
    in transl (expiry,iff (cond, fxForward buyer seller
                                             (sellCurr, otherCurr)
                                             amount strike 0    , zero))
    end

(* Single-Barrier *-touch options (up or down) require "continuous", i.e.
   daily fixings. 
   Notional value unnecessary, only the fixed coupon of it is used.
   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry

   Note that this code also triggers the option when the price fixes
   exactly _at_ (not above/below) the given barrier, which is what the
   word "touch" suggests.
*)
datatype BarrierKind = Up | Down

(* First version (BAD) uses recursion in SML, unrolling the entire contract period! *)
fun fxBarrierTouchBAD
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = fxRate cur1 cur2
        val cond = case kind of 
                           Up   => not (obs (rate, 0) !<! R barrier)
                         | Down => not (R barrier !<! obs (rate, 0))
                      (* next steps depend on whether barrier hit today *)
                      (* note that Transl below leads to checking every day *)
        fun fxTLoop day = 
            transl (day, 
                    iff (cond,
                        scale (R amount, transfOne (curSettle, buyer, seller)),
                        if day < expiry then fxTLoop (day + 1)
                        else zero (* base case, immediate expiry *)))
    in fxTLoop 0
    end

(* using a tailored loop construct "CheckWithin", much better: no big
   unrolled data structure. Evaluation needs to realise its semantics.
   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry
*)
fun fxBarrierTouch
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = fxRate cur1 cur2
        val cond = case kind of
                       Up   => not (obs (rate, 0) !<! R barrier)
                     | Down => not (R barrier !<! obs (rate, 0))
                      (* next steps depend on whether barrier hit today *)
    in checkWithin (cond, expiry,
                    scale (R amount, transfOne (curSettle, buyer, seller)),
                    zero) (* if barrier hit: payment. Otherwise: zero *)
    end

(* NO-touch options: pay out if barrier NOT breached, just swapping
   the branches from before (exit to zero when touched, pay otherwise).

   Could also again unroll the period in a SML-level recursion.

   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry
*)
fun fxBarrierNoTouchBAD
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = fxRate cur1 cur2
        val cond = case kind of (* same code as above, but condition swapped *)
                       Up   => not (R barrier !<! obs (rate, 0))
                     | Down => not (obs (rate, 0) !<! R barrier)
        fun fxTLoop day = 
            transl (day,
                    iff (cond, 
                        scale (R amount, transfOne (curSettle, buyer, seller)),
                        if day < expiry then fxTLoop (day + 1)
                        else zero (* base case, immediate expiry *)))
    in fxTLoop 0
    end

fun fxBarrierNoTouch
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = fxRate cur1 cur2
        val cond = case kind of
                       Up   => not (obs (rate, 0) !<! R barrier)
                     | Down => not (R barrier !<! obs (rate, 0))
                      (* intention: exit when barrier hit today *)
    in checkWithin (cond, expiry,
                    zero, (* if barrier hit: zero, otherwise: payment *)
                    scale (R amount, transfOne (curSettle, buyer, seller)))
    end

(* Double barrier option: we need a boolean "or" (added), then just as
   easy as the single barrier.
   option buyer, option seller, (curr1,curr2) 
       OptionKind(Call/Put) amount strike (lo-barrier, hi-barrier) expiry
*)
fun fxDoubleBarrierIn 
    buyer seller (cur1,cur2) kind amount strike (loBarr,hiBarr) expiry
  = let val rate = fxRate cur1 cur2
        val cond = (obs (rate,0) !<! R loBarr)
                   !|! (R hiBarr !<! obs (rate,0))
                    (* "in" if price below lower || above upper *)
    in checkWithin (cond, expiry,
                    vanillaFx kind buyer seller (cur1,cur2)
                              amount strike expiry,
                    zero) (* if barrier hit: option; otherwise zero *)
    end

fun fxDoubleBarrierOut
    buyer seller (cur1,cur2) kind amount strike (loBarr,hiBarr) expiry
  = let val rate = fxRate cur1 cur2
        val cond = (obs (rate,0) !<! R loBarr)
                   !|! (R hiBarr !<! obs (rate,0))
                    (* "out" if price below lower || above upper *)
    in checkWithin (cond, expiry,
                    zero,  (* if barrier hit: zero, otherwise option *)
                    vanillaFx kind buyer seller (cur1,cur2)
                              amount strike expiry)
    end

(* Single barrier: needs a barrierKind (Up/Down), but only one barrier value
   Arg.s:
   option buyer, option seller, (curr1,curr2) 
       OptionKind(Call/Put) BarrierKind(Up/Down) amount strike barrier expiry
 *)
fun fxSingleBarrierIn
    buyer seller (cur1,cur2) optKind barrKind amount strike barr expiry
  = let val rate = fxRate cur1 cur2
        val cond = case barrKind of  
                       Up   => R barr !<! obs (rate,0) (* Up: price higher  *)
                     | Down => obs (rate,0) !<! R barr (* Down: price lower *)
    in checkWithin (cond, expiry,
                    vanillaFx optKind buyer seller (cur1,cur2)
                              amount strike expiry,
                    zero) (* if barrier hit: option, otherwise zero *)
    end

fun fxSingleBarrierOut
    buyer seller (cur1,cur2) optKind barrKind amount strike barr expiry
  = let val rate = fxRate cur1 cur2
        val cond = case barrKind of  
                       Up   => R barr !<! obs (rate,0) (* Up: price higher  *)
                     | Down => obs (rate,0) !<! R barr (* Down: price lower *)
    in checkWithin (cond, expiry,
                    zero, (* if barrier hit: zero, otherwise option *)
                    vanillaFx optKind buyer seller (cur1,cur2)
                              amount strike expiry)
    end

end

end
