structure ContractUtil = struct

exception Error of string

open ContractTypes
open Expr

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), date of transaction 
   (string,currency) -> (string,currency) 
   -> real -> real -> days -> Contract.t
*) 
fun fxForward (buyer,buyCurr) (seller, otherCurr) amount strike 0 =
            Scale (R amount, 
                   All [ TransfOne (buyCurr, seller, buyer)
                        , Scale ((R strike),
                                 TransfOne (otherCurr, buyer, seller))]
                  )
  | fxForward (buyer,buyCurr) (seller, otherCurr) amount strike days =
    if days > 0 then 
        Transl (I days, 
                fxForward (buyer, buyCurr) (seller, otherCurr) amount strike 0)
    else raise Error "fxForward into the past"

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), expiry (days), start date (today?) 
   (string,currency) -> (string,currency) 
   -> real -> real -> int -> days -> Contract.t
*) 
fun vanillaFxCall 
        (buyer,buyCurr) (seller, otherCurr) amount strike expiry =
    let val rate    = "FX " ^ Currency.pp_cur buyCurr   (* an ad hoc conven- *)
                      ^ "/" ^ Currency.pp_cur otherCurr (* tion for rates    *)
        val cond    =  Expr.!<! (obs (rate,expiry), R strike)
                      (* option taken depending on price > strike *)
                      (* XXX this assumes Transl does _not_ modify obs *)
    in Transl (I expiry,If (cond, fxForward (buyer, buyCurr) 
                                            (seller, otherCurr) 
                                            amount strike 0    , All []))
    end

fun vanillaFxPut
        (seller, sellCurr) (buyer,otherCurr) amount strike expiry =
    let val rate    = "FX " ^ Currency.pp_cur sellCurr   (* an ad hoc conven- *)
                      ^ "/" ^ Currency.pp_cur otherCurr (* tion for rates    *)
        val cond    =  Expr.!<! (R strike, obs (rate,expiry))
                      (* option taken depending on price < strike *)
                      (* XXX this assumes Transl does _not_ modify obs *)
    in Transl (I expiry,If (cond, fxForward (buyer, sellCurr)
                                            (seller, otherCurr)
                                            amount strike 0    , All []))
    end

(* Single-Barrier *-touch options (up or down) require "continuous", i.e.
   daily fixings. 
   Notional value unnecessary, only the fixed coupon of it is used.
   buyer, seller, settling currency, amount, FX cross, barrier, up/down, expiry
*)
datatype TouchKind = Up | Down

(* First version (BAD) uses recursion in SML, unrolling the entire contract period! *)
fun fxBarrierTouchBAD
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = "FX " ^ Currency.pp_cur cur1
                   ^ "/" ^ Currency.pp_cur cur2
        val cond = case kind of 
                       Up   => Expr.!<! (R barrier, obs (rate,0))
                     | Down => Expr.!<! (obs (rate,0), R barrier)
                      (* next steps depend on whether barrier hit today *)
        fun fxTLoop days = 
            If (cond, Scale (R amount, TransfOne (curSettle, buyer, seller)),
                if days > 0 then fxTLoop (days - 1)
                else All [] (* base case, immediate expiry *))
    in fxTLoop expiry
    end

fun fxBarrierTouch
    buyer seller curSettle amount (cur1,cur2) barrier kind expiry
  = let val rate = "FX " ^ Currency.pp_cur cur1
                   ^ "/" ^ Currency.pp_cur cur2
        val cond = case kind of
                       Up   => Expr.!<! (R barrier, obs (rate,0))
                     | Down => Expr.!<! (obs (rate,0), R barrier)
                      (* next steps depend on whether barrier hit today *)
    in CheckWithin (cond, I expiry,
                    Scale (R amount, TransfOne (curSettle, buyer, seller)))
    end
end
