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

end
