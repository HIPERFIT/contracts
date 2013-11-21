structure ContractUtil = struct

open multicontracts
open Contract

(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), date of transaction 
   (string,currency) -> (string,currency) 
   -> real -> real -> Date.date -> Contract.t
*) 

fun fxForward(buyer,buyCurr) (seller, otherCurr) amount strike date =
        Scale ((Obs.Const amount),
               All [ TransfOne (date,buyCurr, seller, buyer)
                   , Scale ((Obs.Const strike),
                            TransfOne (date, otherCurr, buyer, seller))]
              )


(* buyer and seller with the currencies they receive,
   notional amount, strike (sell/buy), expiry (days), start date (today?) 
   (string,currency) -> (string,currency) 
   -> real -> real -> int -> Date.date -> Contract.t
*) 
fun vanillaFxCall 
        (buyer,buyCurr) (seller, otherCurr) amount strike expiry date =
    let val rate    = "FX " ^ pp_cur buyCurr ^ "/" ^ pp_cur otherCurr
                      (* an ad hoc convention to specify rates... *)
        val expDate = addDays expiry date
    in Transl (expiry, (* option taken depending on price > strike *) 
               If (fn p => p > strike, Obs.Underlying (rate,expDate),
                   fxForward (buyer, buyCurr) (seller, otherCurr) 
                             amount strike expDate))
    end
end
