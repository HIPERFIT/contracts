local
  open portfolio ContractTransform Contract
in 

(* compact function for computing and printing all cashflows
   startdate is the start date of the contract.
 *)
fun ppCs startdate contract = 
    print (ppCashflows (cashflows (startdate, contract)) ^ "\n")

val today = DateUtil.?"2014-01-01"

(* simple test for addFixings *)

val env = addFixings ("FX USD/SEK",today) 
                     [6.6,6.7,6.8,6.9,6.8,6.7,6.6,6.5,6.4,6.3,6.2,6.1]
                     (emptyFrom today)
          (* all touchOptions will be triggered, max 6.9, min 6.1 *)
val allTouch = all touchOptions

val allTouch' = simplify (env,today) allTouch

val () = (ppCs today allTouch; print "\n\n"; ppCs today allTouch')

(* 
val () = ppCs today fxPortfolio
*)

(* this file should be extended to showcase advancing, fixings, normalisation *)

end

