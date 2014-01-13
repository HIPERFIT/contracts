local
  open portfolio ContractTransform Contract
in 

(* compact function for computing and printing all cashflows
   startdate is the start date of the contract.
 *)
fun ppCs startdate contract = 
    print (ppCashflows (cashflows (startdate, contract)) ^ "\n")

val today = DateUtil.?"2014-01-01"

val () = ppCs today fxPortfolio

(* this file should be extended to showcase advancing, fixings, normalisation *)

end

