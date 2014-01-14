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
                     [6.6,6.7,6.8,6.91,6.8,6.7,6.6,6.5,6.4,6.3,6.2,6.1]
                     (emptyFrom today)
   (* two touchOptions will be triggered (barriers up 6.9, down 6.15)
      two noTouchOptions will be canceled (barriers up 6.7, down 6.25) *)
val allTouch = all touchOptions
val allTouch' = simplify (env,today) allTouch

val () = (ppCs today allTouch;
          print "------------------\n and with fixings:\n";
          ppCs today allTouch';
          print ("Contract was: \n" ^ ppContr allTouch ^ "\n");
          print ("Simplified contract is:\n" ^ ppContr allTouch' ^ "\n"))

(* 
val () = ppCs today fxPortfolio
*)

(* this file should be extended to showcase advancing, fixings, normalisation *)

end

