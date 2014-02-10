(* this is a mosml script for development *)

app load ["Real", "Int", "ContractBase", "Contract", "ContractTriggers" ];

open ContractBase Contract ContractTriggers;

(* copied *)
infix !+! !-! !*! !<! !=! !|! ;

load "Currency"; open Currency;

fun M n = n*30
fun Y n = n*360

(* Barrier option on "Carlsberg" stock *)
val equity = "Carlsberg"
val maturity = M 3
val ex4if =
    let val strike = 50.0
        val obs = obs(equity,0)
    in checkWithin (R strike !<! obs, maturity,
                    scale(obs !-! R strike,
                          transfOne(EUR,"you","me")),
                    zero)
    end

fun mkOpt i s =
    let val strike = s
        val obs = obs(equity,0)
    in checkWithin (R strike !<! obs, M i,
                    scale(obs !-! R strike,
                          transfOne(EUR,"you","me")),
                    zero)
    end

val test1 = all (List.tabulate (3, fn di => mkOpt 3 (40.0 + real di)))
val test2 = all (List.tabulate (6, fn i => mkOpt i (real i + 42.0)))
val test3 = all [test1,test2]

fun ppTriggers     [] = ""
  | ppTriggers ((s,(i,j),vs)::rest) 
    = s ^ " from day " ^ Int.toString i ^ " to " ^ Int.toString j ^
      ": " ^ (String.concatWith ", " (map Real.toString vs)) ^
      "\n" ^ ppTriggers rest

(* some test data  *)
infix !+! !-! !*! !<! !=! !|! ;

load "Currency"; open Currency;

fun M n = n*30
fun Y n = n*360

(* Barrier option on "Carlsberg" stock *)
val equity = "Carlsberg"
val maturity = M 3
val ex4if =
    let val strike = 50.0
        val obs = obs(equity,0)
    in checkWithin (R strike !<! obs, maturity,
                    scale(obs !-! R strike,
                          transfOne(EUR,"you","me")),
                    zero)
    end

fun mkOpt i s =
    let val strike = s
        val obs = obs(equity,0)
    in checkWithin (R strike !<! obs, M i,
                    scale(obs !-! R strike,
                          transfOne(EUR,"you","me")),
                    zero)
    end

val test1 = all (List.tabulate (3, fn di => mkOpt 3 (40.0 + real di)))
val test2 = all (List.tabulate (6, fn i => mkOpt i (real i + 42.0)))
val test3 = all [test1,test2]

val () = (print ("Carlsberg barrier options (settled):\n" ^ ppContr test3);
          print "\nTrigger values:\n";
          print (ppTriggers (triggers (0,10) test3)))

