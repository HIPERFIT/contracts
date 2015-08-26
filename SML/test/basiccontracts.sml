structure test = struct

open Currency ContractSafe
infix !+! !-! !*! !<! !=! !|! 

fun ppReal s = Real.fmt (StringCvt.FIX(SOME 8)) s
fun println s = print (s ^ "\n")

fun you2me(d,v,c) = flow(d,R v,c,"you","me")

(* these guys are now just int *)
val now = 0
val today = DateUtil.? "2013-01-01"
val () = print ("Today is " ^ DateUtil.ppDate today ^ "\n")
fun M n = n*30
fun Y n = n*360

val me2you = dual o you2me

fun report s (d,c) =
    (println "\n---REPORT BEGIN---";
     println ("Today is " ^ DateUtil.ppDate d);
     println (s ^ " - Contract:\n" ^ ppContr c);
     println "Cashflows:";
     println (ppCashflows(cashflows (d,c)));
     println "---REPORT END---"
    )

(* Simple amortized loan *)
val ex1 =
    let val coupon = 11000.0
        val principal = 30000.0
    in all [you2me(now,principal,EUR),
            me2you(M 1,coupon,EUR),
            me2you(M 2,coupon,EUR),
            me2you(M 3,coupon,EUR)]
    end

val () = report "Ex1 (swap)" (today,ex1)

(* Cross currency swap *)
val ex2 =
    let val coupon_eur = 1000.0
        val coupon_dkk = 7000.0
    in all [dual(
             all[me2you(M 0,coupon_dkk,DKK),
                 me2you(M 1,coupon_dkk,DKK),
                 me2you(M 2,coupon_dkk,DKK)]),
            me2you(M 0,coupon_eur,EUR),
            me2you(M 1,coupon_eur,EUR),
            me2you(M 2,coupon_eur,EUR)]
    end    

val ex2m = (today,ex2)
val () = report "Ex2 (Fx-swap)" ex2m

val ex3 = advance 15 ex2m
val _ = println "\nEx3: Cross-currency swap advanced half a month:"
val _ = println (ppCashflows(cashflows ex3))

(* Call option on "Carlsberg" stock *)
val equity = "Carlsberg"
val maturity = Y 1
val ex4 =
    let val strike = 50.0
        val nominal = 1000.0
        val obs = max(R 0.0, obs(equity,0) !-! R strike)
    in scale(R nominal,
             transl(maturity,
                    scale(obs,transfOne(EUR,"you","me"))))
    end

fun mature s c p =
    let val m = (today, c)
        val () = report (s ^ " - initial") m
        val ME0 = emptyFrom today
        val ME = addFixing ((equity,DateUtil.addDays maturity today,p),ME0)
        val m' = simplify ME m
        val m'' = advance maturity m'
    in report (s ^ " - at maturity; price(maturity)=" ^ ppReal p) m''
    end

val () = mature "Ex4-79 (call option, strike=50.0)" ex4 79.0

(* same call option, expressed with If *)
val ex4if =
    let val strike = 50.0
        val nominal = 1000.0
        val obs = obs(equity,0)
    in scale(R nominal,
             transl(maturity,
                    iff (R strike !<! obs,
                         scale(obs !-! R strike,
                               transfOne(EUR,"you","me")),
                         zero)))
    end

(* should be:
val () = mature "Ex4if-79 (call option, strike=50.0)" ex4if 79.0
val () = mature "Ex4if-46 (call option, strike=50.0)" ex4if 46.0
   (correct it alongside the tests.ok text file... *)
val () = mature "Ex4if-79 (call option, strike=50.0)" ex4 79.0
val () = mature "Ex4if-46 (call option, strike=50.0)" ex4 46.0

(*
(* Valuation (Pricing) *)
structure FlatRate = struct
  fun discount d0 d amount rate =
      let val time = real (dateDiff d0 d) / 365.2422
                     (* could use precise day count instead of 365.2422 *)
      in amount * Math.exp(~ rate * time)
      end
  fun price d0 (R : currency -> real) 
               (FX: currency * real -> real) t =
      let val flows = cashflows0 noE t
      in List.foldl (fn ((d,cur,_,_,v,_),acc) =>
                        acc + FX(cur,discount d0 d v (R cur))) 
                    0.0 flows
      end
end

fun FX(EUR,v) = 7.0 * v
  | FX(DKK,v) = v
fun R EUR = 0.04
  | R DKK = 0.05

val p1 = FlatRate.price (?"2011-01-01") R FX ex1
val p2 = FlatRate.price (?"2011-01-01") R FX ex2

val _ = println("\nPrice(ex1) : DKK " ^ ppReal p1)
val _ = println("\nPrice(ex2) : DKK " ^ ppReal p2)
*)
end
