structure test = struct

open Currency Contract
infix !+! !-! !*! !<! !=! !|! 

fun println s = print (s ^ "\n")

fun prHash s c =
   println ("\nHash(" ^ s ^ ") = " ^ IntInf.toString (hashContr(c,IntInf.fromInt 0)) ^ "\n")

fun you2me(d,v,c) = flow(d,R v,c,"you","me")

(* these guys are now just int *)
val now = 0
val today = DateUtil.? "2013-01-01"
fun M n = (n*30)
fun Y n = (n*360)

val me2you = dual o you2me

fun report s (d,c) =
    (println "";
     println(s ^ " - Contract:\n  " ^ ppContr c);
     println "\nCashflows:";
     println (ppCashflows(cashflows (d,c))))

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

val ex4m = (today, ex4)
val () = report "Ex4 (call option)" ex4m
val _ = println "\nEx4 - Cashflows on 1000 Stock options (Strike:50,Price:79):"
val e = addFixing ((equity,DateUtil.addDays maturity today,79.0),emptyEnv)
val ex4m' = (today, simplify(e,today) ex4)
val ex4m'' = advance maturity ex4m'
val () = report "Ex4 (call option - price=79 and advanced)" ex4m''

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

val _ = println "\nEx4if - Cashflows on 1000 Stock options (Strike:50,Price:79):"

(* val _ = println (cashflows (fn _ => 79.0) ex4if) *)

(*
fun matureit e =
    let
      val ex5 = fixing(equity,maturity,83.0) e
      val _ = println "\nEx5 - Call option with fixing 83"
      val _ = println ("ex5 = " ^ pp ex5)
      val ex6 = fixing(equity,maturity,46.0) e
      val _ = println "\nEx6 - Call option with fixing 46"
      val _ = println ("ex6 = " ^ pp ex6)
    in  ()
    end

val () = matureit ex4
val () = matureit ex4if


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

val _ = println("\nPrice(ex1) : DKK " ^ Real.toString p1)
val _ = println("\nPrice(ex2) : DKK " ^ Real.toString p2)
*)
end
