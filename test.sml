structure test = struct

open multicontracts

open Contract

fun println s = print (s ^ "\n")

fun you2me(d,v,c) = flow(d,v,c,"you","me")

val me2you = Dual o you2me

(* Simple amortized loan *)
val ex1 =
    let val coupon = 11000.0
        val principal = 30000.0
    in All [you2me(?"2011-01-01",principal,EUR),
            me2you(?"2011-02-01",coupon,EUR),
            me2you(?"2011-03-01",coupon,EUR),
            me2you(?"2011-04-01",coupon,EUR)]
    end

val _ = println "\nEx1 - Cashflows for simple amortized loan:"
val _ = println (cashflows noE ex1)

(* Cross currency swap *)
val ex2 =
    let val coupon_eur = 1000.0
        val coupon_dkk = 7000.0
    in All [Dual(
             All[me2you(?"2011-01-01",coupon_dkk,DKK),
                 me2you(?"2011-02-01",coupon_dkk,DKK),
                 me2you(?"2011-03-01",coupon_dkk,DKK)]),
            me2you(?"2011-01-01",coupon_eur,EUR),
            me2you(?"2011-02-01",coupon_eur,EUR),
            me2you(?"2011-03-01",coupon_eur,EUR)]
    end    

val _ = println "\nEx2 - Cashflows for cross-currency swap:"
val _ = println (cashflows noE ex2)

(* Contract Management *)

val ex3 = advance (?"2011-01-15") ex2
val _ = println "\nEx3: Cross-currency swap advanced to 2011-01-15:"
val _ = println (cashflows noE ex3)

(* Call option on "Carlsberg" stock *)
val equity = "Carlsberg"
val maturity = ?"2012-01-01"
val ex4 =
    let val strike = 50.0
        val nominal = 1000.0
        val obs = 
            Obs.Max(Obs.Const 0.0,
                    Obs.Sub(Obs.Underlying(equity,maturity),
                            Obs.Const strike))
    in Scale(Obs.Const nominal,
             Scale(obs,TransfOne(maturity,EUR,"you","me")))
    end

val _ = println "\nEx4 - Cashflows on 1000 Stock options (Strike:50,Price:79):"
val _ = println (cashflows (fn _ => Obs.Const 79.0) ex4)

(* same call option, expressed with If *)
val ex4if =
    let val strike = 50.0
        val nominal = 1000.0
        val obs = Obs.Underlying(equity,maturity)
        val pred = fn r => r > strike
    in Scale(Obs.Const nominal,
             If (pred, obs,
                 Scale(Obs.Sub(obs,Obs.Const strike),
                       TransfOne(maturity,EUR,"you","me"))))
    end

val _ = println "\nEx4if - Cashflows on 1000 Stock options (Strike:50,Price:79):"
val _ = println (cashflows (fn _ => Obs.Const 79.0) ex4if)

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

end
