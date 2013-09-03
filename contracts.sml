(* Contracts *)

datatype currency = EUR | DKK
fun pp_cur EUR = "EUR"
  | pp_cur DKK = "DKK"

datatype certainty = Certain | Uncertain
fun pp_certainty Certain = "Certain  "
  | pp_certainty Uncertain = "Uncertain"

(* Observables *)
structure Obs = struct
  datatype t = 
           Const of real
         | Underlying of string * Date.date
         | Mul of t * t
         | Add of t * t
         | Sub of t * t
         | Max of t * t

  (* Evaluation utility function on observables *)
  exception Eval
  fun eval E obs =
      let fun max r1 r2 = if r1 > r2 then r1 else r2
      in case obs of
           Const r => r
         | Underlying arg =>
           let val obs = E arg
           in case obs of
                Underlying arg1 =>
                if arg = arg1 then raise Eval
                else eval E obs
              | _ => eval E obs
           end
         | Mul(obs1,obs2) => eval E obs1 * eval E obs2
         | Add(obs1,obs2) => eval E obs1 + eval E obs2
         | Sub(obs1,obs2) => eval E obs1 - eval E obs2
         | Max(obs1,obs2) => max (eval E obs1) (eval E obs2)
      end

  fun pp obs = 
      let fun par s = "(" ^ s ^ ")"
      in case obs of 
           Const r => Real.toString r
         | Underlying(s,d) => "[" ^ s ^ ":" ^ Date.toString d ^ "]"
         | Mul(o1,o2) => par(pp o1 ^ "*" ^ pp o2)
         | Add(o1,o2) => par(pp o1 ^ "+" ^ pp o2)
         | Sub(o1,o2) => par(pp o1 ^ "-" ^ pp o2)
         | Max(o1,o2) => "max(" ^ pp o1 ^ "," ^ pp o2 ^ ")"
      end

  fun certainty t =
      case t of
        Const _ => true
      | Underlying _ => false
      | Mul(o1,o2) => certainty o1 andalso certainty o2
      | Add(o1,o2) => certainty o1 andalso certainty o2
      | Sub(o1,o2) => certainty o1 andalso certainty o2
      | Max(o1,o2) => certainty o1 andalso certainty o2

  (* Try to simplify an observable by evaluating it *)
  fun simplify E obs =
      let fun simpl opr o1 o2 = 
              opr(simplify E o1,simplify E o2)
      in (Const(eval E obs)) 
         handle _ =>
         case obs of
           Const _ => obs
         | Underlying _ => obs
         | Mul(o1,o2) => simpl Mul o1 o2
         | Add(o1,o2) => simpl Add o1 o2
         | Sub(o1,o2) => simpl Sub o1 o2
         | Max(o1,o2) => simpl Max o1 o2
      end
end

structure Contract = struct
  datatype t = 
           One of currency
         | Scale of Obs.t * t
         | All of t list
         | Acquire of Date.date * t
         | Give of t

  fun pp t =
      case t of
        One c => "One(" ^ pp_cur c ^ ")"
      | Scale (obs, t) => "Scale(" ^ Obs.pp obs ^ "," ^ pp t ^ ")"
      | All [] => "zero"
      | All ts => "All[" ^ String.concatWith "," (map pp ts) ^ "]"
      | Acquire (d, t) => "Acquire(" ^ Date.toString d ^ "," ^ pp t ^ ")"
      | Give t => "Give(" ^ pp t ^ ")"

  (* Shorthand notation *)
  fun flow(d,v,c) = Acquire(d,Scale(Obs.Const v,One c))
  val zero = All []

  (* Contract Management *)
  fun simplify d0 E t =
      case t of
        All ts =>
        let val ts = map (simplify d0 E) ts
        in case List.filter (fn All[] => false | _ => true) ts of
             [t] => t
           | ts => All ts
        end
      | Give(All[]) => All[]
      | Scale(obs,All[]) => All[]
      | Give(All ts) => simplify d0 E (All(map Give ts))
      | Scale(obs,All ts) => 
        simplify d0 E (All (map (fn t => Scale(obs,t)) ts))
      | Scale(obs,t) => 
        (case Scale(Obs.simplify E obs,simplify d0 E t) of
           Scale(o1,Scale(o2,t)) => 
           simplify d0 E (Scale(Obs.Mul(o1,o2),t))
         | Scale(obs,All[]) => All[]
         | t as Scale(Obs.Const r,_) => 
           if Real.==(r,0.0) then zero else t
         | t => t)
      | Acquire(d,t) => 
        if Date.diff d0 d >= 0 then simplify d0 E t
        else Acquire(d,simplify d0 E t)
      | Give t => 
        (case Give(simplify d0 E t) of
           Give(Give t) => simplify d0 E t
         | t => t)
      | One _ => t

  fun noE _ = raise Fail "noEnv"

  (* Apply a fixing to a contract *)
  fun fixing (name,date,value) t =
      let fun E arg = 
              if arg = (name,date) then Obs.Const value 
              else Obs.Underlying arg
      in simplify date E t
      end

  (* Remove the past from a contract *)      
  fun advance d t =
      let val t = simplify d noE t
          fun adv t =
              case t of
                One _ => zero
              | Scale(obs,t) => Scale(obs, adv t)
              | Acquire _ => t
              | Give t => Give(adv t)
              | All ts => All(map adv ts)
      in simplify d noE (adv t)
      end

  (* Future Cash Flows *)

  fun today() = Date.fromString "2010-10-19"

  fun cashflows0 E t =
      let fun flows s d c t =
              case t of
                One cur => 
                [(d,cur,s,if c then Certain else Uncertain)]
              | Scale(obs,t) => 
                let val s1 = (Obs.eval E obs) handle _ => 1.0
                in flows (s * s1) d 
                         (c andalso Obs.certainty obs) t
                end
              | All ts => List.concat (map (flows s d c) ts)
              | Acquire(d,t) => flows s d c t
              | Give(t) => flows (~s) d c t                      
          val res = flows 1.0 (today()) true t
      in Listsort.sort 
             (fn (r1,r2) => Date.compare(#1 r1,#1 r2)) 
             res
      end

    fun cashflows E t : string =
        let fun pp (d,cur,r,c) = 
              Date.toString d ^ " " ^ pp_certainty c ^ " " ^ 
              pp_cur cur ^ " " ^ Real.toString r          
            val res = cashflows0 E t
        in String.concatWith "\n" (List.map pp res)
        end
end

open Contract

fun println s = print (s ^ "\n")

fun ? s = Date.fromString s

(* Simple amortized loan *)
val ex1 =
    let val coupon = 11000.0
        val principal = 30000.0
    in All [Give(flow(?"2011-01-01",principal,EUR)),
            flow(?"2011-02-01",coupon,EUR),
            flow(?"2011-03-01",coupon,EUR),
            flow(?"2011-04-01",coupon,EUR)]
    end

val _ = println "\nEx1 - Cashflows for simple amortized loan:"
val _ = println (cashflows noE ex1)

(* Cross currency swap *)
val ex2 =
    let val coupon_eur = 1000.0
        val coupon_dkk = 7000.0
    in All [Give(
             All[flow(?"2011-01-01",coupon_dkk,DKK),
                 flow(?"2011-02-01",coupon_dkk,DKK),
                 flow(?"2011-03-01",coupon_dkk,DKK)]),
            flow(?"2011-01-01",coupon_eur,EUR),
            flow(?"2011-02-01",coupon_eur,EUR),
            flow(?"2011-03-01",coupon_eur,EUR)]
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
             Acquire(maturity,Scale(obs,One EUR)))
    end

val _ = println "\nEx4 - Cashflows on 1000 Stock options (Strike:50,Price:79):"
val _ = println (cashflows (fn _ => Obs.Const 79.0) ex4)

val ex5 = fixing(equity,maturity,83.0) ex4
val _ = println "\nEx5 - Call option with fixing 83"
val _ = println ("ex5 = " ^ pp ex5)
val ex6 = fixing(equity,maturity,46.0) ex4
val _ = println "\nEx6 - Call option with fixing 46"
val _ = println ("ex6 = " ^ pp ex6)


(* Valuation (Pricing) *)
structure FlatRate = struct
  fun discount d0 d amount rate =
      let val time = real(Date.diff d d0) / 360.0
      in amount * Math.exp(~ rate * time)
      end
  fun price d0 (R : currency -> real) 
               (FX: currency * real -> real) t =
      let val flows = cashflows0 noE t
      in List.foldl (fn ((d,cur,v,_),acc) =>
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
