structure multicontracts = struct

(* our own date library, day-precision and support for arithmetic *)
open DateUtil

(* Contracts *)
datatype currency = EUR | DKK | SEK | USD | GBP | JPY
fun pp_cur EUR = "EUR"
  | pp_cur DKK = "DKK"
  | pp_cur SEK = "SEK"
  | pp_cur USD = "USD"
  | pp_cur GBP = "GBP"
  | pp_cur JPY = "JPY"

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
                if #1 arg = #1 arg1
                   andalso Date.compare (#2 arg, #2 arg1) = EQUAL
                then raise Eval
                else eval E obs
              | _ => eval E obs
           end
         | Mul(obs1,obs2) => eval E obs1 * eval E obs2
         | Add(obs1,obs2) => eval E obs1 + eval E obs2
         | Sub(obs1,obs2) => eval E obs1 - eval E obs2
         | Max(obs1,obs2) => max (eval E obs1) (eval E obs2)
      end

  fun evalOpt E obs =
      SOME (eval E obs) handle Eval => NONE

  fun pp obs = 
      let fun par s = "(" ^ s ^ ")"
      in case obs of 
           Const r => Real.toString r
         | Underlying(s,d) => "[" ^ s ^ ":" ^ DateUtil.ppDate d ^ "]"
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

type party = string

structure Contract = struct
  datatype t = 
           TransfOne of              (* Atom: cash flow *)
           Date.date * currency * party * party
         | Scale of Obs.t *   t      (* scaling by observable value *)
         | All of t list             (* combining several contracts *)
         | Transl of int * t         (* move into the future by some days.
                                        Days argument must be positive! *)
         | Dual of t                 (* invert transfers in a contract *)
         | If of (real -> bool) * Obs.t * t 
                                     (* conditional (on observable) *)

  fun pp t =
      case t of
        TransfOne (when,c,from,to) => "TransfOne(" ^ DateUtil.ppDate when ^ "," 
                                      ^ pp_cur c ^ "," ^ from ^ "->" ^ to ^ ")"
      | Scale (obs, t) => "Scale(" ^ Obs.pp obs ^ "," ^ pp t ^ ")"
      | All [] => "emp"
      | All ts => "All[" ^ String.concatWith "," (map pp ts) ^ "]"
      | Transl (days, t) => "Transl(" ^ Int.toString days ^ "," ^ pp t ^ ")"
      | Dual t => "Dual(" ^ pp t ^ ")"
      | If (pred, obs, t) => "Conditional on " ^ Obs.pp obs ^ ": " ^ pp t

  (* Shorthand notation *)
  fun flow(d,v,c,from,to) = Scale(Obs.Const v,TransfOne(d,c,from,to))
  val emp = All []

  (* Contract Management *)
  fun simplify E t =
      case t of
        All ts =>
        let val ts = map (simplify E) ts
        in case List.filter (fn All[] => false | _ => true) ts of
             [t] => t
           | ts => All ts
        end
      | Dual(All[]) => All[]
      | Scale(obs,All[]) => All[]
      | Dual(All ts) => simplify E (All(map Dual ts))
      | Scale(obs,All ts) => 
        simplify E (All (map (fn t => Scale(obs,t)) ts))
      | Scale(obs,t) => 
        (case Scale(Obs.simplify E obs,simplify E t) of
           Scale(o1,Scale(o2,t)) => 
           simplify E (Scale(Obs.Mul(o1,o2),t))
         | Scale(obs,All[]) => All[]
         | t as Scale(Obs.Const r,_) => 
           if Real.==(r,0.0) then emp else t
         | t => t)
      | Transl(d,t) => (* Transl should be eliminated, push it inside *)
        (case simplify E t of (* do we need this call to simplify? *)
             All []  => emp
           | TransfOne (date,c,from,to) => TransfOne(addDays d date,c,from,to)
                                           (* do the translate in the date *)
           | Scale (obs,t') => simplify E (Scale (obs,Transl(d,t')))
           | All ts  => All (List.map (fn t => simplify E (Transl(d,t))) ts)
           | Transl(d',t')  => simplify E (Transl(d'+d,t')) (* collapse *)
           | Dual t' => simplify E (Dual (Transl(d,t')))
           | If (pred,obs,t') => simplify E (If (pred,obs,Transl(d,t')))
             (* XXX should transl this obs as well?   ^^^ *)
        )
      | Dual t => 
        (case Dual(simplify E t) of
             Dual(Dual t) => simplify E t
           | Dual(TransfOne(d,c,from,to)) => TransfOne(d,c,to,from)
           | t => t)
      | TransfOne _ => t
      | If (pred, obs, t') => 
        let val obs' = Obs.simplify E obs
            val t''  = simplify E t'
        in case Obs.evalOpt E obs' of
               SOME r => if pred r then t'' else emp
             | NONE => If (pred, obs', t'')
        end

  fun noE _ = raise Fail "noEnv"

  (* Apply a fixing to a contract *)
  fun fixing (name,date,value) t =
      let fun E arg = 
              if #1 arg = name 
                 andalso Date.compare (#2 arg, date) = EQUAL
              then Obs.Const value 
              else Obs.Underlying arg
      in simplify E t (* should also advance t to date *)
      end

  (* Remove the past from a contract *)      
  fun advance d t =
      let val t = simplify noE t
          fun adv t =
              case t of
                TransfOne (dt,c,from,to) => if Date.compare (dt,d) = GREATER 
                                            then t else emp (* remove past transfers *)
              | Scale(obs,t) => Scale(obs, adv t)
              | Transl _ => t
              | Dual t => Dual(adv t)
              | All ts => All(map adv ts)
              | If (p,obs,t') => If (p, obs, adv t')
      in simplify noE (adv t)
      end

  fun swap (x,y) = (y,x)

  fun today() = ? "2010-10-19"
                
 (* Future Cash Flows *)
  (* XXX can get rid of d parameter now *)
  fun cashflows0 E t =
      let fun flows sw s d c t =
              if Real.== (s, 0.0) then []
              else
              case t of
                TransfOne (when,cur,from,to) =>
                let val (from,to) = sw (from,to)
                in [(when,cur,from,to,s,if c then Certain else Uncertain)]
                end
              | Scale(obs,t) => 
                let val s1 = (Obs.eval E obs) handle _ => 1.0
                in flows sw (s * s1) d 
                         (c andalso Obs.certainty obs) t
                end
              | All ts => List.concat (map (flows sw s d c) ts)
              | Transl(d,t) => raise Error "flows sw s d c t" 
              (* XXX do the translate, quite like the simplify code *)
              | Dual t => flows (sw o swap) s d c t                      
              | If (pred, obs, t') =>
                case Obs.evalOpt E obs of
                    SOME r => if pred r then flows sw s d c t' (* obs is certain *)
                              else []
                  | NONE => flows sw s d false t' (* obs is uncertain *)
          val res = flows (fn x => x) 1.0 (today()) true t
      in ListSort.sort 
             (fn (r1,r2) => Date.compare(#1 r1,#1 r2)) 
             res
      end

    fun cashflows E t : string =
        let fun pp (d,cur,from,to,r,c) = 
              DateUtil.ppDate d ^ " " ^ pp_certainty c ^ " " ^ 
              pp_cur cur ^ " " ^ Real.toString r ^ "  [" ^ from ^ " -> " ^ to ^ "]" 
            val res = cashflows0 E t
        in String.concatWith "\n" (List.map pp res)
        end
end

end
