structure Contract :> CONTRACT_UNSAFE = struct
open ContractBase Currency
type 'a exp = exp0
type boolE = bool exp
type 'a num = unit
type intE = int num exp
type realE = real num exp

local
  type hash = IntInf.int
  val Alpha = IntInf.fromInt 65599
  val Beta = IntInf.fromInt 19
  fun H (p,a) = IntInf.*(IntInf.fromInt p,
                         IntInf.+(a,IntInf.fromInt 1))
  fun hashAdd (w:IntInf.int, acc) = let open IntInf in w+acc*Beta end
  fun Hs (s,a:hash) =
	let val sz = size s
	    fun loop (n,a) = 
		if n >= sz then a
		else loop (n+1, 
			   hashAdd 
			       (IntInf.fromInt(Char.ord(String.sub(s,n))), a))
	in loop (0,a)
	end
in
fun hashExp (e,a) =
    case e of
        I i => H(2,H(i,a))
      | R r => H(3,Hs(Real.toString r, a))
      | B true => H(5,a)
      | B false => H(7,a)
      | Var v => H(11, Hs(v,a))
      | BinOp(s,e1,e2) => Hs(s,hashExp(e1,hashExp(e2,a)))
      | UnOp(s,e) => Hs(s,hashExp(e,a))
      | Obs(s,i) => H(13,Hs(s,H(i,a)))
fun hashContr (c,a) = 
    case c of
        Zero => H(2,a)
      | Both(c1,c2) => let open IntInf in hashContr(c1,IntInf.fromInt 0) + hashContr(c2,IntInf.fromInt 0) + a end
      | TransfOne(cur,p1,p2) => Hs(ppCur cur,Hs(p1,Hs(p2,H(3,a))))
      | If(e,c1,c2) => hashContr(c1,hashContr(c2,hashExp(e,H(5,a))))
      | Scale(e,c) => hashExp(e,hashContr(c,H(7,a)))
      | Transl(i,c) => H(i, hashContr(c,H(11,a)))
      | CheckWithin(e1,i,c1,c2) => hashContr(c1,hashContr(c2,hashExp(e1,H(i,H(13,a)))))
end
infix !+! !-! !*! !<! !=! !|!
fun x !+! y = BinOp("+",x,y)
fun x !-! y = BinOp("-",x,y)
fun x !*! y = BinOp("*",x,y)
fun x !<! y = BinOp("<",x,y)
fun x !=! y = BinOp("=",x,y)
fun x !|! y = BinOp("|",x,y)
fun not x = UnOp("not",x)
fun max (x,y) = BinOp("max",x,y)
fun min (x,y) = BinOp("min",x,y)

val obs : (string*int) -> 'a exp = Obs

exception Eval of string

fun binopII opr i1 i2 =
    case opr of
        "+" => I (i1+i2)
      | "-" => I (i1-i2) 
      | "*" => I (i1*i2) 
      | "<" => B (i1<i2) 
      | "=" => B (i1=i2)
      | "max" => I(if i1 >= i2 then i1 else i2)
      | "min" => I(if i1 <= i2 then i1 else i2)
      | _ => raise Fail ("binopII: operator not supported: " ^ opr)

fun binopRR opr r1 r2 =
    case opr of
        "+" => R (r1+r2)
      | "-" => R (r1-r2) 
      | "*" => R (r1*r2) 
      | "<" => B (r1<r2) 
      | "=" => B (Real.compare(r1,r2) = EQUAL) 
      | "max" => R(if r1 >= r2 then r1 else r2)
      | "min" => R(if r1 <= r2 then r1 else r2)
      | _ => raise Fail ("binopRR: operator not supported: " ^ opr)

fun binopBB opr b1 b2 =
    case opr of
        "=" => B (b1=b2)
      | _ => raise Fail ("binopBB: operator not supported: " ^ opr)

type date = Date.date

type env = string*date*int -> real option   (* int is a date offset *)

val emptyEnv : env = fn _ => NONE

fun date_eq d1 d2 = Date.compare (d1,d2) = EQUAL

fun addFixing ((s,d,r),e:env) : env = 
    fn k => 
       let val off = #3 k
       in if s = #1 k andalso off >= 0 andalso date_eq d (DateUtil.addDays off (#2 k)) then SOME r
          else if s = #1 k andalso off < 0 andalso date_eq (DateUtil.addDays (~off) d) (#2 k) then SOME r
          else e k
       end

fun eval (E:env,d:date) e =
    case e of
        Var s => raise Eval ("variable " ^ s)
      | I _ => e
      | R _ => e
      | B _ => e
      | Obs (s,off) =>
        (case E (s,d,off) of
             SOME r => R r
           | NONE => raise Eval "unresolved observable")
      | BinOp(opr,e1,e2) => 
        (case (eval (E,d) e1, eval (E,d) e2) of
               (I i1, I i2) => binopII opr i1 i2
             | (R r1, R r2) => binopRR opr r1 r2
             | (B b1, B b2) => binopBB opr b1 b2
             | _ => raise Fail "eval.BinOp: difference in argument types")
        | UnOp("not", e1) => 
          (case eval (E,d) e1 of
              B b => B(Bool.not b)
            | _ => raise Fail "eval.UnOp.not - wrong argument type")
        | UnOp(opr,_) => raise Fail ("eval.UnOp: unsupported operator: " ^ opr)
                               
fun evalR E e = 
    case eval E e of R r => r
                   | _ => raise Fail "evalR: expecting real"
fun evalI E e =
    case eval E e of I i => i
                   | _ => raise Fail "evalI: expecting real"

fun evalB E e =
    case eval E e of B b => b
                   | _ => raise Fail "evalB: expecting real"
         
fun ppTime t = 
    let val months = t div 30
        val years = t div 360
        val months = months mod 12
        val days = t mod 30
        val s = if days = 0 then "" else Int.toString days ^ "d"
        val s = if months = 0 then s else Int.toString months ^ "m" ^ s
        val s = if years = 0 then s else Int.toString years ^ "y" ^ s
    in if s = "" then "0d" else s
    end
                       
fun ppExp0 ppTime e = 
    let fun par s = "(" ^ s ^ ")"
        fun notfixed opr = opr = "max" orelse opr = "min"
    in case e of 
           Var s => "Var" ^ par s
         | I i => ppTime i
         | R r => Real.toString r
         | B b => Bool.toString b
         | Obs (s,off) => "Obs" ^ par (s ^ "@" ^ ppTime off)
         | BinOp(opr,e1,e2) => 
           if notfixed opr then opr ^ par (ppExp e1 ^ "," ^ ppExp e2)
           else par(ppExp e1 ^ opr ^ ppExp e2)
         | UnOp(opr, e1) => opr ^ par (ppExp e1)
    end
and ppExp e = ppExp0 Int.toString e
val ppTimeExp = ppExp0 ppTime

fun certainExp e =
    case e of
        Var _ => false
      | I _ => true
      | R _ => true
      | B _ => true
      | Obs _ => false
      | BinOp(_,e1,e2) => certainExp e1 andalso certainExp e2
      | UnOp(_,e1) => certainExp e1
                              
fun simplifyExp P e =  (* memo: rewrite to bottom-up strategy to avoid the quadratic behavior *)
    eval P e
    handle Eval _ =>
           case e of
               UnOp(f,e1) => UnOp(f,simplifyExp P e1)
             | BinOp(f,e1,e2) => BinOp(f,simplifyExp P e1,simplifyExp P e2)
             | _ => e

(*
val rec eqExp = fn
    (I i1, I i2) => i1 = i2
  | (R r1, R r2) => Real.compare(r1,r2) = EQUAL
  | (B b1, B b2) => b1 = b2
  | (Var v1, Var v2) => v1 = v2
  | (BinOp(s1,e1,e'1), BinOp(s2,e2,e'2)) => s1 = s2 andalso eqExp(e1,e2) andalso eqExp(e'1,e'2)
  | (UnOp(s1,e1), UnOp(s2,e2)) => s1 = s2 andalso eqExp(e1,e2)
  | (Obs(s1,i1),Obs(s2,i2)) => s1=s2 andalso i1=i2
  | _ => false
*)

fun eqExp (e1,e2) = IntInf.compare(hashExp(e1,IntInf.fromInt 0),hashExp(e2,IntInf.fromInt 0)) = EQUAL
fun ppContr c =
    let fun par s = "(" ^ s ^ ")"
    in case c of
           TransfOne(c,p1,p2) => "TransfOne" ^ par (ppCur c ^ "," ^ p1 ^ "," ^ p2)
         | Scale (e,c) => "Scale" ^ par (ppExp e ^ "," ^ ppContr c)
         | Transl(i,c) => "Transl" ^ par (ppTimeExp (I i) ^ "," ^ ppContr c)
         | Zero => "zero"
         | Both (c1,c2) => "Both" ^ par (ppContrs[c1,c2])
         | If(e,c1,c2) => "If" ^ par (ppExp e ^ ", " ^ ppContr c1 ^ ", " ^ ppContr c2)
         | CheckWithin (e, i, c1, c2) => 
           "CheckWithin" ^ par (ppExp e ^ ", " ^ ppTimeExp (I i) ^ ", "  ^ ppContr c1 ^ ", " ^ ppContr c2)
    end
and ppContrs [] = ""
  | ppContrs [c] = ppContr c
  | ppContrs (c::cs) = ppContr c ^ ", " ^ ppContrs cs

val transfOne = TransfOne
val transl = Transl
val checkWithin = CheckWithin
val iff = If
fun all [] = Zero
  | all [c] = c
  | all (c::cs) = Both(c,all cs)
val scale = Scale

(* Shorthand notation *)
fun flow(d,v,c,from,to) = scale(v,transl(d,transfOne(c,from,to)))
val zero = Zero

val rec dual = 
 fn Zero => Zero
  | TransfOne(c,p1,p2) => TransfOne(c,p2,p1)
  | Scale (e,c) => Scale(e,dual c)
  | Transl(i,c) => Transl(i,dual c)
  | Both(c1,c2) => Both (dual c1, dual c2)
  | If(e,c1,c2) => If(e,dual c1, dual c2)
  | CheckWithin (e, i, c1, c2) => CheckWithin (e, i, dual c1, dual c2)
(*
(* Contract Management *)
fun simplify P t =
    case t of
        All ts =>
        let val ts = map (simplify P) ts
        in case List.filter (fn All[] => false | _ => true) ts of
             [t] => t
           | ts => all ts
        end
      | Scale(obs,All[]) => zero
      | Scale(obs,All ts) => 
        simplify P (all (map (fn t => scale(obs,t)) ts))
      | Scale(r,t) => 
        (case scale(simplifyExp P r,simplify P t) of
             Scale(o1,Scale(o2,t)) => simplify P (scale(o1 !*! o2,t))
           | Scale(obs,All[]) => zero
           | t as Scale(R r,_) => 
             if Real.==(r,0.0) then zero else t
           | t => t)
      | Transl(d,t') => (* Transl should be pushed inside *)
        let val d = simplifyExp P d
            val t' = simplify P t'
        in case t' of (* do we need this call to simplify? *)
               All []  => zero
             | TransfOne _ => transl(d,t')
             | Scale (r,t') =>
               if certainExp r then simplify P (scale (r,transl(d,t')))
               else t (* maybe simplify t' in a modified env *)
             | All ts  => all (List.map (fn t => simplify P (transl(d,t))) ts)
             | Transl(d',t')  => simplify P (transl(d' !+! d,t')) (* collapse *)
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
               SOME r => if pred r then t'' else zero
             | NONE => If (pred, obs', t'')
        end
*)
end
