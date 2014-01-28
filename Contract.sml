structure Contract :> Contract = struct
open ContractBase Currency

fun ppReal s = Real.fmt (StringCvt.FIX(SOME 8)) s

type 'a var = var0
local val c = ref 0
in fun new s = s ^ (Int.toString (!c before c := !c + 1))
end
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
  fun index nil v n = NONE
    | index (x::xs) v n = if v = x then SOME n else index xs v (n+1)

  fun hashExp (vs,e,a) =
      case e of
          I i => H(2,H(i,a))
        | R r => H(3,Hs(ppReal r, a))
        | B true => H(5,a)
        | B false => H(7,a)
        | V v =>
          (case index vs v 0 of
               SOME i => H(11, H(i,a))
             | NONE => H(11, Hs(v,a)))
        | BinOp(s,e1,e2) => Hs(s,hashExp(vs,e1,hashExp(vs,e2,a)))
        | UnOp(s,e) => Hs(s,hashExp(vs,e,a))
        | Obs(s,i) => H(13,Hs(s,H(i,a)))
        | ChosenBy (p,i) => H(17,Hs(p,H(i,a)))
        | Iff (b,e1,e2) => H(19,hashExp(vs,b,hashExp(vs,e1,hashExp(vs,e2,a))))
        | Pair(e1,e2) => H(23,hashExp(vs,e1,hashExp(vs,e2,a)))
        | Fst e => H(29,hashExp(vs,e,a))
        | Snd e => H(31,hashExp(vs,e,a))
        | Acc((v,e1),i,e2) => H(37,H(i,hashExp(v::vs,e1,hashExp(vs,e2,a))))

  fun hashContr (vs,c,a) = 
      case c of
          Zero => H(2,a)
        | Both(c1,c2) => let open IntInf in hashContr(vs,c1,IntInf.fromInt 0) + hashContr(vs,c2,IntInf.fromInt 0) + a end
        | TransfOne(cur,p1,p2) => Hs(ppCur cur,Hs(p1,Hs(p2,H(3,a))))
        | If(e,c1,c2) => hashContr(vs,c1,hashContr(vs,c2,hashExp(vs,e,H(5,a))))
        | Scale(e,c) => hashExp(vs,e,hashContr(vs,c,H(7,a)))
        | Transl(i,c) => H(i,hashContr(vs,c,H(11,a)))
        | CheckWithin(e1,i,c1,c2) => hashContr(vs,c1,hashContr(vs,c2,hashExp(vs,e1,H(i,H(13,a)))))
        | Let(v,e,c) => hashContr(v::vs,c,hashExp(vs,e,H(17,a)))
in
fun eqExp (e1,e2) =
    IntInf.compare(hashExp([],e1,IntInf.fromInt 0),
                   hashExp([],e2,IntInf.fromInt 0)) = EQUAL

fun eqContr (c1,c2) =
    IntInf.compare(hashContr([],c1,IntInf.fromInt 0),
                   hashContr([],c2,IntInf.fromInt 0)) = EQUAL
end

val obs : (string*int) -> 'a exp = Obs
val chosenBy : (string*int) -> boolE = ChosenBy
val ifExpr : boolE * 'a exp * 'a exp -> 'a exp = Iff

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
      | "|" => B (b1 orelse b2)
      | _ => raise Fail ("binopBB: operator not supported: " ^ opr)

fun binop opr e1 e2 =
    let fun mk() = BinOp(opr,e1,e2)
    in case (e1, e2) of
           (I i1, I i2) => binopII opr i1 i2
         | (R r1, R r2) => binopRR opr r1 r2
         | (B b1, B b2) => binopBB opr b1 b2
         | _ => 
       case opr of
           "-" => if eqExp(e1,e2) then I 0
                  else if eqExp(e2,I 0) orelse eqExp(e2,R 0.0) then e1
                  else mk()
         | "min" => if eqExp(e1,e2) then e1 else mk()
         | "max" => if eqExp(e1,e2) then e1 else mk()
         | "<" => if eqExp(e1,e2) then B false else mk()
         | "=" => if eqExp(e1,e2) then B true else mk()
         | "|" => if eqExp(e1,e2) then e1 else mk()
         | "*" => if eqExp(e1,R 1.0) orelse eqExp(e1,I 1) then e2
                  else if eqExp(e2,R 1.0) orelse eqExp(e2,I 1) then e1
                  else if eqExp(e1,R 0.0) orelse eqExp(e2,R 0.0) then R 0.0
                  else if eqExp(e1,I 0) orelse eqExp(e2,I 0) then I 0
                  else mk()
         | "+" => if eqExp(e1,R 0.0) orelse eqExp(e1,I 0) then e2
                  else if eqExp(e2,R 0.0) orelse eqExp(e2,I 0) then e1
                  else mk()
         | _ => mk()
    end

infix !+! !-! !*! !<! !=! !|!
fun x !+! y = binop "+" x y
fun x !-! y = binop "-" x y
fun x !*! y = binop "*" x y
fun x !<! y = binop "<" x y
fun x !=! y = binop "=" x y
fun x !|! y = binop "|" x y
fun max (x,y) = binop "max" x y
fun min (x,y) = binop "min" x y
fun not (B b) = B (Bool.not b)
  | not x = UnOp("not",x)

fun pair (e1,e2) = Pair(e1,e2)
fun fst (Pair(e,_)) = e
  | fst e = Fst e
fun snd (Pair(_,e)) = e
  | snd e = Snd e

(* Functions *)
fun acc (_,0,a) = a
  | acc (f,i,a) =
    let val v = new "v"
    in Acc((v,f (V v)),i,a)
    end

type date = DateUtil.date

(*
env: is a partial function string*int -> real

In analogy to contracts having no explicit date, environments use
relative time in days.

A "management environment" = date*env is used later to handle managed
contacts, adding a "reference date". Likewise, we have "managed
contracts" with a start date.

Contract simplification works with relative environments and relative
contracts, assuming identical reference dates, and aligning the
environment to the contract start date.

It is counter-intuitive to have fixings which are not attached to
absolute dates. Fixings are always added to managed environments, but
enter the simplify routine as a relative environment (aligned to the
contract).

To translate an entire environment in time ("promotion") can mean just
to modify the reference date, or else to offset the lookup function.

For efficiency, we can later implement string*int -> real option as a
hash table (or binary search tree or alike...). At the moment, we
carry around partial functions constructed in the heap.

Every environment contains bindings to a value "days since started"
(called "Time); which are 0 to infinity in the relative environment.

*)

(* Variable environments map variables to certain (ground) expressions *)
type VE = var0 -> exp0 option
val emptyVE : VE = fn _ => NONE
fun addVE (VE,v,e) = fn x => if v = x then SOME e else VE x
fun lookupVE (VE,v) = VE v

type env = string * int -> real option

datatype menv = Env of date * env

val emp : env = fn _ => NONE

val emptyEnv : env = fn (s,i) => if s = "Time" 
                                 then SOME (Real.fromInt i) else NONE

(* we do want a function that sets the start date to something convenient... *)
fun emptyFrom d = Env (d, emptyEnv)

fun promote (e:env) (i:int) : env = e o (fn (s,x) => (s,x+i))

fun promoteEnv (Env (d,e) : menv) (i:int) : menv = Env (d,promote e i)

fun addFix ((s,d,r:real),e:env):env =
    fn x => if s = #1 x andalso #2 x = d then SOME r else e x

(* new values silently take precedence with this definition *)
fun addFixing ((s,d,r), Env (e_d, e_f) : menv) : menv =
    let val off = DateUtil.dateDiff e_d d
    in Env (e_d,
         fn x => if s = #1 x andalso #2 x = off then SOME r else e_f x)
    end

fun addFixings (s,d) [] e = e
(* inefficient
  | addFixings (s,d) vs e = 
    ListPair.foldl (fn (d,v,e) => addFixing ((s,d,v),e))
      e (List.tabulate (length vs, fn i => DateUtil.addDays i d), vs)
*)
  | addFixings (s,d) vs (Env (e_d,e_f)) =
    let val l = length vs
        fun f (s',n) = if s = s' andalso  n >= 0 andalso n < l 
                     then SOME (List.nth (vs,n)) else e_f (s',n)
    in Env (e_d, f)
    end 

fun certainExp e =
    case e of
        V _ => false       (* if variables are used only for functions in Acc, we could return true here! *)
      | I _ => true
      | R _ => true
      | B _ => true
      | Obs _ => false
      | ChosenBy _ => false
      | BinOp(_,e1,e2) => certainExp e1 andalso certainExp e2
      | UnOp(_,e1) => certainExp e1
      | Iff(b,e1,e2) => certainExp b andalso certainExp e1 andalso certainExp e2
      | Pair(e1,e2) => certainExp e1 andalso certainExp e2
      | Fst e => certainExp e
      | Snd e => certainExp e
      | Acc((v,e),i,a) => certainExp e andalso certainExp a

fun translExp (e,0) = e
  | translExp (e,d) =
    case e of
        Obs (s,t) => obs (s,t+d)
      | BinOp(s,e1,e2) => BinOp(s,translExp(e1,d),translExp(e2,d))
      | UnOp(s,e) => UnOp(s,translExp(e,d))
      | ChosenBy(p,t) => ChosenBy(p,t+d)
      | Iff(b,e1,e2) => Iff(translExp(b,d),translExp(e1,d),translExp(e2,d))
      | Fst e => fst(translExp(e,d))
      | Snd e => snd(translExp(e,d))
      | Pair(e1,e2) => pair(translExp(e1,d),translExp(e2,d))
      | Acc((v,e),i,a) => Acc((v,translExp(e,d)),i,translExp(a,d))
      | I _=> e
      | R _ => e
      | B _ => e
      | V _ => e

fun eval (E : env * VE) (e : exp0) =
    case e of
        V v => (case lookupVE(#2 E,v) of
                    SOME e => e (* should we call eval again here? *)
                                (* is e relative to a start date here? *)
                  | NONE => e)
      | I _ => e
      | R _ => e
      | B _ => e
      | Obs obs => (case #1 E obs of
                        SOME r => R r
                      | NONE => e)
      | BinOp(opr,e1,e2) => binop opr (eval E e1) (eval E e2)
      | UnOp("not", e1) => 
        (case eval E e1 of
             B b => B(Bool.not b)
           | e1 => UnOp("not",e1))
      | UnOp(opr,_) => raise Fail ("eval.UnOp: unsupported operator: " ^ opr)
      | ChosenBy ch => (case #1 E ch of SOME r => B (Real.!=(r, 0.0)) (* HAAAACK *)
                                      | NONE => e)
      | Iff(b,e1,e2) => (case eval E b of
                             B true  => eval E e1
                           | B false => eval E e2
                           | other   => Iff (other, eval E e1, eval E e2))
      | Fst e => fst(eval E e)
      | Snd e => snd(eval E e)
      | Pair(e1,e2) => pair(eval E e1,eval E e2)
      | Acc((v,e),i,a) =>
        let val a = eval E a
        in if i <= 0 then a 
           else if certainExp a then
             eval (#1 E,addVE(#2 E,v,a)) (Acc((v,translExp(e,1)),i-1,e))
           else Acc((v,e),i,a)
        end

fun evalR E e = 
    case eval (E,emptyVE) e of R r => r
                             | _ => raise Fail "evalR: expecting real"
fun evalI E e =
    case eval (E,emptyVE) e of I i => i
                             | _ => raise Fail "evalI: expecting int"
fun evalB E e =
    case eval (E,emptyVE) e of B b => b
                             | _ => raise Fail "evalB: expecting bool"
         
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
        fun ppExp e = ppExp0 ppTime e
        fun ppFun (v,e) = "fn " ^ v ^ " => " ^ ppExp e
    in case e of 
           V s => s
         | I i => ppTime i
         | R r => ppReal r
         | B b => Bool.toString b
         | Obs (s,off) => "Obs" ^ par (s ^ "@" ^ ppTime off)
         | BinOp(opr,e1,e2) => 
           if notfixed opr then opr ^ par (ppExp e1 ^ "," ^ ppExp e2)
           else par(ppExp e1 ^ opr ^ ppExp e2)
         | UnOp(opr, e1) => opr ^ par (ppExp e1)
         | ChosenBy (p,i) => "Chosen by " ^ p ^ " @ " ^ ppTime i
         | Iff (b,e1,e2) => par (ppExp b ^ "? " ^ ppExp e1 ^ " : " ^ ppExp e2)
         | Pair(e1,e2) => par (ppExp e1 ^ "," ^ ppExp e2)
         | Fst e => "fst" ^ par(ppExp e)
         | Snd e => "snd" ^ par(ppExp e)
         | Acc(f,i,e) => "acc" ^ par(ppFun f ^ "," ^ Int.toString i ^ "," ^ ppExp e)
    end
val ppExp = ppExp0 Int.toString
val ppTimeExp = ppExp0 ppTime

fun simplifyExp E e = eval (E,emptyVE) e

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
         | Let(v,e,c) => "Let" ^ par (v ^ "," ^ ppExp e ^ "," ^ ppContr c)
    end
and ppContrs [] = ""
  | ppContrs [c] = ppContr c
  | ppContrs (c::cs) = ppContr c ^ ", " ^ ppContrs cs

val zero = Zero
val transfOne = TransfOne
fun transl (0,c) = c
  | transl (i,c) =
    if i < 0 then raise Fail "transl: negative time"
    else case c of             
             Zero => zero
           | Transl(i',c) => transl(i+i',c)
           | _ => Transl(i,c) 

fun iff (B true,  c1,c2) = c1
  | iff (B false, c1,c2) = c2
  | iff (b,c1,c2) = if eqContr(c1,c2) then c1
                    else If(b,c1,c2)

fun checkWithin (b,0,c1,c2) = iff (b,c1,c2)
  | checkWithin (b,i,c1,c2) = if i > 0 then CheckWithin (b,i,c1,c2)
                              else raise Fail "checkWithin: negative duration"

fun both (Zero,c2) = c2
  | both (c1,Zero) = c1
  | both (c1,c2) = Both(c1,c2)

fun all [] = Zero
  | all [c] = c
  | all (c::cs) = both(c,all cs)

fun scale (_,Zero) = zero
  | scale (r,Scale(r',c)) = scale(r !*! r', c)
  | scale (r,t) = if eqExp(R 0.0, r) then zero
                  else if eqExp(R 1.0, r) then t
                  else Scale(r,t)

(* Shorthand notation *)
fun flow(d,v,c,from,to) = scale(v,transl(d,transfOne(c,from,to)))

val rec dual = 
 fn Zero => zero
  | TransfOne(c,p1,p2) => transfOne(c,p2,p1)
  | Scale (e,c) => scale(e,dual c)
  | Transl(i,c) => transl(i,dual c)
  | Both(c1,c2) => both (dual c1, dual c2)
  | If(e,c1,c2) => iff(e,dual c1, dual c2)
  | CheckWithin (e, i, c1, c2) => checkWithin (e, i, dual c1, dual c2)
  | Let(v,e,c) => Let(v,e,dual c)

(* Contract Management *)
(* internal simplify, assumes c and env have same reference date *)
fun simplify0 G t =       (* G is (E,VE) *)
    case t of
        Zero => zero
      | Both(c1,c2) => both(simplify0 G c1, simplify0 G c2)
      | Scale(obs,Both(c1,c2)) => 
        simplify0 G (both(scale(obs,c1),scale(obs,c2)))
      | Scale(r,t) => scale(eval G r,simplify0 G t)
      | Transl(i,t') =>
        let val (E,VE) = G
            val E' = promote E i (* E o (fn (s,n) => (s,n+i)) *)
        in transl(i,simplify0 (E',VE) t')
        end
      | TransfOne _ => t
      | If (e, c1, c2) => 
        let val e = eval G e
            val c1 = simplify0 G c1
            val c2 = simplify0 G c2
        in iff(e,c1,c2) (* if e is known, iff constr. will shorten *)
        end
      | CheckWithin (e, i, c1, c2) =>
        let val G0 = (emp,#2 G)
            val substE = eval G0
            val substC = simplify0 G0
(*
            val () = print ("e = " ^ ppExp e ^ "\n")
            val () = print ("obs(Time,0) = " ^ ppExp (eval G (obs("Time",0))) ^ "\n")
*)
        in case eval G e of
               B true => simplify0 G c1
             | B false => simplify0 G (transl(1,checkWithin(substE e,i-1,substC c1,substC c2)))
             | _ => checkWithin (substE e, i, substC c1, substC c2)
        end
      | Let(v,e,c) =>
        let val e' = eval G e
        in if certainExp e' then
             let val G' = (#1 G, addVE(#2 G,v,e'))
             in simplify0 G' c
             end
           else Let(v,e',simplify0 G c)
        end

fun simplify (Env (e_d,e_f)) (c_d,c) =
    let val off = DateUtil.dateDiff e_d c_d
        val E   = promote e_f off (* e_f o (fn (s,x) => (s,x+off)) *)
    in (c_d, simplify0 (E,emptyVE) c)
    end

type cashflow   = date * cur * party * party * bool * realE
fun ppCashflow w (d,cur,p1,p2,certain,e) =
    let fun sq s = "[" ^ s ^ "]"
        fun pad w s =
            s ^ CharVector.tabulate (w - size s, fn _ => #" ")
        fun ppCertain true = "Certain"
          | ppCertain false = "Uncertain"
    in String.concatWith " "
       [DateUtil.ppDate d,
        ppCertain certain,
        pad w (sq(p1 ^ "->" ^ p2)),
        ppCur cur,
        ppExp (simplifyExp emptyEnv e)]
    end

fun ppCashflows [] = "no cashflows"
  | ppCashflows l =  
    let val szs = List.map (fn (_,_,p1,p2,_,_) => size p1 + size p2 + 4) l
        val sz = List.foldl(fn (i,a) => if i > a then i else a) 0 szs
    in String.concatWith "\n" (List.map (ppCashflow sz) l)
    end

fun cashflows (d,c) : cashflow list =
    let fun cf (d,c,s,certain) =
            case c of
                Zero => nil
              | TransfOne(c,p1,p2) => [(d,c,p1,p2,certain,s)]
              | Both(c1,c2) => cf(d,c1,s,certain) @ cf(d,c2,s,certain)
              | Scale(s',c) => cf(d,c,s !*! s',certain)
              | Transl(i,c2) =>
                let val d' = DateUtil.addDays i d
(*
                    val () = print ("d=" ^ DateUtil.ppDate d ^ "\n")
                    val () = print ("i=" ^ Int.toString i ^ "\n")
                    val () = print ("d'=" ^ DateUtil.ppDate d' ^ "\n")
*)
                in cf(d',c2,s,certain)
                end
              | If(b,c1,c2) => cf(d,c1,s,false) @ cf(d,c2,s,false)
              | CheckWithin(e,i,c1,c2) =>
                if i < 0 then cf(d,c1,s,false) @ cf(d,c2,s,false)
                else cf(d,c1,s,false) @
                     cf(DateUtil.addDays 1 d,
                        checkWithin(translExp(e,1),i-1,c1,c2),s,certain)
              | Let(v,e,c) => cf(d,c,s,certain)          (* MEMO: check this *)
        val flows = cf(d,c,R 1.0,true)
    in ListSort.sort (fn ((d1,_,_,_,_,_),(d2,_,_,_,_,_)) => DateUtil.compare (d1,d2)) flows
    end

(* horizon of a contract. Never returns negative number *)
fun horizon     Zero       = 0
  | horizon (TransfOne _ ) = 0
  | horizon (Scale(_,c))   = horizon c
  | horizon (Both (c1,c2)) = Int.max(horizon c1, horizon c2)
  | horizon (Transl(i,c))  = i + horizon c (* maybe negative if i < 0 *)
  | horizon (If(_,c1,c2))  = Int.max (horizon c1, horizon c2)
  | horizon (CheckWithin (_,i,c1,c2)) = i + Int.max (horizon c1, horizon c2)
  | horizon (Let(_,_,c)) = horizon c

type mcontr = date * contr (* "managed contract", with a start date *)
(* Remove the next i days from a contract *)
fun adv i c : contr =
    if i < 0 then raise Fail "adv: expecting a positive number of days"
    else if i = 0 then c
    else case c of
             Zero => zero
           | Both(c1,c2) => both(adv i c1, adv i c2)
           | Transl(i',c) =>
             if i <= i' then transl(i'-i,c)
             else adv (i-i') c
           | Scale(s,c) => scale(translExp(s,~i),adv i c)
           | TransfOne _ => zero
           | If(b,c1,c2) => iff(translExp(b,~i),adv i c1, adv i c2)
           | CheckWithin(e,i',c1,c2) =>
             raise Fail "adv: you cannot advance into a CheckWithin construct - fixings are needed using simplify"
           | Let(v,e,c) => Let(v,translExp(e,~i),adv i c)

fun advance i (d,c) =
    (DateUtil.addDays i d,
     adv i c)

fun letc (e,f) =
    let val v = new "v"
    in Let(v,e,f(V v))
    end

end
