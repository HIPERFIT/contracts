structure Contract :> CONTRACT_UNSAFE = struct
open ContractBase Currency
type 'a exp = exp0
type boolE = bool exp
type 'a num = unit
type intE = int num exp
type realE = real num exp

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
                                
fun ppExp e = 
    let fun par s = "(" ^ s ^ ")"
        fun notfixed opr = opr = "max" orelse opr = "min"
    in case e of 
           Var s => "Var" ^ par s
         | I i => Int.toString i
         | R r => Real.toString r
         | B b => Bool.toString b
         | Obs (s,off) => "Obs" ^ par (s ^ "@" ^ Int.toString off)
         | BinOp(opr,e1,e2) => 
           if notfixed opr then opr ^ par (ppExp e1 ^ "," ^ ppExp e2)
           else par(ppExp e1 ^ opr ^ ppExp e2)
         | UnOp(opr, e1) => opr ^ par (ppExp e1)
    end
        
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

val rec eqExp = fn
    (I i1, I i2) => i1 = i2
  | (R r1, R r2) => Real.compare(r1,r2) = EQUAL
  | (B b1, B b2) => b1 = b2
  | (Var v1, Var v2) => v1 = v2
  | (BinOp(s1,e1,e'1), BinOp(s2,e2,e'2)) => s1 = s2 andalso eqExp(e1,e2) andalso eqExp(e'1,e'2)
  | (UnOp(s1,e1), UnOp(s2,e2)) => s1 = s2 andalso eqExp(e1,e2)
  | (Obs(s1,i1),Obs(s2,i2)) => s1=s2 andalso i1=i2
  | _ => false

fun ppContr c =
    let fun par s = "(" ^ s ^ ")"
    in case c of
           TransfOne(c,p1,p2) => "TransfOne" ^ par (ppCur c ^ "," ^ p1 ^ "," ^ p2)
         | Scale (e,c) => "Scale" ^ par (ppExp e ^ "," ^ ppContr c)
         | Transl(e,c) => "Transl" ^ par (ppExp e ^ "," ^ ppContr c)
         | All[] => "emp"
         | All cs => "All" ^ par (ppContrs cs)
         | If(e,c1,c2) => "If" ^ par (ppExp e ^ ", " ^ ppContr c1 ^ ", " ^ ppContr c2)
         | CheckWithin (e1, e2, c1, c2) => 
           "CheckWithin" ^ par (ppExp e1 ^ ", " ^ ppExp e2 ^ ", "  ^ ppContr c1 ^ ", " ^ ppContr c2)
    end
and ppContrs [] = ""
  | ppContrs [c] = ppContr c
  | ppContrs (c::cs) = ppContr c ^ ", " ^ ppContrs cs

val transfOne = TransfOne
val transl = Transl
val checkWithin = CheckWithin
val iff = If
val all = All
val scale = Scale

(* Shorthand notation *)
fun flow(d,v,c,from,to) = scale(v,transl(d,transfOne(c,from,to)))
val emp = All []

end
