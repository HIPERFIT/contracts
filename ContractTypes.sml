structure ContractTypes = struct

structure Currency = struct
datatype cur = EUR | DKK | SEK | USD | GBP | JPY
fun ppCur EUR = "EUR"
  | ppCur DKK = "DKK"
  | ppCur SEK = "SEK"
  | ppCur USD = "USD"
  | ppCur GBP = "GBP"
  | ppCur JPY = "JPY"
end

structure Expr : sig 
   type var = string
   type 'a expr
   type boolE = bool expr
   type 'a num
   type intE = int num expr
   type realE = real num expr
   val Var : var -> 'a expr
   val !+! : 'a num expr * 'a num expr -> 'a num expr
   val !-! : 'a num expr * 'a num expr -> 'a num expr
   val !*! : 'a num expr * 'a num expr -> 'a num expr
   val max : 'a num expr * 'a num expr -> 'a num expr
   val min : 'a num expr * 'a num expr -> 'a num expr
   val !<! : 'a num expr * 'a num expr -> boolE
   val !=! : 'a expr * 'a expr -> boolE
   val !|! : boolE * boolE -> boolE
   val not : boolE -> boolE
   val obs : string*int -> 'a expr
   val I : int -> intE
   val R : real -> realE
   val B : bool -> boolE
   exception Eval of string
   type env
   type date = Date.date
   val empty : env
   val addFixing : (string * date * real) * env -> env
   val evalR : env * date -> realE -> real
   val evalI : env * date -> intE  -> int
   val evalB : env * date -> boolE -> bool
   val pp    : 'a expr -> string
end =
struct
   type var = string
   datatype expr0 = I of int | R of real | B of bool | Var of var | BinOp of string * expr0 * expr0 | UnOp of string * expr0 | Obs of string * int
   type 'a expr = expr0
   type boolE = bool expr
   type 'a num = unit
   type intE = int num expr
   type realE = real num expr
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
   val obs : (string*int) -> 'a expr = Obs
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
         | "=" => B (r1=r2) 
         | "max" => R(if r1 >= r2 then r1 else r2)
         | "min" => R(if r1 <= r2 then r1 else r2)
         | _ => raise Fail ("binopRR: operator not supported: " ^ opr)
   fun binopBB opr b1 b2 =
       case opr of
           "=" => B (b1=b2)
         | _ => raise Fail ("binopBB: operator not supported: " ^ opr)
   type date = Date.date
   type env = string*date*int -> real option   (* int is a date offset *)
   val empty : env = fn _ => NONE
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
                      | _ => raise Fail "evalI: expecting int"
   fun evalB E e =
       case eval E e of B b => b
                      | _ => raise Fail "evalB: expecting bool"

  fun pp e = 
      let fun par s = "(" ^ s ^ ")"
          fun notfixed opr = opr = "max" orelse opr = "min"
      in case e of 
          Var s => "Var" ^ par s
        | I i => Int.toString i
        | R r => Real.toString r
        | B b => Bool.toString b
        | Obs (s,off) => "Obs" ^ par (s ^ "@" ^ Int.toString off)
        | BinOp(opr,e1,e2) => 
          if notfixed opr then opr ^ par (pp e1 ^ "," ^ pp e2)
          else par(pp e1 ^ opr ^ pp e2)
        | UnOp(opr, e1) => opr ^ par (pp e1)
      end

  fun certain e =
      case e of
          Var _ => false
        | I _ => true
        | R _ => true
        | B _ => true
        | Obs _ => false
        | BinOp(_,e1,e2) => certain e1 andalso certain e2
        | UnOp(_,e1) => certain e1

  fun simplify P e =  (* memo: rewrite to bottom-up strategy to avoid the quadratic behavior *)
      eval P e
      handle Eval _ =>
             case e of
                 UnOp(f,e1) => UnOp(f,simplify P e1)
               | BinOp(f,e1,e2) => BinOp(f,simplify P e1,simplify P e2)
               | _ => e
end

local open Expr Currency
in
type party = string
datatype contract =
       TransfOne of cur * party * party
     | Scale of realE * contract
     | Transl of intE * contract
     | All of contract list
     | If of boolE * contract * contract
     | Iter of intE * (var -> contract)
     | CheckWithin of boolE * intE * contract * contract 
     (* if cond : boolE becomes true within time: intE then contract 1 in effect. 
        otherwise (time expired, always false) contract 2 in effect
      *)

fun pp c =
    let fun par s = "(" ^ s ^ ")"
    in case c of
           TransfOne(c,p1,p2) => "TransfOne" ^ par (ppCur c ^ "," ^ p1 ^ "," ^ p2)
         | Scale (e,c) => "Scale" ^ par (Expr.pp e ^ "," ^ pp c)
         | Transl(e,c) => "Transl" ^ par (Expr.pp e ^ "," ^ pp c)
         | All[] => "emp"
         | All cs => "All" ^ par (pps cs)
         | If(e,c1,c2) => "If" ^ par (Expr.pp e ^ ", " ^ pp c1 ^ ", " ^ pp c2)
         | Iter _ => raise Fail "unimplemented"
         | CheckWithin (e1, e2, c1, c2) => 
           "CheckWithin" ^ par (Expr.pp e1 ^ ", " ^ Expr.pp e2 ^ ", "  ^ pp c1 ^ ", " ^ pp c2)
    end
and pps [] = ""
  | pps [c] = pp c
  | pps (c::cs) = pp c ^ ", " ^ pps cs

(* Shorthand notation *)
fun flow(d,v,c,from,to) = Scale(Expr.R v,Transl(d,TransfOne(c,from,to)))
val emp = All []

end
end

