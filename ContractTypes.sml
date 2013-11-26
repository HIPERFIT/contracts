structure ContractTypes = struct

structure Currency = struct
datatype cur = EUR | DKK | SEK | USD | GBP | JPY
fun pp_cur EUR = "EUR"
  | pp_cur DKK = "DKK"
  | pp_cur SEK = "SEK"
  | pp_cur USD = "USD"
  | pp_cur GBP = "GBP"
  | pp_cur JPY = "JPY"
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
   val !<! : 'a num expr * 'a num expr -> boolE
   val !=! : 'a expr * 'a expr -> boolE
   val !|! : boolE * boolE -> boolE
   val obs : string*int -> 'a expr
   val I : int -> intE
   val R : real -> realE
   val B : bool -> boolE
   exception Eval of string
   type env = string*int -> realE   (* extend later *)
   val evalR : env -> realE -> real
   val evalI : env -> intE -> int
   val evalB : env -> boolE -> bool
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
   val obs : (string*int) -> 'a expr = Obs
   exception Eval of string
   fun binopII opr i1 i2 =
       case opr of
           "+" => I (i1+i2)
         | "-" => I (i1-i2) 
         | "*" => I (i1*i2) 
         | "<" => B (i1<i2) 
         | "=" => B (i1=i2) 
         | _ => raise Fail ("binopII: operator not supported: " ^ opr)
   fun binopRR opr r1 r2 =
       case opr of
           "+" => R (r1+r2)
         | "-" => R (r1-r2) 
         | "*" => R (r1*r2) 
         | "<" => B (r1<r2) 
         | "=" => B (r1=r2) 
         | _ => raise Fail ("binopRR: operator not supported: " ^ opr)
   fun binopBB opr b1 b2 =
       case opr of
           "=" => B (b1=b2)
         | _ => raise Fail ("binopBB: operator not supported: " ^ opr)
   type env = string*int -> realE   (* extend later *)
   fun eval (E:env) e =
       case e of
          Var s => raise Eval ("variable " ^ s)
        | I _ => e
        | R _ => e
        | B _ => e
        | Obs u =>
          (case E u of
               Obs u' => if u = u' then raise Eval "unresolved observable"
                         else eval E (Obs u')
             | e' => eval E e')
        | BinOp(opr,e1,e2) => 
          (case (eval E e1, eval E e2) of
               (I i1, I i2) => binopII opr i1 i2
             | (R r1, R r2) => binopRR opr r1 r2
             | (B b1, B b2) => binopBB opr b1 b2
             | _ => raise Fail "eval.BinOp: difference in argument types")
        | UnOp("not", e1) => 
          (case eval E e1 of
              B b => B(not b)
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
end
end

