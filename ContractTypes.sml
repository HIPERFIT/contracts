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
   val !<! : 'a num expr * 'a num expr -> boolE
   val obs : string*int -> 'a expr
   val I : int -> intE
   val R : real -> realE
   val B : bool -> boolE
end =
struct
   type var = string
   datatype expr0 = I of int | R of real | B of bool | Var of var | BinOp of string * expr0 * expr0 | UnOp of string * expr0 | Obs of string * int
   type 'a expr = expr0
   type boolE = bool expr
   type 'a num = unit
   type intE = int num expr
   type realE = real num expr
   infix !+! !<!
   fun x !+! y = BinOp("+",x,y)
   fun x !<! y = BinOp("<",x,y)
   val obs : (string*int) -> 'a expr = Obs
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
end
end

