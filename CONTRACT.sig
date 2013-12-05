signature CONTRACT = sig
  type var

  (* Expressions *)
  type 'a num
  type 'a exp
  type boolE      = bool exp
  type intE       = int num exp
  type realE      = real num exp

  val Var         : var -> 'a exp
  val I           : int -> intE
  val R           : real -> realE
  val B           : bool -> boolE
  val !+!         : 'a num exp * 'a num exp -> 'a num exp
  val !-!         : 'a num exp * 'a num exp -> 'a num exp
  val !*!         : 'a num exp * 'a num exp -> 'a num exp
  val max         : 'a num exp * 'a num exp -> 'a num exp
  val min         : 'a num exp * 'a num exp -> 'a num exp
  val !<!         : 'a num exp * 'a num exp -> boolE
  val !=!         : 'a exp * 'a exp -> boolE
  val !|!         : boolE * boolE -> boolE
  val not         : boolE -> boolE
  val obs         : string*int -> 'a exp

  (* Environments *)
  type date       = Date.date
  type env
  val emptyEnv    : env
  val addFixing   : (string * date * real) * env -> env

  (* Evaluation *)
  val evalR       : env * date -> realE -> real
  val evalI       : env * date -> intE  -> int
  val evalB       : env * date -> boolE -> bool

  (* Expression utilities *)
  val certainExp  : 'a exp -> bool
  val simplifyExp : env * date -> 'a exp -> 'a exp
  val ppExp       : 'a exp -> string
  val eqExp       : 'a exp * 'a exp -> bool
  val hashExp     : 'a exp * IntInf.int -> IntInf.int
  val translExp   : 'a exp * int -> 'a exp

  (* Contracts *)
  type party      = string
  type cur        = Currency.cur
  type contr
  val transfOne   : cur * party * party -> contr
  val scale       : realE * contr -> contr
  val transl      : int * contr -> contr
  val all         : contr list -> contr
  val iff         : boolE * contr * contr -> contr
  val checkWithin : boolE * int * contr * contr -> contr 

  (* Some derived forms *)
  val zero        : contr
  val flow        : int * realE * cur * party * party -> contr

  val dual        : contr -> contr

  (* Contract utilities *)
  val ppContr     : contr -> string
  val hashContr   : contr * IntInf.int -> IntInf.int
  val eqContr     : contr * contr -> bool
  val simplify    : env * date -> contr -> contr
end

signature CONTRACT_UNSAFE =
CONTRACT where type 'a exp = ContractBase.exp0
           and type contr = ContractBase.contr 
