signature CONTRACTSIG = sig

  (* Expressions *)
  type 'a num
  type 'a exp
  type boolE      = bool exp
  type intE       = int num exp
  type realE      = real num exp

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
  val chosenBy    : string*int -> boolE
  val ifExpr      : boolE * 'a exp * 'a exp -> 'a exp
  val pair        : 'a exp * 'b exp -> ('a*'b) exp
  val fst         : ('a*'b)exp -> 'a exp
  val snd         : ('a*'b)exp -> 'b exp

  (* Functions *)
  val acc         : ('a exp -> 'a exp) * int * 'a exp -> 'a exp

  (* Environments *)
  type date       = DateUtil.date
  type env
  type menv
  val emptyEnv    : env
  val addFix      : (string * int * real) * env -> env
  val emptyFrom   : date -> menv
  val addFixing   : (string * date * real) * menv -> menv
  val addFixings  : (string * date) -> real list -> menv -> menv
  val promoteEnv  : menv -> int -> menv

  (* Evaluation *)
  val evalR       : env -> realE -> real
  val evalI       : env -> intE  -> int
  val evalB       : env -> boolE -> bool

  (* Expression utilities *)
  val certainExp  : 'a exp -> bool
  val simplifyExp : env -> 'a exp -> 'a exp
  val ppExp       : 'a exp -> string
  val eqExp       : 'a exp * 'a exp -> bool
  val translExp   : 'a exp * int -> 'a exp

  (* Contracts *)
  type party      = string
  type cur        = Currency.cur
  type contr
  val zero        : contr
  val transfOne   : cur * party * party -> contr
  val scale       : realE * contr -> contr
  val transl      : int * contr -> contr
  val both        : contr * contr -> contr
  val iff         : boolE * contr * contr -> contr
  val checkWithin : boolE * int * contr * contr -> contr 
  val letc        : 'a exp * ('a exp -> contr) -> contr

  (* Some derived forms *)
  val all         : contr list -> contr
  val flow        : int * realE * cur * party * party -> contr
  val dual        : contr -> contr

  (* Contract utilities *)
  val ppContr     : contr -> string
  val eqContr     : contr * contr -> bool
  val horizon     : contr -> int

  (* Managed contracts *)
  type mcontr = date * contr
  val advance     : int -> mcontr -> mcontr
  val simplify    : menv -> mcontr -> mcontr

  type cashflow   = date * cur * party * party * bool * realE
  val ppCashflows : cashflow list -> string
  val cashflows   : mcontr -> cashflow list
end
