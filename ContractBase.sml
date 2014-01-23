structure ContractBase = struct

type var0 = string
datatype exp0 = I of int
              | R of real
              | B of bool
              | V of var0
              | BinOp of string * exp0 * exp0
              | UnOp of string * exp0
              | Obs of string * int      (* Obs(s,i): the value of s in i days; negative
                                          * values refer to the past... *)
              | ChosenBy of string * int (* label(incl party) and time *)
              | Iff of exp0 * exp0 * exp0
              | Pair of exp0 * exp0
              | Fst of exp0
              | Snd of exp0
              | Acc of (var0*exp0) * int * exp0  (* Acc(f,i,a) = f/i(...(f/2(f/1(a)))) *)

local open Currency
in
type party = string
datatype contr =
       Zero
     | TransfOne of cur * party * party
     | Scale of exp0 * contr
     | Transl of int * contr
     | Both of contr * contr
     | If of exp0 * contr * contr
     | CheckWithin of exp0 * int * contr * contr
     (* if cond : boolE becomes true within time: intE then contract 1 in effect. 
        otherwise (time expired, always false) contract 2 in effect
      *)
     | Let of var0 * exp0 * contr
end

end
