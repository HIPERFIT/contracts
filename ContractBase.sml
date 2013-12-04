structure ContractBase = struct

type var = string
datatype exp0 = I of int
              | R of real
              | B of bool
              | Var of var
              | BinOp of string * exp0 * exp0
              | UnOp of string * exp0
              | Obs of string * int

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
end

end
