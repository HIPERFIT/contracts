{-# LANGUAGE GADTs #-}
module Contract.Transform
       ( dual
       , advance
       , simplify
       ) where

import Contract.Type
import Contract.Expr
import Contract.Date

dual :: Contract -> Contract
dual Zero = zero
dual (TransfOne c p1 p2) = transfOne c p2 p1
dual (Scale  e c) = scale e (dual c)
dual (Transl i c) = transl i (dual c)
dual (Both c1 c2) = both (dual c1) (dual c2)
dual (If e c1 c2) = iff e (dual c1) (dual c2)
dual (CheckWithin e i c1 c2) = checkWithin e i (dual c1) (dual c2)

-- | Remove the given number of days (assumed positive) from a contract
advance :: Int -> MContract -> MContract
advance i (d,c) | i < 0  = error "advance: expecting positive number of days"
                | i == 0 = (d,c)
                | otherwise = (addDays i d, adv i c)

adv :: Int -> Contract -> Contract
adv i c = case c of
             Zero -> zero
             Both c1 c2 -> both (adv i c1) (adv i c2)
             Transl i' c -> if i <= i' then transl (i'-i) c
                            else adv (i-i') c
             Scale s c -> scale (translExp s (-i)) (adv i c)
             TransfOne _ _ _ -> zero
             If b c1 c2 -> iff (translExp b (-i)) (adv i c1) (adv i c2)
             CheckWithin e i' c1 c2 
                 -> error "cannot advance into a CheckWithin (simplify first)"
          -- Let(v,e,c) => Let(v,translExp(e,~i),adv i c)

-- | simplify a contract, using fixings from a managed environment ('MEnv')
simplify :: MEnv -> MContract -> MContract
simplify (Env e_d e_f) (c_d, c) = (c_d, simplify0 env c)
    where off = dateDiff e_d c_d
          env = promote e_f off -- (* e_f o (fn (s,x) => (s,x+off)) *)

-- | internal simplify, assumes c and env have same reference date
simplify0 :: Env -> Contract -> Contract
simplify0 env c = 
    case c of
        Zero -> zero
        Both c1 c2 -> both (simplify0 env c1) (simplify0 env c2)
        Scale ob (Both c1 c2) -> 
            simplify0 env (both (scale ob c1) (scale ob c2))
        Scale r t -> scale (eval env r) (simplify0 env t)
        Transl i t' -> transl i (simplify0 (promote env i) t')
        TransfOne _ _ _ -> c
        If e c1 c2 -> let e = eval env e
                          c1 = simplify0 env c1
                          c2 = simplify0 env c2
                      in iff e c1 c2 -- if e known, iff constr. will shorten
        CheckWithin e i c1 c2 
            -> let env' = emptyEnv -- (emp,#2 G)
                   substE = eval env'
                   substC = simplify0 env'
               in case eval env e of
                    B True  -> simplify0 env c1
                    B False -> simplify0 env 
                               (transl 1 (checkWithin (substE e) (i-1) 
                                                 (substC c1) (substC c2)))
                    _ -> checkWithin (substE e) i (substC c1) (substC c2)

{- (*
            val () = print ("e = " ^ ppExp e ^ "\n")
            val () = print ("obs(Time,0) = " ^ ppExp (eval G (obs("Time",0))) ^ "\n")
*) -}

      --  Let(v,e,c) =>
      --   let val e' = eval G e
      --   in if certainExp e' then
      --        let val G' = (#1 G, addVE(#2 G,v,e'))
      --        in simplify0 G' c
      --        end
      --      else Let(v,e',simplify0 G c)

