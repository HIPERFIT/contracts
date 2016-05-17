{-# LANGUAGE GADTs #-}
module Contract.Transform
       ( dual
       , advance
       , simplify
       , elimBranches
       ) where
import Debug.Trace
import Contract.Type
import Contract.Expr
import Contract.Date
import Contract.Environment

import Data.List

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
        If e c1 c2 -> let e' = eval env e
                          c1' = simplify0 env c1
                          c2' = simplify0 env c2
                      in iff e' c1' c2' -- if e known, iff will shorten due to use of the smart constructor "iff"
        CheckWithin e i c1 c2 
                   -> let env' = emptyEnv -- (emp,#2 G)
                          substE = eval env'
                          substC = simplify0 env'
                      in case eval env e of
                           B True  -> simplify0 env c1
                           B False -> simplify0 env 
                                      (transl 1 (checkWithin (substE e) (i-1) (substC c1) (substC c2)))
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

-- | uses values from environment to take known decision alternatives (constructs 'if' and 'checkWithin'). Like 'simplify', but it does not use values for scaling contracts.
elimBranches :: MEnv -> MContract -> MContract
elimBranches (Env e_d e) (c_d,c) = (c_d, elimBrs env c)
    where off = dateDiff e_d c_d
          env = promote e off

-- | internal function working on relative dates for env and contract
elimBrs :: Env -> Contract -> Contract
elimBrs env Zero = zero
elimBrs env (Both c1 c2) = both (elimBrs env c1) (elimBrs env c2)
elimBrs env (Scale ob (Both c1 c2)) 
    = elimBrs env (both (scale ob c1) (scale ob c2))
elimBrs env (Scale r t) = scale r (elimBrs env t)
elimBrs env (Transl i t') = transl i (elimBrs (promote env i) t')
elimBrs env c@(TransfOne _ _ _) = c
-- the interesting ones:
elimBrs env (If e c1 c2) =
    let e' = eval env e
        c1' = elimBrs env c1
        c2' = elimBrs env c2
    in iff e' c1' c2' -- if e known, iff will shorten due to use of the smart constructor "iff"
elimBrs env (CheckWithin e 0 c1 c2) = elimBrs env (If e c1 c2)
-- elimBrs env (CheckWithin e i c1 c2) 
--     = let env' = emptyEnv -- (emp,#2 G)
--           substE = eval emptyEnv
--           substC = elimBrs emptyEnv
-- -- MEMO: this was adopted from the simplify0 code in SML; but why are
-- -- we emptying the env? (probably do with variable environment in ML)
--       in case eval env e of
--            B True  -> elimBrs env c1
--            B False -> elimBrs env 
--                       (transl 1 (checkWithin (substE e) (i-1) 
--                                                  (substC c1) (substC c2)))
--            _ -> checkWithin (substE e) i (substC c1) (substC c2)
-- -- For the particular application (scenario execution) the function
-- -- should check whether there is a value _anywhere_ within the checked
-- -- range, and use that, instead of leaving it untouched unless e
-- -- evaluates to B False.
elimBrs env (CheckWithin e n c1 c2)
    = let vs = map (\d -> eval (promote env d) e) [0..n] -- check all values
          firstHit = findIndex (== B True) vs
      in case firstHit of
           Nothing -> -- never true, but maybe undetermined, cannot just use c2
                      -- OK to eliminate in c2, but not in c1 (unknown start)
                       checkWithin e n c1 (elimBrs (promote env n) c2)
           Just i -> -- e is B True on day n. No matter what it might
                     -- be before, use this value to simplify the contract
                       transl i (elimBrs (promote env i) c1)
