Require Import Denotational.

Definition Admit {A} : A. admit. Defined.

Open Scope Z.

Definition constFoldBin {n} (op : BinOp) (e1 e2 : rexp' n) : rexp' n :=
  match e1 with
    | RLit _ r1 => match e2 with
                     | RLit _ r2 => RLit (RBinOp op r1 r2)
                     | _ => RBin op e1 e2
                   end
    | _ => RBin op e1 e2
  end.

Fixpoint constFoldAcc {n} (f : nat -> option Z -> rexp' (S n)) (l : nat) (z : rexp' n) : rexp' n :=
  match l with
    | 0 => z
    | S l' => match constFoldAcc f l' z with
                | RLit r => f l (Some r) 
                | _ => 

let zo := match z with
                          | RLit r => Some r 
                          | _ => None
                        end
              in f l zo
Fixpoint Rfixing {n} (e : rexp' n) : obs -> rexp' n :=
  fun rho =>
    match e with
      | RLit _ r => RLit r
      | RBin n op e1 e2 =>  constFoldBin op (Rfixing e1 rho) (Rfixing e2 rho)
      | RNeg _ e => match Rfixing e rho with
                      | RLit _ r => RLit (0 - r)
                      | e => e
                    end
      | Obs _ obs t => match rho t obs with
                         | Some r => RLit r
                         | None => Obs obs t
                       end
      | RVar _ v => RVar v 
      | RAcc _ f m z => RAcc f m (Rfixing z rho)
    end.

Fixpoint Bfixing (e : bexp) : env ->  bexp :=
  fun rho => 
    match e with
      | BLit r => BLit r
      | BChoice choice t => match snd rho t choice with
                              | Some b => BLit b
                              | None => BChoice choice t
                            end
      | BOp op e1 e2 =>  BOp op (Bfixing e1 rho) (Bfixing e2 rho)
      | BNot e => BNot (Bfixing e rho)
      | RCmp cmp e1 e2 => RCmp cmp (Rfixing e1 (fst rho)) (Rfixing e2 (fst rho))
    end.


Fixpoint Cfixing (c : contract) : env -> contract :=
  fun rho => 
    match c with
      | Zero => Zero
      | TransfOne _ _ _ => c
      | Scale e c' => Sclae (Rfixing e rho (fst rho)) (Cfixing c' rho)
      | Transl d c' => Transl d (Cfixing c (adv_env (Z.of_nat d) rho))
      | Both c1 c2 => Both c1 c2 (C[|c1|]rho) (C[|c2|]rho)
      | IfWithin e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).
