Require Import Denotational.

(* Fixing (a.k.a. partial evaluation, a.k.a. specialisation) of contracts. *)

Definition constFoldBin {n} (op : BinOp) (e1 e2 : rexp' n) : rexp' n :=
  match e1 with
    | RLit _ r1 => match e2 with
                     | RLit _ r2 => RLit (RBinOp op r1 r2)
                     | _ => RBin op e1 e2
                   end
    | _ => RBin op e1 e2
  end.


Fixpoint constFoldAcc {V} (f : nat -> Z -> rexp' V)  (l : nat) (z : rexp' V) : 
  rexp' V + (nat * rexp' V) :=
  match l with
    | O => inl z
    | S l' => match constFoldAcc f l' z with
                | inl (RLit _ r) => inl (f l r)
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.


                   
Fixpoint Rfixing' {V V'} (e : rexp' V) (rho : obs) : PEnv Z V V' -> rexp' V' :=
    match e with
      | RLit _ r => fun _ => RLit r
      | RBin n op e1 e2 => fun vars => constFoldBin op (Rfixing' e1 rho vars) (Rfixing' e2 rho vars)
      | RNeg _ e => fun vars => 
                      match Rfixing' e rho vars with
                        | RLit _ r => RLit (0 - r)
                        | e => e
                      end
      | Obs _ obs t => fun vars => 
                         match rho t obs with
                           | Some r => RLit r
                           | None => Obs obs t
                         end
      | RVar _ v => fun vars => 
                      match lookupPEnv vars v with
                        | inl r =>  RLit r
                        | inr v' => RVar v'
                      end
      | RAcc _ f l z => fun vars => 
                        let rho' := adv_inp (0 - Z.of_nat l) rho in
                        let f' i z := Rfixing' f (adv_inp (Z.of_nat i)  rho') (PExtend z vars)
                        in match constFoldAcc f' l (Rfixing' z rho' vars) with
                             | inl e => e
                             | inr (l', e') => RAcc (Rfixing' f (fun _ _ => None) (PSkip vars)) l' e'
                           end
    end.

Definition Rfixing (e : rexp) (o : obs) : rexp := Rfixing' e o (PEmpty (zero Z)).

Fixpoint Bfixing (e : bexp) (rho : env) : bexp :=
  match e with
    | BLit b => BLit b
    | BChoice ch t => match snd rho t ch with
                           | Some b => BLit b
                           | None => e
                         end
    | RCmp cmp e1 e2 => match Rfixing e1 (fst rho), Rfixing e2 (fst rho) with 
                          | RLit _ b1, RLit _ b2 => BLit (RCompare cmp b1 b2) 
                          | _,_ => e
                        end
    | BNot e' => match Bfixing e' rho with
                   | BLit b => BLit (negb b)
                   | _ => e
                 end
    | BOp op e1 e2 => match Bfixing e1 rho, Bfixing e2 rho with 
                        | BLit b1, BLit b2 => BLit (BBinOp op b1 b2) 
                        | _,_ => e
                      end
  end.

Fixpoint traverseIfWithin (rho : env) (e: bexp) (c1 c2 : env -> contract) (l : nat) : contract + (bexp * nat) :=
  match Bfixing e rho with
      | BLit true => inl (c1 rho)
      | BLit false => match l with
                        | O => inl (c2 rho)
                        | S l' => traverseIfWithin (adv_env 1 rho) e c1 c2 l'
                        end
      | e' => inr (e', l)
  end.

Fixpoint fixing (c : contract) (rho : env) : contract :=
  match c with
    | Zero => c
    | TransfOne _ _ _ => c
    | Scale e c' => Scale (Rfixing e (fst rho)) c'
    | Transl l c' => Transl l (fixing c' (adv_env (Z.of_nat l) rho))
    | Both c1 c2 => Both (fixing c1 rho) (fixing c2 rho)
    | IfWithin e l c1 c2 => match traverseIfWithin rho e (fixing c1) (fixing c2) l with
                              | inl c' => c
                              | inr (e', l') => transl (l - l') (IfWithin e' l' c1 c2)
                            end
  end.