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


Fixpoint constFoldAcc {V} (rho : obs) (f : obs -> Z -> rexp' V)  (l : nat) (z : obs -> rexp' V) :
  rexp' V + (nat * rexp' V) :=
  match l with
    | O => inl (z rho)
    | S l' => match constFoldAcc (adv_inp (-1) rho) f l'  z with
                | inl (RLit _ r) => inl (f rho r)
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.

Definition obs_empty : obs := fun _ _ => None.

Fixpoint Rfixing' {V V'} (e : rexp' V) (rho : obs) : PEnv Z V V' -> rexp' V' :=
    match e with
      | RLit _ r => fun _ => RLit r
      | RBin _ op e1 e2 => fun vars => constFoldBin op (Rfixing' e1 rho vars) (Rfixing' e2 rho vars)
      | RNeg _ e => fun vars =>
                      match Rfixing' e rho vars with
                        | RLit _ r => RLit (- r)
                        | e => RNeg e
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
                        let z' rho := Rfixing' z rho vars in
                        let f' rho r := Rfixing' f rho (PExtend r vars)
                        in match constFoldAcc rho f' l z' with
                             | inl e => e
                             | inr (l', e') => RAcc (Rfixing' f obs_empty (PSkip vars)) l' e'
                           end
    end.


Fixpoint constFoldAcc' {V V'} (vars: PEnv Z V V') (rho : obs) (f : Scope rexp' V) (l : nat) (z : rexp' V) :
  rexp' V' + (nat * rexp' V') :=
  match l with
    | O => inl (Rfixing' z rho vars)
    | S l' => match constFoldAcc' vars (adv_inp (-1) rho) f l' z with
                | inl (RLit _ r) => inl (Rfixing' f rho (PExtend r vars))
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.


Definition fixingRAcc {V V'} (f : Scope rexp' V) (l : nat) (z: rexp' V) (rho : obs) : PEnv Z V V' -> rexp' V' :=
  fun vars =>
    match constFoldAcc' vars rho f l z with
      | inl e => e
      | inr (l', e') => RAcc (Rfixing' f obs_empty (PSkip vars)) l' e'
    end.

Lemma fixingRAcc_def {V V'} (f : Scope rexp' V) (l : nat) (z: rexp' V) (rho : obs) (vars : PEnv Z V V') :
  Rfixing' (RAcc f l z) rho vars = fixingRAcc f l z rho vars.
Proof. admit.
  (* induction l. *)
  (* - reflexivity. *)
  (* - unfold fixingRAcc. simpl. *)
Qed.


Definition Rfixing (e : rexp) (o : obs) : rexp := Rfixing' e o (PEmpty (zero Z)).

Fixpoint subst {V V'} (e : rexp' V) : PEnv Z V V' -> rexp' V' :=
    match e with
      | RLit _ r => fun _ => RLit r
      | RBin _ op e1 e2 => fun vars => RBin op (subst e1 vars) (subst e2 vars)
      | RNeg _ e => fun vars => RNeg (subst e vars)
      | Obs _ obs t => fun _ => Obs obs t
      | RVar _ v => fun vars =>
                      match lookupPEnv vars v with
                        | inl r =>  RLit r
                        | inr v' => RVar v'
                      end
      | RAcc _ f l z => fun vars => RAcc (subst f (PSkip vars)) l (subst z vars)
    end.


Lemma Rfixing_complete' {V V'} e rho vars (pvars : PEnv Z V V') :
  R'[|Rfixing' e rho pvars|] vars obs_empty = R'[|subst e pvars|]vars rho.
Proof.
  generalize dependent rho. induction e; intros; auto.
  - simpl.
    remember (Rfixing' e1 rho pvars) as R1. pose (IHe1 pvars rho) as IH1.
    remember (Rfixing' e2 rho pvars) as R2. pose (IHe2 pvars rho) as IH2.
    rewrite <- HeqR1 in *. rewrite <- HeqR2 in *. rewrite <- IH1. rewrite <- IH2.
    destruct R1; destruct R2; reflexivity.
  - simpl. remember (Rfixing' e rho pvars) as R. pose (IHe pvars rho) as IH.
    rewrite <- HeqR in *. rewrite <- IH.
    destruct R; try reflexivity.
  - simpl. destruct (rho z o); reflexivity.
  - simpl. destruct (lookupPEnv pvars v); reflexivity.
  - rewrite fixingRAcc_def. generalize dependent rho. generalize dependent pvars. induction n; intros.
    + unfold fixingRAcc. simpl. rewrite IHe0. reflexivity.
    + unfold fixingRAcc.
      (* remember (constFoldAcc' pvars rho s (S n) e) as C. *)
      (* destruct C. simpl in HeqC. *)
      simpl.
      remember (constFoldAcc' pvars (adv_inp (-1) rho) s n e) as R.
      destruct R. destruct r. simpl.



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