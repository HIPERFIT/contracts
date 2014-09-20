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

Fixpoint lift {n} (e : rexp' n) : rexp' (S n) :=
  match e with
    | RLit _ r => RLit r
    | RBin n op e1 e2 => RBin op (lift e1) (lift e2)
    | RNeg _ e' => RNeg (lift e')
    | Obs _ obs t =>  Obs obs t
    | RVar _ i => RVar (FS i)
    | RAcc _ f l z => RAcc (lift f) l (lift z)
end.

(* Substitution (not capture avoiding!) *)
Fixpoint subst {n m} (e : rexp' n) : vector (rexp' m) n -> rexp' m :=
  match e with
    | RLit _ r => fun s => RLit r
    | RBin n op e1 e2 =>  fun s => RBin op (subst e1 s) (subst e2 s)
    | RNeg _ e' => fun s => RNeg (subst e' s)
    | Obs _ obs t => fun s => Obs obs t
    | RVar _ i => fun s => nth s i
    | RAcc _ f l z => fun s => RAcc (subst f (RVar F1 :: vmap lift s)) l (subst z s)
end.

Fixpoint mkvector {A} (n : nat) : (fin n -> A) -> vector A n :=
  match n with
    | O => fun f => vnil A
    | S n => fun f => f F1 :: mkvector n (f ∘ FS)
  end.

Lemma mkvector_nth A n f i : nth (@mkvector A n f) i = f i.
Proof.
  generalize dependent n. induction i.
  - reflexivity.
  - simpl. rewrite IHi. reflexivity.
Qed.

Definition constSubst {n} (r : Z) (e : rexp' (S n)) : rexp' n 
  :=  subst e (RLit r :: mkvector n RVar).

Fixpoint constFoldAcc {n} (f : nat -> Z -> rexp' n)  (l : nat) (z : rexp' n) : 
  rexp' n + (nat * rexp' n) :=
  match l with
    | O => inl z
    | S l' => match constFoldAcc f l' z with
                | inl (RLit _ r) => inl (f l r)
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.


                   
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
      | RAcc _ f l z => let rho' := adv_inp (0 - Z.of_nat l) rho in
                        let f' i z := Rfixing (constSubst z f) (adv_inp (Z.of_nat i)  rho')
                        in match constFoldAcc f' l (Rfixing z rho') with
                             | inl e => e
                             | inr (l', e') => RAcc f l' e'
                           end
    end.