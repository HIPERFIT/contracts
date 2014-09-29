Require Import Denotational.

(* advancing contracts and expressions *)

Fixpoint adv_rexp {V} (d : Z) (e : rexp' V) : rexp' V :=
  match e with
    | RLit _ r => RLit r
    | RBin _ op e1 e2 => RBin op (adv_rexp d e1) (adv_rexp d e2)
    | RNeg _ e' => RNeg (adv_rexp d e')
    | Obs _ o i => Obs o (d + i)%Z
    | RVar _ a => RVar a
    | RAcc _ f n z => RAcc (adv_rexp d f) n (adv_rexp d z)
  end.


Fixpoint adv_bexp {V} (d : Z) (e : bexp' V) : bexp' V :=
  match e with
    | BLit _ b => BLit b
    | BChoice _ c i => BChoice c (d + i)
    | BOp _ op e1 e2 => BOp op (adv_bexp d e1) (adv_bexp d e2)
    | RCmp _ op e1 e2 => RCmp op (adv_rexp d e1) (adv_rexp d e2)
    | BNot _ e' => BNot (adv_bexp d e')
    | BVar _ a => BVar a
    | BAcc _ f n z => BAcc (adv_bexp d f) n (adv_bexp d z)
  end.



Lemma adv_rexp_obs' A (vars : Env (option R) A) d (e : rexp' A) rho : 
  R'[|adv_rexp d e|] vars rho = R'[|e|] vars (adv_inp d rho).
Proof.
  generalize dependent rho. induction e;intros; simpl; first [reflexivity | f_equal; assumption | auto].
  rewrite IHe1. rewrite IHe2. reflexivity.
  rewrite IHe. reflexivity.

  assert (adv_inp (- Z.of_nat n) (adv_inp d rho) = adv_inp d (adv_inp (- Z.of_nat n) rho)) as J.
  repeat rewrite adv_inp_iter. f_equal. omega.
  rewrite J. remember (adv_inp (- Z.of_nat n) rho) as rho'. 
  clear Heqrho' J.
  induction n.
  - simpl. apply IHe0.
  - intros. simpl. rewrite IHn. rewrite adv_inp_swap. apply IHe. 
Qed.

Lemma adv_rexp_obs d (e : rexp) rho : R[|adv_rexp d e|] rho = R[|e|] (adv_inp d rho).
Proof. apply adv_rexp_obs'. Qed.

Lemma adv_rexp_ext d e rho : R[|adv_rexp d e|](fst rho) = R[|e|](fst (adv_ext d rho)).
Proof.
  destruct rho. simpl. apply adv_rexp_obs.
Qed.


Lemma adv_ext_ch d rho : snd (adv_ext d rho) = adv_inp d (snd rho).
Proof.
  unfold adv_ext. destruct rho. reflexivity.
Qed.

Lemma adv_ext_obs d rho : fst (adv_ext d rho) = adv_inp d (fst rho).
Proof.
  unfold adv_ext. destruct rho. reflexivity.
Qed.


Lemma adv_bexp_ext' {V} d (e : bexp' V) vars rho : B'[|adv_bexp d e|]vars rho = B'[|e|] vars (adv_ext d rho).
Proof.
  generalize dependent rho. induction e;intros; simpl; try first [reflexivity | f_equal; assumption].
  - rewrite adv_ext_ch. reflexivity.
  - repeat rewrite adv_rexp_obs. rewrite adv_ext_obs. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - assert (adv_ext (- Z.of_nat n) (adv_ext d rho) = adv_ext d (adv_ext (- Z.of_nat n) rho)) as J.
    repeat rewrite adv_ext_iter. f_equal. omega.
    rewrite J. remember (adv_ext (- Z.of_nat n) rho) as rho'. 
    clear Heqrho' J.
    induction n.
    + simpl. apply IHe0.
    + intros. simpl. rewrite IHn. rewrite adv_ext_swap. apply IHe.
Qed.

Lemma adv_bexp_ext d (e : bexp) rho : B[|adv_bexp d e|] rho = B[|e|] (adv_ext d rho).
Proof. apply adv_bexp_ext'. Qed.