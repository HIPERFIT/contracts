Require Import Denotational.

(* advancing contracts and expressions *)

Fixpoint adv_rexp {n} (d : Z) (e : rexp' n) : rexp' n :=
  match e with
    | RLit _ r => RLit r
    | RBin _ op e1 e2 => RBin op (adv_rexp d e1) (adv_rexp d e2)
    | RNeg _ e' => RNeg (adv_rexp d e')
    | Obs _ o i => Obs o (d + i)%Z
    | RVar _ a => RVar a
    | RAcc _ f n z => RAcc (adv_rexp d f) n (adv_rexp d z)
  end.


Fixpoint adv_bexp (d : Z) (e : bexp) : bexp :=
  match e with
    | BLit b => BLit b
    | BChoice c i => BChoice c (d + i)
    | BOp op e1 e2 => BOp op (adv_bexp d e1) (adv_bexp d e2)
    | RCmp op e1 e2 => RCmp op (adv_rexp d e1) (adv_rexp d e2)
    | BNot e' => BNot (adv_bexp d e')
  end.



Lemma adv_rexp_obs A (vars : Env (option Z) A) d (e : rexp' A) rho : 
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

Lemma adv_rexp_env d e rho : R[|adv_rexp d e|](fst rho) = R[|e|](fst (adv_env d rho)).
Proof.
  destruct rho. simpl. apply adv_rexp_obs.
Qed.


Lemma adv_env_ch d rho : snd (adv_env d rho) = adv_inp d (snd rho).
Proof.
  unfold adv_env. destruct rho. reflexivity.
Qed.

Lemma adv_env_obs d rho : fst (adv_env d rho) = adv_inp d (fst rho).
Proof.
  unfold adv_env. destruct rho. reflexivity.
Qed.


Lemma adv_bexp_env d e rho : B[|adv_bexp d e|]rho = B[|e|](adv_env d rho).
Proof.
  induction e; simpl; try first [reflexivity | f_equal; assumption].
  rewrite adv_env_ch. reflexivity.
  repeat rewrite adv_rexp_obs. rewrite adv_env_obs. reflexivity.
Qed.
