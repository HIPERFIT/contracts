Require Import Denotational.

(* advancing contracts and expressions *)

Fixpoint adv_rexp (d : Z) (e : rexp) : rexp :=
  match e with
    | RLit r => RLit r
    | RBin op e1 e2 => RBin op (adv_rexp d e1) (adv_rexp d e2)
    | RNeg e' => RNeg (adv_rexp d e')
    | Obs o i => Obs o (d + i)%Z
  end.

Fixpoint adv_bexp (d : Z) (e : bexp) : bexp :=
  match e with
    | BLit b => BLit b
    | BChoice c i => BChoice c (d + i)
    | BOp op e1 e2 => BOp op (adv_bexp d e1) (adv_bexp d e2)
    | RCmp op e1 e2 => RCmp op (adv_rexp d e1) (adv_rexp d e2)
    | BNot e' => BNot (adv_bexp d e')
  end.


Lemma adv_rexp_obs d e rho : R[|adv_rexp d e|]rho = R[|e|](adv_inp d rho).
Proof.
  induction e; simpl; first [reflexivity | f_equal; assumption].
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
