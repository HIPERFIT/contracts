Require Export ZArith.
Require Export Syntax.
Require Import FunctionalExtensionality.
Require Import Tactics.

(* External environments map observables to values. [ExtEnv'] is
parametrised over the type of values so that we can instantiate it
later to partial environments. *)

Definition ExtEnv' A := ObsLabel -> Z -> A.



Open Scope Z.

(* Move external environments into the future. *)

Definition adv_ext {A} (d : Z) (e : ExtEnv' A) : ExtEnv' A
  := fun l x => e l (d + x)%Z.

Lemma adv_ext_0 {A} (e : ExtEnv' A) : adv_ext 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_ext. reflexivity.
Qed.

Lemma adv_ext_iter {A} d d' (e : ExtEnv' A) : adv_ext d (adv_ext d' e) = adv_ext (d' + d) e.
Proof.
  apply functional_extensionality. intro. apply functional_extensionality. induction d'; intros.
  - simpl. rewrite adv_ext_0. reflexivity.
  - simpl. unfold adv_ext in *.  rewrite Z.add_assoc. reflexivity.
  - unfold adv_ext. rewrite Z.add_assoc.  reflexivity.
Qed.

Lemma adv_ext_iter' {A} d d' (e : ExtEnv' A) : adv_ext d (adv_ext d' e) = adv_ext (d + d') e.
Proof.
  apply functional_extensionality. intro. apply functional_extensionality. destruct d; intros;
  unfold adv_ext; f_equal; omega.
Qed.

Lemma adv_ext_opp {A} d d' (e : ExtEnv' A) : d' + d = 0 -> adv_ext d (adv_ext d' e) = e.
Proof.
  intros. rewrite adv_ext_iter. rewrite H. apply adv_ext_0.
Qed.


Lemma adv_ext_swap {A} d d' (e : ExtEnv' A) : 
  adv_ext d (adv_ext d' e) = adv_ext d' (adv_ext d e).
Proof.
  repeat rewrite adv_ext_iter. rewrite Z.add_comm. reflexivity.
Qed.

Lemma adv_ext_step {A} n (ext : ExtEnv' A) : 
  ((adv_ext (- Z.of_nat (S n)) ext) = (adv_ext (- Z.of_nat n) (adv_ext (-1) ext))).
Proof.
  rewrite adv_ext_iter. f_equal. rewrite Nat2Z.inj_succ. omega.
Qed.

Lemma Zneg_of_succ_nat : forall n, Z.neg (Pos.of_succ_nat n) = (- Z.of_nat (S n))%Z.
Proof.
  intros. rewrite <- Pos2Z.opp_pos. rewrite Zpos_P_of_succ_nat. rewrite Nat2Z.inj_succ. reflexivity.
Qed.

Lemma adv_ext_step' {A} n (ext : ExtEnv' A) : ((adv_ext (Z.neg (Pos.of_succ_nat n)) ext) 
                                               = (adv_ext (- Z.of_nat n) (adv_ext (-1) ext))).
Proof.
  rewrite Zneg_of_succ_nat. apply adv_ext_step.
Qed.


Definition Env' A := list A.


Fixpoint lookupEnv {A} (v : Var) (env : Env' A) : option A :=
  match v, env with
    | V1, x::_ => Some x
    | VS v, _::xs => lookupEnv v xs
    | _,_ => None
  end.
