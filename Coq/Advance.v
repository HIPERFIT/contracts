Require Import Denotational.
Require Import Tactics.
Require Import List.
Import ListNotations.
Require Import FunctionalExtensionality.
Require Import Typing.

(* advancing contracts and expressions *)

Fixpoint adv_exp (d : Z) (e : Exp) : Exp :=
  match e with
    | OpE op args => OpE op (map (adv_exp d) args)
    | Obs l i => Obs l (d + i)
    | VarE a => VarE a
    | Acc f n z => Acc (adv_exp d f) n (adv_exp d z)
  end.



Lemma adv_exp_ope d op args : adv_exp d (OpE op args) = OpE op (map (adv_exp d) args).
reflexivity. Qed.

Ltac rewr_assumption := idtac; match goal with
                          | [R:  _ |- _ ] => rewrite R
                        end.


Lemma adv_exp_ext' (vars : Env) d (e : Exp) rho : 
  E'[|adv_exp d e|] vars rho = E'[|e|] vars (adv_ext d rho).
Proof.
  generalize dependent rho.   generalize dependent vars. 
  induction e using Exp_ind';intros; 
  try solve [simpl; repeat rewr_assumption; reflexivity].
  rewrite adv_exp_ope. simpl. rewrite map_map.
  eapply forall_list_apply_dep with (p:= vars) in H.
  eapply forall_list_apply_dep with (p:= rho) in H.
  apply map_rewrite in H. rewrite H. reflexivity.

  generalize dependent rho.   generalize dependent vars. 
  simpl. induction d0; intros.
  - simpl. apply IHe2.
  - repeat rewrite adv_ext_step. simpl. rewrite IHd0. 
    repeat rewrite adv_ext_iter. apply bind_equals.      
    f_equal; try (f_equal; omega). f_equal.
    f_equal; try (f_equal;f_equal; omega). do 2 (apply functional_extensionality; intro).
    do 3 f_equal. omega. do 2 f_equal. omega. intros. rewrite IHe1.
    repeat rewrite Zpos_P_of_succ_nat. do 2 f_equal. omega. rewrite <- adv_ext_0. f_equal.
    omega.
Qed.

Lemma adv_exp_ext d (e : Exp) rho : E[|adv_exp d e|] rho = E[|e|] (adv_ext d rho).
Proof. apply adv_exp_ext'. Qed.


Lemma adv_exp_type g d e t : g |-E e ∶ t -> g |-E adv_exp d e ∶ t.
Proof.
  intro T. generalize dependent g. generalize dependent t. 
  induction e using Exp_ind'; intros; simpl; inversion T; subst; try auto.
  - econstructor. eassumption. eapply forall_list_apply_dep' in H. apply forall_list_zip; eauto. 
Qed.