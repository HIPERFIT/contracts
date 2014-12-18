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


Lemma adv_exp_ext (env : Env) d (e : Exp) ext : 
  E[|adv_exp d e|] env ext = E[|e|] env (adv_ext d ext).
Proof.
  generalize dependent ext.   generalize dependent env. 
  induction e using Exp_ind';intros; 
  try solve [simpl; repeat rewr_assumption; reflexivity].
  rewrite adv_exp_ope. simpl. rewrite map_map.
  eapply all_apply with (p:= env) in H.
  eapply all_apply with (p:= ext) in H.
  apply map_rewrite in H. rewrite H. reflexivity.

  generalize dependent ext.   generalize dependent env. 
  simpl. unfold Fsem in *. induction d0; intros.
  - simpl. apply IHe2.
  - repeat rewrite adv_ext_step. simpl. rewrite IHd0. 
    repeat rewrite adv_ext_iter. apply bind_equals. 
    f_equal; try (f_equal; omega). f_equal.
    f_equal; try (f_equal;f_equal; omega). do 2 (apply functional_extensionality; intro).
    do 3 f_equal. apply functional_extensionality. intros. do 3 f_equal. omega. do 2 f_equal. omega.
    intros.    rewrite IHe1.
    repeat rewrite Zpos_P_of_succ_nat. do 2 f_equal. omega. rewrite <- adv_ext_0. f_equal.
    omega.
Qed.


Lemma adv_exp_type g d e t : g |-E e ∶ t -> g |-E adv_exp d e ∶ t.
Proof.
  intro T. generalize dependent g.  generalize dependent t. 
  induction e using Exp_ind'; intros; simpl; inversion T; subst; try auto.
  - econstructor. eassumption. eapply all_apply' in H. apply all_zip; eauto. 
Qed.