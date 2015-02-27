(********** Translating Expressions in Time **********)

(* This module defines the operation [translateExp] on expressions,
which corresponds to the [Translate] constructs on contracts. In
contrast to [Translate], however, [translateExp] works on [Z] instead of
only on [nat]. *)

Require Import Denotational.
Require Import Tactics.
Require Import Typing.
Require Import FunctionalExtensionality.

Fixpoint translateExp (d : Z) (e : Exp) : Exp :=
  match e with
    | OpE op args => OpE op (map (translateExp d) args)
    | Obs l i => Obs l (d + i)
    | VarE a => VarE a
    | Acc f n z => Acc (translateExp d f) n (translateExp d z)
  end.



Lemma translateExp_ope d op args : translateExp d (OpE op args) = OpE op (map (translateExp d) args).
reflexivity. Qed.

Ltac rewr_assumption := idtac; match goal with
                          | [R:  _ |- _ ] => rewrite R
                        end.


Lemma translateExp_ext (env : Env) d (e : Exp) ext : 
  E[|translateExp d e|] env ext = E[|e|] env (adv_ext d ext).
Proof.
  generalize dependent ext.   generalize dependent env. 
  induction e using Exp_ind';intros; 
  try solve [simpl; repeat rewr_assumption; reflexivity].
  rewrite translateExp_ope. simpl. rewrite map_map.
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

Open Scope Z.

Lemma translateExp_ext_opp (env : Env) (d d' : Z) (e : Exp) (ext : ExtEnv):
  d' + d = 0 -> E[|translateExp d e|] env (adv_ext d' ext) = E[|e|] env ext.
Proof.
  intro H. rewrite translateExp_ext. rewrite adv_ext_opp; auto.
Qed.


Lemma translateExp_type g d e t : g |-E e ∶ t -> g |-E translateExp d e ∶ t.
Proof.
  intro T. generalize dependent g.  generalize dependent t. 
  induction e using Exp_ind'; intros; simpl; inversion T; subst; auto.
  - econstructor. eassumption. eapply all_apply' in H. apply all_zip; eauto. 
Qed.
