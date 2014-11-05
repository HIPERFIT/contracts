Require Import Denotational.
Require Import Tactics.
Require Import List.
Import ListNotations.
Require Import FunctionalExtensionality.

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

Lemma mapM_map {A B C} (f : B -> option C) (g : A -> B) l : mapM f (map g l) = mapM (f ∘ g) l.
Proof.
  induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma mapM_rewrite {A B} (f g : A -> option B) l : forall_list (fun x => f x = g x) l -> mapM f l = mapM g l.
Proof.
  intros. induction l. reflexivity.
  inversion H. subst. simpl. rewrite IHl by auto. rewrite H2. reflexivity.
Qed.


Lemma forall_list_apply_dep {A} (P : Type) (p : P) (R : A -> P -> Prop) xs : 
  forall_list (fun x => forall (p:P), R x p) xs -> forall_list (fun x => R x p) xs.
Proof.
  intros F. induction F; auto.
Qed.


Lemma adv_exp_ext' (vars : Env) d (e : Exp) rho : 
  E'[|adv_exp d e|] vars rho = E'[|e|] vars (adv_ext d rho).
Proof.
  generalize dependent rho.   generalize dependent vars. 
  induction e using Exp_ind';intros; 
  try solve [simpl; repeat rewr_assumption; reflexivity].
  rewrite adv_exp_ope. do 2 rewrite EsemOpE. rewrite mapM_map. unfold compose.
  eapply forall_list_apply_dep with (p:= vars) in H.
  eapply forall_list_apply_dep with (p:= rho) in H.
  apply mapM_rewrite in H. rewrite H. reflexivity.

  generalize dependent rho.   generalize dependent vars. 
  simpl. induction d0; intros.
  - simpl. apply IHe2.
  - repeat rewrite adv_ext_step. simpl. rewrite IHd0. rewrite IHe1.
    repeat rewrite adv_ext_iter. f_equal; try (f_equal; omega). f_equal.
    f_equal; try (f_equal;f_equal; omega). do 2 (apply functional_extensionality; intro).
    do 3 f_equal. omega.
Qed.

Lemma adv_exp_ext d (e : Exp) rho : E[|adv_exp d e|] rho = E[|e|] (adv_ext d rho).
Proof. apply adv_exp_ext'. Qed.
