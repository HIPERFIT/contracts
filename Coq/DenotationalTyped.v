(********** Denotational semantics preserves types  **********)

Require Import Equality.
Require Import Denotational.

Definition TypeEnv (g : TyEnv) (rho : Env) : Prop := forall_zip TypeVal rho g.

Definition TypeArgs (ts : list Ty) (args : list Val) : Prop := forall_zip TypeVal args ts.


Lemma OpSem_typed_total {A} op ts t (args : list A) (f : A -> option Val) :
|-Op op ∶ ts => t -> forall_zip (fun x t => exists v, f x = Some v /\ |-V v ∶ t) args ts -> 
                     exists v, (mapM f args >>= OpSem op) = Some v /\ |-V v ∶ t.
Proof.
  intros O T. induction O;
  repeat (match goal with
      | [ H : exists _, _ /\ _ |- _ ] => 
        let H1 := fresh in let H2 := fresh in let H3 := fresh in
        let H4 := fresh in
        destruct H as [H1 H2]; destruct H2 as [H3 H4]; rewrite H3 in *; inversion H4
      | [H : forall_zip _ _ _ |- _] => inversion H; clear H
  end; subst; simpl; unfold liftM2, bind); eexists; auto.
Qed.


(* The denotational semantics of expressions is total and produces
values of the correct type. *)

Theorem Esem_typed_total g e t (rho : Env) (erho : ExtEnv) : 
  g |-E e ∶ t -> TypeEnv g rho -> TypeExt erho -> (exists v, E'[|e|] rho erho = Some v /\ |-V v ∶ t).
Proof.
  intros E R V'. generalize dependent rho. generalize dependent erho.
  dependent induction E using TypeExp_ind'; intros.
  + simpl. rewrite sequence_map. eapply OpSem_typed_total. apply H.
    do 4 (eapply forall_zip_apply_dep in H1;eauto). 
  + simpl. eauto.
  + simpl. generalize dependent rho. 
    generalize dependent g. induction v; intros.
    - inversion H. subst. inversion R. subst. simpl. eauto.
    - simpl. inversion H. subst. inversion R. subst. eapply IHv. 
      apply H2. auto.
  + simpl. eapply Acc_sem_ind. intros. apply IHE1. auto. decompose [ex and] H. 
    inversion H1. subst. constructor;auto. apply IHE2; auto.
Qed.


Definition total_trace (t : trace) := forall i, exists v, t i = Some v.

Hint Unfold empty_trace empty_trans const_trace empty_trans 
     total_trace singleton_trace singleton_trans scale_trace scale_trans.


(* The denotational semantics of contracts is total. *)


Theorem Csem_typed_total c (erho : ExtEnv) : 
  |-C c -> TypeExt erho -> total_trace (C[|c|] erho).
Proof.
  intros C R. generalize dependent erho. unfold total_trace. induction C.
  + simpl. repeat autounfold. eauto.
  + simpl. repeat autounfold. intros. destruct i; eauto.
  + simpl. repeat autounfold. intros. unfold liftM2, bind.
    destruct (IHC erho R i). 
    eapply Esem_typed_total in H; eauto. decompose [and ex] H.
    rewrite H2. inversion H3. simpl. rewrite  H0.
    unfold pure, compose. eauto. constructor.
  + intros. simpl. unfold delay_trace. destruct (leb d i).
    simpl. apply IHC; auto. autounfold; eauto.
  + intros. simpl. unfold add_trace, add_trans, liftM2, bind. 
    destruct (IHC1 erho R i). rewrite H.
    destruct (IHC2 erho R i). rewrite H0.
    unfold pure, compose. eauto.
  + simpl. induction d; intros.
    - simpl. eapply  Esem_typed_total in H; eauto. decompose [and ex] H.
      rewrite H1. inversion H2. destruct b; auto. constructor.
    - simpl. eapply  Esem_typed_total in H; eauto. decompose [and ex] H.
      rewrite H1. inversion H2. destruct b; auto. 
      unfold delay_trace. destruct (leb 1 i). apply IHd; eauto. autounfold. eauto. constructor.
Qed.