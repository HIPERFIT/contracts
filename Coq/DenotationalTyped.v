(********** Denotational semantics preserves types  **********)

Require Import Equality.
Require Import Denotational.

Definition TypeEnv (g : TyEnv) (rho : Env) : Prop := forall_zip TypeVal' rho g.

Definition TypeArgs (ts : list Ty) (args : list Val) : Prop := forall_zip TypeVal args ts.


Lemma OpSem_typed' {A} op ts t (args : list A) (f : A -> option Val) :
|-Op op ∶ ts => t -> forall_zip (fun x t => |-V' (f x) ∶ t) args ts -> |-V' (mapM f args >>= OpSem op) ∶ t.
Proof.
  intros O T. induction O; 
  repeat (idtac; match goal with
      | [H : forall_zip _ _ _ |- _] => inversion H; clear H
      | [ |- context [match ?x with 
                      | _ => _ 
                    end]] => is_var x; destruct x
      | [ |- context [match ?x ?y with 
                      | _ => _ 
                    end]] => is_var x; is_var y; destruct (x y)
       
  end; subst; simpl; unfold liftM2, bind, pure,compose; auto).
Qed.

Lemma OpSem_typed_total {A} op ts t (args : list A) (f : A -> option Val) :
|-Op op ∶ ts => t -> forall_zip (fun x t => |-V' (f x) ∶ t /\ exists v, f x = Some v) args ts -> 
                     exists v, (mapM f args >>= OpSem op) = Some v.
Proof.
  intros O T. induction O;
  repeat (match goal with
      | [ H : _ /\ _ |- _ ] => 
        let H1 := fresh in let H2 := fresh in let H3 := fresh in
        let H4 := fresh in let H5 := fresh in let H6 := fresh in
        let H7 := fresh in
        destruct H as [H1 H2]; destruct H2 as [H3 H4]; rewrite H4 in *
      ; inversion H1 as [ H5 H6 H7| H5 ]; inversion H7
      | [H : forall_zip _ _ _ |- _] => inversion H; clear H
  end; subst; simpl; unfold liftM2, bind); eexists; auto.
Qed.

Lemma lookupEnv_typed g rho v t : TypeEnv g rho -> g |-X v ∶ t -> |-V' (lookupEnv v rho) ∶ t.
Proof.
  intros E V. generalize dependent rho. dependent induction V; intros.
  + simpl. inversion E. auto.
  + simpl. inversion E. apply IHV. auto.
Qed.

Theorem Esem_typed' g e t (rho : Env) (erho : ExtEnv) : 
  g |-E e ∶ t -> TypeEnv g rho -> TypeExt erho -> |-V' E'[|e|] rho erho ∶ t.
Proof.
  intros E R V'. generalize dependent rho. generalize dependent erho.
  dependent induction E using TypeExp_ind'; intros.
  + rewrite EsemOpE. eapply OpSem_typed'. apply H. 
    do 4 (eapply forall_zip_apply_dep in H1;eauto).  
  + apply V'. auto.
  + simpl. eapply lookupEnv_typed; eauto.
  + simpl. generalize dependent erho. induction n; intros.
    - simpl. auto.
    - apply IHE1. auto. constructor. 
      rewrite adv_ext_step. apply IHn. auto. auto.
Qed.

Corollary Esem_typed e t (erho : ExtEnv) : 
  nil |-E e ∶ t -> TypeExt erho -> |-V' E[|e|] erho ∶ t.
Proof.
  intros. eapply Esem_typed'; eauto. constructor.
Qed.

Definition total_ext (erho : ExtEnv) : Prop := forall l i, exists v, erho l i = Some v.

Lemma total_ext_adv d e : total_ext e -> total_ext (adv_ext d e).
Proof.
  unfold total_ext. intros. apply H.
Qed.

Hint Resolve total_ext_adv.

Definition total_env (rho : Env) : Prop := forall_list (fun x => exists v , x = Some v) rho.


Theorem Esem_typed_total' g e t (rho : Env) (erho : ExtEnv) : 
  total_env rho -> total_ext erho -> 
  g |-E e ∶ t -> TypeEnv g rho -> TypeExt erho -> exists v, E'[|e|] rho erho = Some v.
Proof.
  intros T' T E R V'. generalize dependent rho. generalize dependent erho.
  dependent induction E using TypeExp_ind'; intros.
  + rewrite EsemOpE in *. eapply OpSem_typed_total. apply H. 
    apply forall_zip_and. eapply forall_zip_impl in H0; auto.
    apply H0. intros. eapply Esem_typed'; eauto. 
    do 6 (eapply forall_zip_apply_dep in H1;eauto). 
  + apply T.
  + simpl. generalize dependent rho. 
    generalize dependent g. induction v; intros.
    - inversion H. subst. inversion R. subst. simpl.
      inversion T'. subst. auto.
    - simpl. inversion H. subst. inversion R. subst. eapply IHv. 
      apply H2. inversion T'. subst. auto. auto.
  + apply proj1 with (B:= |-V' E'[|Acc e1 n e2|] rho erho ∶ t).
    simpl. generalize dependent erho. induction n; intros.
    - simpl. split. apply IHE2; auto. eapply Esem_typed'; eauto.
    - rewrite adv_ext_step. split. apply IHE1; auto. constructor;auto. apply IHn; auto.
      constructor. eapply proj2. apply IHn; auto.
      auto. eapply Esem_typed'; eauto.
      constructor. eapply proj2. apply IHn; eauto. auto.
Qed.

Corollary Esem_typed_total e t (erho : ExtEnv) : 
  total_ext erho -> nil |-E e ∶ t -> TypeExt erho -> exists v, E[|e|] erho = Some v /\ |-V v ∶ t.
Proof.
  intros. pose H0 as H'. eapply Esem_typed_total' in H'; eauto. destruct H'.
  eexists. split; eauto. eapply Esem_typed in H0; eauto. rewrite H2 in *. inversion H0. 
  auto. constructor. constructor.
Qed.

Definition total_trace (t : trace) := forall i, exists v, t i = Some v.

Hint Unfold empty_trace empty_trans const_trace empty_trans 
     total_trace singleton_trace singleton_trans scale_trace scale_trans.

Theorem Csem_typed_total c (erho : ExtEnv) : 
  total_ext erho -> |-C c -> TypeExt erho -> total_trace (C[|c|] erho).
Proof.
  intros T C R. generalize dependent erho. unfold total_trace. induction C.
  + simpl. repeat autounfold. eauto.
  + simpl. repeat autounfold. intros. destruct i; eauto.
  + simpl. repeat autounfold. intros. unfold liftM2, bind.
    destruct (IHC erho T R i). 
    eapply Esem_typed_total in H; eauto. decompose [and ex] H.
    rewrite H2. inversion H3. simpl. rewrite  H0.
    unfold pure, compose. eauto.
  + intros. simpl. unfold delay_trace. destruct (leb d i).
    simpl. apply IHC; auto. autounfold; eauto.
  + intros. simpl. unfold add_trace, add_trans, liftM2, bind. 
    destruct (IHC1 erho T R i). rewrite H.
    destruct (IHC2 erho T R i). rewrite H0.
    unfold pure, compose. eauto.
  + simpl. induction d; intros.
    - simpl. eapply  Esem_typed_total in H; eauto. decompose [and ex] H.
      rewrite H1. inversion H2. destruct b; auto.
    - simpl. eapply  Esem_typed_total in H; eauto. decompose [and ex] H.
      rewrite H1. inversion H2. destruct b; auto. 
      unfold delay_trace. destruct (leb 1 i). apply IHd; eauto. autounfold. eauto.
Qed.