(********** Denotational semantics preserves types  **********)
(**********    (and is total on typed contracts)    **********)

Require Import Equality.
Require Import Denotational.


(* Typing of values *)

Reserved Notation "'|-V' e '∶' t" (at level 20).

Inductive TypeVal : Val -> Ty -> Prop := 
| type_bool b : |-V BVal b ∶ BOOL
| type_real b : |-V RVal b ∶ REAL
        where "'|-V' v '∶' t" := (TypeVal v t).

(* Typing of partial values *)

Reserved Notation "'|-V'' e '∶' t" (at level 20).

Inductive TypeVal' : option Val -> Ty -> Prop := 
| type_some v t : |-V v ∶ t -> |-V' Some v ∶ t
| type_none t : |-V' None ∶ t
        where "'|-V'' v '∶' t" := (TypeVal' v t).

Hint Constructors TypeVal TypeVal'.

(* Typing of external environments *)

Definition TypeExt (ext : ExtEnv) := forall z l t, |-O l ∶ t -> |-V (ext l z)  ∶ t.

Lemma adv_ext_type e d : TypeExt e -> TypeExt (adv_ext d e).
Proof.
  unfold TypeExt, adv_ext. intros. auto.
Qed.

Hint Resolve adv_ext_type.

(* Typing of environments *)

Definition TypeEnv (g : TyEnv) (env : Env) : Prop := all2 TypeVal env g.

Hint Unfold TypeEnv.

(* Typing of arguments (to an operation). *)

Definition TypeArgs (ts : list Ty) (args : list Val) : Prop := all2 TypeVal args ts.


Lemma OpSem_typed_total {A} op ts t (args : list A) (f : A -> option Val) :
|-Op op ∶ ts => t -> all2 (fun x t => exists v, f x = Some v /\ |-V v ∶ t) args ts -> 
                     exists v, (mapM f args >>= OpSem op) = Some v /\ |-V v ∶ t.
Proof.
  intros O T. induction O;
  repeat (match goal with
      | [ H : exists _, _ /\ _ |- _ ] => 
        let H1 := fresh in let H2 := fresh in let H3 := fresh in
        let H4 := fresh in
        destruct H as [H1 H2]; destruct H2 as [H3 H4]; rewrite H3 in *; inversion H4
      | [H : all2 _ _ _ |- _] => inversion H; clear H
  end; subst; simpl; unfold liftM2, bind); eexists; auto.
Qed.


(* The denotational semantics of expressions is total and produces
values of the correct type. *)

Theorem Esem_typed_total g e t (env : Env) (ext : ExtEnv) : 
  g |-E e ∶ t -> TypeEnv g env -> TypeExt ext -> (exists v, E[|e|] env ext = Some v /\ |-V v ∶ t).
Proof.
  intros E R V'. generalize dependent env. generalize dependent ext.
  dependent induction E using TypeExp_ind'; intros.
  + simpl. rewrite sequence_map. eapply OpSem_typed_total. apply H.
    do 4 (eapply all2_apply in H1;eauto). 
  + simpl. eauto.
  + simpl. generalize dependent env. 
    generalize dependent g. induction v; intros.
    - inversion H. subst. inversion R. subst. simpl. eauto.
    - simpl. inversion H. subst. inversion R. subst. eapply IHv. 
      apply H2. auto.
  + simpl. eapply Acc_sem_ind. intros. decompose [ex and] H. subst.
    simpl. apply IHE1; auto. apply IHE2; auto.
Qed.


Definition total_trace (t : option Trace) := exists v, t = Some v.

Hint Unfold empty_trace empty_trans const_trace empty_trans 
     total_trace singleton_trace singleton_trans scale_trace scale_trans.


(* The denotational semantics of contracts is total. *)


Theorem Csem_typed_total c g (env: Env) (ext : ExtEnv) : 
 g |-C c -> TypeEnv g env -> TypeExt ext -> total_trace (C[|c|] env ext).
Proof.
  intros C T R. generalize dependent env. generalize dependent ext. generalize dependent g.
  unfold total_trace. induction c.
  + simpl. repeat autounfold. eauto.
  + simpl. repeat autounfold. intros. inversion C; subst. clear C. 
    eapply Esem_typed_total in H2; eauto. decompose [ex and] H2. rewrite H0.
    assert (TypeEnv (t :: g) (x :: env)) as T'. constructor; auto.
    destruct (IHc (t :: g) H3 ext R (x :: env) T'). simpl. rewrite H. eauto.
  + simpl. repeat autounfold. intros. eauto.
  + simpl. repeat autounfold. intros. unfold liftM2, bind.
    inversion C. subst. destruct (IHc g H3 ext R env T). 
    eapply Esem_typed_total in H2; eauto. decompose [and ex] H2.
    rewrite H1. inversion H4. simpl. rewrite  H.
    unfold pure, compose. eauto. 
  + intros. simpl. unfold delay_trace. inversion C; subst. 
    assert (TypeExt (adv_ext (Z.of_nat n) ext)) as R' by auto.
    destruct (IHc g H1 (adv_ext (Z.of_nat n) ext) R' env T).
    rewrite H. simpl. autounfold; eauto.
  + intros. simpl. unfold add_trace, add_trans, liftM2, bind. inversion C; subst.
    destruct (IHc1 g H2 ext R env T). rewrite H.
    destruct (IHc2 g H3 ext R env T). rewrite H0.
    unfold pure, compose. eauto.
  + simpl. induction n; intros;inversion C; subst.
    - simpl. eapply  Esem_typed_total in H3; eauto. decompose [and ex] H3.
      rewrite H0. inversion H1. destruct b; eauto. 
    - simpl. eapply  Esem_typed_total in H3; eauto. decompose [and ex] H3.
      rewrite H0. inversion H1. destruct b; eauto. 
      assert (TypeExt (adv_ext 1 ext)) as R' by auto.
      assert (g |-C If e n c1 c2) as C' by (inversion C; constructor;auto).
      destruct (IHn g C' (adv_ext 1 ext) R' env T).
      rewrite H2. simpl. autounfold. eauto.
Qed.