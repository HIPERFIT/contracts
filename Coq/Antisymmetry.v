(********** Antisymmetry of the denotational semantics **********)

Require Import Denotational.
Require Import Tactics.

Definition antisym (t : Trans) : Prop := forall p1 p2 c, t p1 p2 c = - t p2 p1 c.
Definition antisym_trace (t : Trace) : Prop := forall i, antisym (t i).
Definition antisym_trace' (t : Env -> ExtEnv -> option Trace) : Prop := 
  forall env ext t', t env ext = Some t' -> antisym_trace t'.


Hint Resolve Ropp_0 Ropp_involutive.

Lemma empty_trans_antisym : antisym empty_trans.
Proof.
  unfold antisym, empty_trans. auto.
Qed.


Lemma const_trace_antisym t : antisym t -> antisym_trace (const_trace t).
Proof.
  unfold antisym_trace. auto.
Qed.


Lemma singleton_trans_antisym p1 p2 c r : antisym (singleton_trans p1 p2 c r).
Proof.
  unfold antisym, singleton_trans.
  intros. remember (Party.eqb p1 p2) as E0.
  destruct E0. auto.
  remember (Party.eqb p1 p0 && Party.eqb p2 p3 && Asset.eqb c c0) as E1. destruct E1.
  symmetry in HeqE1. repeat rewrite Bool.andb_true_iff in *. repeat rewrite Party.eqb_eq in *.
  rewrite Asset.eqb_eq in *.
  decompose [and] HeqE1. remember (Party.eqb p1 p3 && Party.eqb p2 p0 && Asset.eqb c c0) as E2. destruct E2.
  symmetry in HeqE2. repeat rewrite Bool.andb_true_iff in *. repeat rewrite Party.eqb_eq in *.
  rewrite Asset.eqb_eq in *.
  decompose [and] HeqE2.  assert (p1 = p2) by (subst; auto).
  rewrite <- Party.eqb_eq in H4. tryfalse.
  simpl. auto. destruct (Party.eqb p1 p3 && Party.eqb p2 p0 && Asset.eqb c c0); auto.
Qed.

Lemma singleton_trace_antisym p1 p2 c r : antisym_trace (singleton_trace (singleton_trans p1 p2 c r)).
Proof.
  unfold antisym_trace, singleton_trace. intros. destruct i. 
  apply singleton_trans_antisym. apply empty_trans_antisym.
Qed.


Lemma scale_trans_antisym r t : antisym t -> antisym (scale_trans r t).
Proof.
  unfold antisym, scale_trans. intros. rewrite H. apply Ropp_mult_distr_l_reverse.
Qed.


Lemma scale_trace_antisym r t : antisym_trace t -> antisym_trace (scale_trace r t).
Proof.
  unfold antisym_trace, scale_trace, compose. intros. apply scale_trans_antisym. apply H.
Qed.


Lemma add_trans_antisym t1 t2: antisym t1 -> antisym t2 -> antisym (add_trans t1 t2).
Proof.
  unfold antisym, add_trans. intros. rewrite H. rewrite H0. rewrite Ropp_plus_distr. reflexivity.
Qed.


Lemma add_trace_antisym t1 t2: antisym_trace t1 -> antisym_trace t2 -> antisym_trace (add_trace t1 t2).
Proof.
  unfold antisym_trace, add_trace. intros. apply add_trans_antisym; auto.
Qed.

Lemma delay_trace_antisym d t : antisym_trace t -> antisym_trace (delay_trace d t).
Proof.
  unfold antisym_trace, delay_trace. intros. destruct (leb d i). 
  apply H. apply empty_trans_antisym.
Qed.



Hint Resolve const_trace_antisym add_trace_antisym delay_trace_antisym 
     scale_trace_antisym singleton_trace_antisym empty_trans_antisym.

Lemma within_trace_antisym t1 t2 b n : antisym_trace' t1 -> antisym_trace' t2 -> 
                                       antisym_trace' (within_sem t1 t2 b n).
Proof.
  intros T1 T2. intros. induction n; unfold antisym_trace'; intros; simpl in *;
  destruct (E[|b|]env ext); try destruct v; try destruct b0; eauto;tryfalse.
  apply liftM_some in H. decompose [ex and] H. subst. apply delay_trace_antisym.
  eauto.
 Qed.

Hint Resolve within_trace_antisym.


Theorem sem_antisym c : antisym_trace' (C[| c |]).
Proof.
  
  induction c; try solve[unfold antisym_trace'; intros; simpl in *; 
                         first[progress option_inv_auto| inversion H]; subst; unfold empty_trace; eauto].
  
  simpl. apply within_trace_antisym; auto.
Qed.