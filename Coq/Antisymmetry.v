(********** Antisymmetry of the denotational semantics **********)

Require Import Denotational.
Require Import Tactics.

Definition antisym' (t : trans) : Prop := forall p1 p2 c, t p1 p2 c = - t p2 p1 c.
Definition antisym (t : transfers) : Prop := forall t', t = Some t' -> antisym' t'.
Definition antisym_trace (t : trace) : Prop := forall i, antisym (t i).
Definition antisym_trace' (t : ExtEnv -> trace) : Prop := forall rho, antisym_trace (t rho).


Hint Resolve Ropp_0 Ropp_involutive.

Lemma empty_trans_antisym' : antisym' empty_trans'.
Proof.
  unfold antisym', empty_trans'. auto.
Qed.

Lemma empty_trans_antisym : antisym empty_trans.
Proof.
  unfold antisym, empty_trans. intros. inversion H. apply empty_trans_antisym'.
Qed.

Lemma const_trace_antisym t : antisym t -> antisym_trace (const_trace t).
Proof.
  unfold antisym_trace. auto.
Qed.


Lemma singleton_trans_antisym' p1 p2 c r : antisym' (singleton_trans' p1 p2 c r).
Proof.
  unfold antisym', singleton_trans'.
  intros. remember (eq_str p1 p2) as E0. 
  destruct E0. auto.
  remember (eq_str p1 p0 && eq_str p2 p3 && eq_str c c0) as E1. destruct E1.
  symmetry in HeqE1. repeat rewrite Bool.andb_true_iff in *. repeat rewrite eq_str_iff in *.
  decompose [and] HeqE1. remember (eq_str p1 p3 && eq_str p2 p0) as E2. destruct E2. 
  symmetry in HeqE2. repeat rewrite Bool.andb_true_iff in *. repeat rewrite eq_str_iff in *.
  destruct HeqE2. assert (p1 = p2) by (subst; auto). rewrite <- eq_str_iff in H4. tryfalse.
  simpl. auto. destruct (eq_str p1 p3 && eq_str p2 p0 && eq_str c c0); auto.
Qed.

Lemma singleton_trans_antisym p1 p2 c r : antisym (singleton_trans p1 p2 c r).
Proof.
  unfold antisym, empty_trans. intros. inversion H. apply singleton_trans_antisym'.
Qed.

Lemma singleton_trace_antisym p1 p2 c r : antisym_trace (singleton_trace (singleton_trans p1 p2 c r)).
Proof.
  unfold antisym_trace, singleton_trace. intros. destruct i. 
  apply singleton_trans_antisym. apply empty_trans_antisym.
Qed.


Lemma scale_trans_antisym' r t : antisym' t -> antisym' (scale_trans' r t).
Proof.
  unfold antisym', scale_trans'. intros. rewrite H. apply Ropp_mult_distr_l_reverse.
Qed.

Lemma scale_trans_antisym r t : antisym t -> antisym (scale_trans r t).
Proof.
  unfold antisym, scale_trans. intros. destruct r; destruct t; simpl in H0; inversion H0.
  apply scale_trans_antisym'. auto.
Qed.

Lemma scale_trace_antisym r t : antisym_trace t -> antisym_trace (scale_trace r t).
Proof.
  unfold antisym_trace, scale_trace, compose. intros. apply scale_trans_antisym. apply H.
Qed.


Lemma add_trans_antisym' t1 t2: antisym' t1 -> antisym' t2 -> antisym' (add_trans' t1 t2).
Proof.
  unfold antisym', add_trans'. intros. rewrite H. rewrite H0. rewrite Ropp_plus_distr. reflexivity.
Qed.

Lemma add_trans_antisym t1 t2: antisym t1 -> antisym t2 -> antisym (add_trans t1 t2).
Proof.
  unfold antisym, add_trans. intros. destruct t1; destruct t2; simpl in H1; inversion H1.
  apply add_trans_antisym'; auto.
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


Lemma bot_trans_antisym : antisym bot_trans.
Proof.
  unfold antisym, bot_trans. intros. inversion H.
Qed.


Hint Resolve const_trace_antisym add_trace_antisym delay_trace_antisym 
     scale_trace_antisym singleton_trace_antisym bot_trans_antisym empty_trans_antisym.

Lemma within_trace_antisym t1 t2 b rho n : antisym_trace' t1 -> antisym_trace' t2 -> 
                                           antisym_trace (within_sem t1 t2 b rho n).
Proof.
  intros. generalize dependent rho. induction n; intros; simpl;
                                    destruct (E[|b|]rho); try destruct v; try destruct b0; auto.
 Qed.

Hint Resolve within_trace_antisym.


Theorem sem_antisym c rho : antisym_trace (C[| c |]rho).
Proof.
  generalize dependent rho. induction c; intros; simpl; unfold empty_trace; auto. 
Qed.