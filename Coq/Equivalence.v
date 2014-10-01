Require Export Denotational.
Require Import Advance.
Require Import FunctionalExtensionality.
Require Import Tactics.

(********** Equivalence of contracts **********)

(* Full equivalence. *)

Definition equiv (c1 c2 : contract) : Prop := 
  forall rho : ext, C[|c1|]rho = C[|c2|]rho.
Infix "≡" := equiv (at level 40).

(* [c1 ⊑ c2] iff the semantics of [c1] and [c2] coincidese "in all
places" that [c1]'s semantics is defined. *)

Definition lequiv (c1 c2 : contract) : Prop := 
  forall rho : ext, C[|c1|]rho ⊆ C[|c2|]rho.

Infix "⊑" := lequiv (at level 40).

Definition total (t : trace) : Prop :=
  forall i, t i <> None.

(* Partial equivalence: equivalence on the total fragment of the
semantics. *)

Definition wequiv (c1 c2 : contract) : Prop := 
  forall rho : ext, total (C[|c1|]rho) \/ total (C[|c2|]rho) -> 
                    C[|c1|]rho = C[|c2|]rho.


Infix "≃" := wequiv (at level 40).

(* We prove some equivalences. *)

(* First some lemmas and auxiliary definitions. *)

Lemma lequiv_total c1 c2 r : c1 ⊑ c2 -> total (C[|c1|]r) -> C[|c1|]r = C[|c2|]r.
Proof.
  unfold lequiv, total, lep. intros.   apply functional_extensionality. intro.
  remember (C[|c1|] r x) as C1. destruct C1. erewrite H. reflexivity. auto.
  symmetry in HeqC1. apply H0 in HeqC1. contradiction.
Qed.



Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Theorem transl_ifwithin e d t c1 c2 : 
  IfWithin (adv_exp (Z.of_nat d) e) t (Transl d c1) (Transl d c2) ⊑
  Transl d (IfWithin e t c1 c2).
Proof.
  unfold lequiv, lep. simpl. induction t; intros.
  simpl in *. rewrite adv_exp_ext in *. remember (E[|e|](adv_ext (Z.of_nat d) rho)) as b.
  destruct b. destruct t;  assumption. 
  unfold const_trace, bot_trans in H. inversion H.

  simpl in *.  rewrite adv_exp_ext in *. 
  remember (E[|e|](adv_ext (Z.of_nat d) rho)) as b. destruct b. destruct t0. assumption. 
  rewrite adv_ext_swap. rewrite delay_trace_swap. 
  unfold delay_trace at 1.
  unfold delay_trace at 1 in H. 
  remember (leb 1 i) as L. destruct L.
  apply IHt. apply H. assumption.

  unfold const_trace, bot_trans in H. inversion H.
Qed.

Lemma total_delay t d : total t <-> total (delay_trace d t).
Proof.
  split; unfold total, delay_trace; intros.
  
  remember (leb d i) as L. destruct L. apply H. unfold not. intro. tryfalse.

  pose (H (i + d)) as H'.
  assert (leb d (i + d) = true) as L by (apply leb_correct; omega).
  rewrite L in H'. assert (i + d - d = i) as E by omega. rewrite E in *. assumption.
  
Qed.

  
Lemma bot_trans_delay_at d : delay_trace d (const_trace bot_trans) d = None.
Proof.
  rewrite delay_trace_at. reflexivity.
Qed.

Lemma bot_trans_delay_total d : ~ total (delay_trace d (const_trace bot_trans)).
Proof.
  unfold not, total. intros.
  contradiction (H d (bot_trans_delay_at d)). 
Qed.


Theorem transl_ifwithin_wequiv e d t c1 c2 : 
  IfWithin (adv_exp (Z.of_nat d) e) t (Transl d c1) (Transl d c2) ≃
  Transl d (IfWithin e t c1 c2). 
Proof.
  unfold wequiv. intros. destruct H. apply lequiv_total. apply transl_ifwithin. assumption.
  
  
  unfold lequiv, lep. simpl. generalize dependent rho. induction t; intros.
  simpl in *. rewrite adv_exp_ext in *. remember (E[|e|](adv_ext (Z.of_nat d) rho)) as b.
  destruct b. destruct t; reflexivity.
  unfold total in H. 
  contradiction (H d (bot_trans_delay_at d)). 

  simpl in *.  rewrite adv_exp_ext in *. 
  remember (E[|e|](adv_ext (Z.of_nat d) rho)) as b. destruct b. destruct t0. reflexivity.
  rewrite adv_ext_swap. rewrite delay_trace_swap. 
  rewrite IHt. reflexivity. rewrite delay_trace_swap in H. rewrite adv_ext_swap.
  apply total_delay in H. assumption. apply bot_trans_delay_total in H. contradiction.
Qed.
