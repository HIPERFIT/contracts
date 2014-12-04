Require Export Denotational.
Require Import Advance.
Require Import FunctionalExtensionality.
Require Import Tactics.

Require Import DenotationalTyped.

(********** Equivalence of contracts **********)

(* Full equivalence. *)

Definition equiv (c1 c2 : Contr) : Prop := 
  forall (rho : ExtEnv), TypeExt rho -> C[|c1|]nil rho = C[|c2|]nil rho.
Infix "≡" := equiv (at level 40).

(* [c1 ⊑ c2] iff the semantics of [c1] and [c2] coincidese "in all
places" that [c1]'s semantics is defined. *)

Definition lequiv (c1 c2 : Contr) : Prop := 
  forall rho : ExtEnv, C[|c1|]nil rho ⊆ C[|c2|]nil rho.

Infix "⊑" := lequiv (at level 40).


Lemma lequiv_total c1 c2 vars r : total_trace (C[|c1|]vars r) -> c1 ⊑ c2 -> C[|c1|]vars r = C[|c2|]vars r.
Proof.
  unfold lequiv, total_trace, lep. intros T S.   apply functional_extensionality. intro.
  remember (C[|c1|] vars r x) as C1. destruct C1. erewrite S. reflexivity. auto.
  symmetry in HeqC1. pose (T x) as HH. destruct HH. tryfalse.
Qed.

Lemma lequiv_typed c1 c2 : |-C c1 -> c1 ⊑ c2 -> c1 ≡ c2.
Proof. 
  unfold equiv. intros T S r E. eapply Csem_typed_total in T. apply lequiv_total; auto. assumption.
Qed.

Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Theorem transl_ifwithin e d t c1 c2 : 
  If (adv_exp (Z.of_nat d) e) t (Translate d c1) (Translate d c2) ⊑
  Translate d (If e t c1 c2).
Proof.
  unfold lequiv, lep. simpl. induction t; intros.
  simpl in *. rewrite adv_exp_ext in *. remember (E[|e|](adv_ext (Z.of_nat d) rho)) as b.
  destruct b; try destruct v; try destruct b; try first [assumption|
  unfold const_trace, bot_trans in H; inversion H].

  simpl in *.  rewrite adv_exp_ext in *. 
  remember (E[|e|](adv_ext (Z.of_nat d) rho)) as b. destruct b. destruct v. destruct b. assumption. 
  rewrite adv_ext_swap. rewrite delay_trace_swap. 
  unfold delay_trace at 1.
  unfold delay_trace at 1 in H. 
  remember (leb 1 i) as L. destruct L.
  apply IHt. apply H. assumption.

  unfold const_trace, bot_trans in H. inversion H. 
  unfold const_trace, bot_trans in H. inversion H. 
Qed.


Hint Resolve adv_exp_type.

Theorem transl_ifwithin_equiv e d t c1 c2 : |-C c1 -> |-C c2 -> nil |-E e ∶ BOOL ->
  If (adv_exp (Z.of_nat d) e) t (Translate d c1) (Translate d c2) ≡
  Translate d (If e t c1 c2). 
Proof.
  intros T1 T2 T. apply lequiv_typed. constructor; auto. apply transl_ifwithin.
Qed.
