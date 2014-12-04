Require Import Denotational.
Require Import Tactics.
Require Import DenotationalTyped.

(* Definition of contract horizon and proof of its correctness. *)

(* Behaves as addition unless second argument is 0, in which case 0 is
returned. *)

Definition plus0 (n m : nat) : nat :=
  match m with
    | 0 => 0
    | _ => n + m
  end.

Lemma plus0_max_l n m p i : plus0 p (max n m) <= i -> n <= i.
Proof.
  remember (max n m) as h. destruct h. destruct n.  simpl. auto.
  simpl in *. destruct m;tryfalse.
  simpl. rewrite Heqh. intros. assert (max n m <= i) by omega. eapply Max.max_lub_l. eauto.
Qed.

Lemma plus0_max_r n m p i : plus0 p (max n m) <= i -> m <= i.
Proof.
  rewrite Max.max_comm. apply plus0_max_l.
Qed.

Lemma plus0_le n m i : plus0 (S n) m <= i -> plus0 n m <= i - 1.
Proof.
  destruct m. simpl. intros. omega.
  simpl. intros. omega.
Qed.


Fixpoint horizon (c : Contr) : nat :=
  match c with
      | Zero => 0
      | Let _ c' => horizon c'
      | Transfer _ _ _ => 1
      | Scale _ c' => horizon c'
      | Translate l c' => plus0 l (horizon c')
      | Both c1 c2 => max (horizon c1) (horizon c2)
      | If _ l c1 c2 => plus0 l (max (horizon c1) (horizon c2))
  end.


Lemma max0 n m : max n m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split. 
  - destruct n. reflexivity. destruct m; simpl in H; inversion H.
  - destruct m. reflexivity. destruct n; simpl in H; inversion H.
Qed.


(* Lemma horizon_empty c g vars rho i t : g |-C c -> TypeEnv g vars -> TypeExt rho -> horizon c  <= i ->  *)
(*                                            C[|c|] vars rho = Some t -> t i = empty_trans. *)

Theorem horizon_sound c vars rho i t : horizon c  <= i ->
                                     C[|c|] vars rho = Some t -> t i = empty_trans.

Proof.
  intros HO T. generalize dependent vars. generalize dependent rho. generalize dependent t.
  generalize dependent i.
  induction c; simpl in *;intros.
  - inversion T. reflexivity.
  - destruct (E[|e|] vars rho);tryfalse. simpl in T. eapply IHc. assumption.  eapply T.
  - destruct i. inversion HO. inversion T. reflexivity.
  - remember (E[|e|] vars rho >>= toReal) as r. remember (C[|c|] vars rho) as C.
    destruct r;destruct C; tryfalse. simpl in T. unfold pure, compose in *. inversion T.
    symmetry in HeqC. eapply IHc with (i:=i) in HeqC ; auto. unfold scale_trace, compose.
    rewrite HeqC. apply scale_empty_trans. 
  - remember (C[|c|] vars (adv_ext (Z.of_nat n) rho)) as C. destruct C;tryfalse.
    simpl in T. unfold pure,compose in T. inversion T. clear T. unfold delay_trace.
    remember (horizon c) as h. destruct h.  
    destruct (leb n i). eapply IHc. omega. eauto. reflexivity.
    simpl in HO. assert (horizon c <= i - n) as H' by omega.
    rewrite Heqh in *. eapply IHc in H'. 
    unfold delay_trace. assert (leb n i = true) as L. apply leb_correct. omega. rewrite L.
    destruct H'; eauto. eauto.
  - rewrite NPeano.Nat.max_lub_iff in HO. destruct HO as [H1 H2].
    remember (C[|c1|] vars rho) as C1. remember (C[|c2|] vars rho) as C2.
    destruct C1; destruct C2; tryfalse.
    simpl in T. unfold pure, compose in T. inversion T.
    unfold add_trace. erewrite IHc1;eauto. erewrite IHc2;eauto.
  - generalize dependent rho. generalize dependent i. generalize dependent t. induction n;intros.
    + simpl in HO. simpl in T. destruct (E[|e|] vars rho);tryfalse. destruct v;tryfalse.
      destruct b. eapply IHc1; eauto. eapply plus0_max_l; eauto.
      eapply IHc2; eauto. eapply plus0_max_r; eauto.
    + simpl in HO. simpl in T. destruct (E[|e|] vars rho);tryfalse. destruct v;tryfalse.
      destruct b. eapply IHc1; eauto. eapply plus0_max_l; eauto.
      remember (within_sem C[|c1|] C[|c2|] e n vars (adv_ext 1 rho)) as C. destruct C;tryfalse.
      simpl in T. unfold pure, compose in T. inversion T. clear T.
      symmetry in HeqC. eapply IHn in HeqC. unfold delay_trace. destruct (leb 1 i).
      apply HeqC. reflexivity. apply plus0_le. assumption.
Qed.
