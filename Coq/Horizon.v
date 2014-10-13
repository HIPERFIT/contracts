Require Import Denotational.
Require Import Tactics.

(* Definition of contract horizon and proof of its correctness. *)

(* Behaves as addition unless second argument is 0, in which case 0 is
returned. *)

Definition plus0 (n m : nat) : nat :=
  match m with
    | 0 => 0
    | _ => n + m
  end.

Fixpoint horizon (c : contract) : nat :=
  match c with
      | Zero => 0
      | TransfOne _ _ _ => 1
      | Scale _ c' => horizon c'
      | Transl l c' => plus0 l (horizon c')
      | Both c1 c2 => max (horizon c1) (horizon c2)
      | IfWithin _ l c1 c2 => plus0 l (max (horizon c1) (horizon c2))
  end.

Lemma max0 n m : max n m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split. 
  - destruct n. reflexivity. destruct m; simpl in H; inversion H.
  - destruct m. reflexivity. destruct n; simpl in H; inversion H.
Qed.

Lemma horizon_empty c rho i : horizon c  <= i -> C[|c|]rho i = None \/ C[|c|]rho i = empty_trans.
Proof.
  generalize dependent rho. generalize dependent i. 
  induction c; simpl in *; intros.
  - auto.
  - destruct i. inversion H. auto.
  - unfold scale_trace, compose, scale_trans. eapply IHc in H. destruct H. 
    + left. rewrite H. apply option_map2_none.
    + destruct (E[|e|] rho). 
      * right. rewrite H. apply scale_empty_trans. 
      * left. reflexivity.
  - remember (horizon c) as h. destruct h.  
    unfold delay_trace. destruct (leb n i). apply IHc. omega. auto.
    simpl in H. assert (horizon c <= i - n) as H' by omega.
    rewrite Heqh in *. eapply IHc in H'. 
    unfold delay_trace. assert (leb n i = true) as L. apply leb_correct. omega. rewrite L.
    destruct H'; eauto.
  - rewrite NPeano.Nat.max_lub_iff in H. destruct H as [H1 H2].
    eapply IHc1 in H1. eapply IHc2 in H2.
    unfold add_trace, add_trans.
    destruct H1 as [H1|H1]. 
    + left. rewrite H1. reflexivity.
    + destruct H2 as [H2|H2].
      * left. rewrite H2. apply option_map2_none.
      * right. rewrite H1, H2. auto.  
  - remember (max (horizon c1) (horizon c2)) as h. destruct h. 
    + symmetry in Heqh. apply max0 in Heqh. destruct Heqh.
      generalize dependent rho. generalize dependent i. 
      induction n; intros.
      *  simpl. destruct (E[|e|]rho).
         destruct t. apply IHc1. rewrite H0. auto.
           apply IHc2. rewrite H1. auto.
         left. reflexivity.
      * simpl.  destruct (E[|e|]rho); auto; destruct t.
        apply IHc1. rewrite H0. auto.
        unfold delay_trace. remember (leb 1 i) as L.
         destruct L. apply IHn. simpl. symmetry in HeqL. apply leb_complete in HeqL. omega. auto.
    + simpl in H. rewrite Heqh in H. clear Heqh.
      rewrite <- Max.plus_max_distr_l in H.
      rewrite NPeano.Nat.max_lub_iff in H. destruct H as [H1 H2].
      generalize dependent rho. generalize dependent i. 
      induction n; intros. 
      * eapply IHc1 in H1. eapply IHc2 in H2. simpl. destruct (E[|e|]rho).
          destruct t; eassumption.
          left. reflexivity.
      * simpl. destruct (E[|e|]rho); auto. destruct t.
          apply IHc1. omega.
          unfold delay_trace. assert (leb 1 i = true) as L. apply leb_correct. omega.
           rewrite L. apply IHn; omega.      
Qed.

Theorem horizon_sound c rho i : horizon c  <= i -> C[|c|]rho i ⊆ empty_trans.
Proof.
  simpl. intros R t T. apply horizon_empty with (rho:=rho) in R. destruct R as [R|R].
  tryfalse. rewrite <- R. assumption.
Qed.