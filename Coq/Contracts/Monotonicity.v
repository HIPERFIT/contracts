Require Export Denotational.
Require Import Advance.
Require Import Tactics.
Open Scope Z.

(********** Monotonicity of the denotational semantics **********)

Lemma Rsem_monotone e rho1 rho2 : rho1 ⊆ rho2 -> R[| e |]rho1 ⊆ R[| e |]rho2.
Proof.
  intro S; induction e; simpl; intros; auto.
  - destruct (R[|e1|]rho1); destruct (R[|e2|]rho1); tryfalse.
    apply lep_some in IHe1. apply lep_some in IHe2. 
    rewrite <- IHe1. rewrite <- IHe2. simpl in *. auto.
  - destruct (R[|e|]rho1); tryfalse. apply lep_some in IHe. rewrite <- IHe. auto. 
Qed.

Lemma Bsem_monotone e rho1 rho2 : rho1 ⊆ rho2 -> B[| e |]rho1 ⊆ B[| e |]rho2.
Proof.
  intro S; induction e; simpl; intros; auto.
  - destruct S. auto.
  - destruct S as [S1 S2]. 
    remember (R[|r|](fst rho1)) as X1. remember (R[|r0|](fst rho1)) as X2.
    pose (Rsem_monotone r _ _ S1) as R1. pose (Rsem_monotone r0 _ _ S1) as R2.
    destruct X1; tryfalse. destruct X2; tryfalse. 
    rewrite <- HeqX1 in R1. rewrite <- HeqX2 in R2.
    simpl in *. erewrite R1 by auto. erewrite R2 by auto.
    auto.
  - destruct (B[|e|]rho1); tryfalse. erewrite IHe by auto. assumption.
  - destruct (B[|e1|]rho1); tryfalse. destruct (B[|e2|]rho1); tryfalse.
    erewrite IHe1 by auto. erewrite IHe2 by auto.  assumption.
Qed.



Lemma adv_inp_monotone A (in1 in2 : inp A) n : in1 ⊆ in2 -> adv_inp n in1 ⊆ adv_inp n in2.
Proof. 
  unfold lep, adv_inp. simpl. intros. remember (in1 (n + i) j) as X.
  destruct X;tryfalse. apply H. rewrite <- H0. auto. 
Qed.

Lemma adv_env_monotone rho1 rho2 n : rho1 ⊆ rho2 -> adv_env n rho1 ⊆ adv_env n rho2.
Proof. 
  intros. destruct rho1. destruct rho2. destruct H. split; apply adv_inp_monotone;
  auto.
Qed.


Theorem Csem_monotone c rho1 rho2 : rho1 ⊆ rho2 -> C[| c |]rho1 ⊆ C[| c |]rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  induction c; intros rho2 rho1 S; simpl; intros; auto.
  - pose S as S'. destruct S' as [S1 S2]. 
    remember (R[|r|] (fst rho1)) as Y. destruct Y; tryfalse.
    pose (Rsem_monotone r (fst rho1) (fst rho2) S1). 
    unfold scale_trace in *. unfold compose in *.
    rewrite <- HeqY in *. apply lep_some in l. rewrite <- l.
    remember (C[|c|] rho1 i) as X.
    pose (IHc _ _ S i) as IHi. 
    destruct X; tryfalse. rewrite <- HeqX in * by auto. erewrite IHi by auto.
    auto.
  - simpl. apply adv_env_monotone with (n := Z.of_nat n) in S. apply IHc in S.
    simpl in S. unfold delay_trace in *. destruct (leb n i); auto.
  - unfold add_trace, add_trans in *. 
    remember (C[|c1|] rho1 i) as X1. remember (C[|c2|] rho1 i) as X2.
    pose (IHc1 _ _ S i) as IHi1. pose (IHc2 _ _ S i) as IHi2. 
    destruct X1; tryfalse. destruct X2; tryfalse. 
    symmetry in HeqX1. apply IHi1 in HeqX1.
    symmetry in HeqX2. apply IHi2 in HeqX2. 
    auto. erewrite HeqX1. erewrite HeqX2. auto.
  - generalize dependent rho1.
    generalize dependent rho2.
    generalize dependent i.
    induction n; intros.
    * simpl. simpl in H.  remember (B[|b|]rho1) as B.
      pose (Bsem_monotone b (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct b0. eapply IHc1; eauto.
      eapply IHc2; eauto.
    * simpl. simpl in H. remember (B[|b|]rho1) as B.
      pose (Bsem_monotone b (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct b0. eapply IHc1; eauto.
      unfold delay_trace in *. destruct (leb 1 i).
      + eapply IHn. apply adv_env_monotone. eassumption. assumption.
      + assumption.
Qed.
