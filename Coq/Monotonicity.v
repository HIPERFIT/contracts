Require Export Denotational.
Require Import Advance.
Require Import Tactics.
Require Import Equality.
Open Scope Z.

(********** Monotonicity of the denotational semantics **********)

Lemma adv_ext_monotone (r1 r2 : ext) n : r1 ⊆ r2 -> adv_ext n r1 ⊆ adv_ext n r2.
Proof. 
  unfold lep, adv_ext. simpl. intros. remember (r1 (n + i) t o) as X.
  destruct X;tryfalse. apply H. rewrite <- H0. auto. 
Qed.


Lemma Esem_monotone' V t (vars1 vars2 : Env (option ∘ TySem) V) (e : exp' V t) rho1 rho2 : 
  rho1 ⊆ rho2 -> vars1 ⊆ vars2 -> E'[| e |] vars1 rho1 ⊆ E'[| e |] vars2 rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  generalize dependent vars1. generalize dependent vars2. 
  induction e; try solve [simpl; intros; auto].
  - simpl. intros. 
    remember (E'[|e1|] vars1 rho1) as R1; remember (E'[|e2|] vars1 rho1) as R2.
    destruct R1;destruct R2; tryfalse.
    symmetry in HeqR1. eapply IHe1 in HeqR1.
    symmetry in HeqR2. eapply IHe2 in HeqR2.
    rewrite HeqR1. rewrite HeqR2. auto. auto. auto. auto. auto.
  - simpl. intros. remember (E'[|e|] vars1 rho1) as R.
    destruct R; tryfalse.
    symmetry in HeqR. eapply IHe in HeqR.
    rewrite HeqR. auto. auto. auto.
  - simpl. intros. 
    remember (E'[|e1|] vars1 rho1) as R1; remember (E'[|e2|] vars1 rho1) as R2;
    remember (E'[|e3|] vars1 rho1) as R3.
    destruct R1; tryfalse.
    destruct t0.
    + destruct R2; tryfalse.
      symmetry in HeqR1. eapply IHe1 in HeqR1.
      symmetry in HeqR2. eapply IHe2 in HeqR2.
      rewrite HeqR1. rewrite HeqR2. auto. auto. auto. auto. auto. 
    + destruct R3; tryfalse.
      symmetry in HeqR1. eapply IHe1 in HeqR1.
      symmetry in HeqR3. eapply IHe3 in HeqR3.
      rewrite HeqR1. rewrite HeqR3. auto. auto. auto. auto. auto. 
  - intros. pose (EnvLe_lookup (I := Ty) (t :=t) (V:=V) (f:=TySem)) as E. simpl in *.
    intros. eapply E; eauto.
  - simpl. intros. auto.
    remember (adv_ext (- Z.of_nat n) rho1) as rho1'. 
    remember (adv_ext (- Z.of_nat n) rho2) as rho2'. 
    assert (rho1' ⊆ rho2') as Sub.
    subst. apply adv_ext_monotone. auto.
    clear Heqrho1' Heqrho2'.
    generalize dependent z. induction n.
    + simpl in *. eapply IHe2; eauto. 
    + intros. simpl. eapply IHe1. apply adv_ext_monotone. eauto.
      constructor. simpl. intros. apply IHn; auto. apply H2.
      simpl. apply H0. apply H1.
Qed.

Corollary Esem_monotone {t} (e : exp t) rho1 rho2 : rho1 ⊆ rho2 -> E[| e |]rho1 ⊆ E[| e |]rho2.
Proof. intros. apply Esem_monotone'; auto. unfold empty_env. auto. Qed.

Theorem Csem_monotone c rho1 rho2 : rho1 ⊆ rho2 -> C[| c |]rho1 ⊆ C[| c |]rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  induction c; intros rho2 rho1 S; simpl; intros; auto.
  - remember (E[|e|] rho1) as Y. destruct Y; tryfalse.
    pose (Esem_monotone e rho1 rho2 S). 
    unfold scale_trace in *. unfold compose in *.
    rewrite <- HeqY in *. apply lep_some in l. rewrite <- l.
    remember (C[|c|] rho1 i) as X.
    pose (IHc _ _ S i) as IHi. 
    destruct X; tryfalse. rewrite <- HeqX in * by auto. erewrite IHi by auto.
    auto.
  - simpl. apply adv_ext_monotone with (n := Z.of_nat n) in S. apply IHc in S.
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
    * simpl. simpl in H.  remember (E[|e|]rho1) as B.
      pose (Esem_monotone e (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct t. eapply IHc1; eauto.
      eapply IHc2; eauto.
    * simpl. simpl in H. remember (E[|e|]rho1) as B.
      pose (Esem_monotone e (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct t. eapply IHc1; eauto.
      unfold delay_trace in *. destruct (leb 1 i).
      + eapply IHn. apply adv_ext_monotone. eassumption. assumption.
      + assumption.
Qed.
