Require Export Denotational.
Require Import Advance.
Require Import Tactics.
Require Import Equality.
Open Scope Z.

(********** Monotonicity of the denotational semantics **********)

Lemma adv_ext_monotone (r1 r2 : ExtEnv) n : r1 ⊆ r2 -> adv_ext n r1 ⊆ adv_ext n r2.
Proof. 
  unfold lep, adv_ext. simpl. intros. remember (r1 o (n + i)) as X.
  destruct X;tryfalse. apply H. rewrite <- H0. auto. 
Qed.


Import ListNotations.

Lemma mapM_monotone {A B} (f g : A -> option B) l : forall_list (fun x => f x ⊆ g x) l -> mapM f l ⊆ mapM g l.
Proof.
  intros. induction l.
  - simpl. intros. auto.
  - simpl in *. unfold liftM2, bind, pure, compose. intros.
    remember (f a) as F. destruct F; tryfalse. destruct (mapM f l);tryfalse. inversion H0. subst.
    inversion H. subst. erewrite H3; eauto. erewrite IHl; eauto.
Qed. 

Lemma lookupEnv_monotone vars1 vars2 v : vars1 ⊆ vars2 -> lookupEnv v vars1 ⊆ lookupEnv v vars2.
Proof.
  intros. generalize dependent vars1. generalize dependent vars2. induction v; intros.
  + simpl. intros. destruct H; auto. 
  + simpl in *. intros. destruct H; auto. eapply IHv; eauto.
Qed.

Lemma Esem_monotone' (vars1 vars2 : Env) (e : Exp) rho1 rho2 : 
  rho1 ⊆ rho2 -> vars1 ⊆ vars2 -> E'[| e |] vars1 rho1 ⊆ E'[| e |] vars2 rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  generalize dependent vars1. generalize dependent vars2. 
  induction e using Exp_ind'; try solve [simpl; intros; auto].
  - intros. do 2 rewrite EsemOpE. simpl. intros.
    remember (mapM (fun e : Exp => E'[|e|] vars1 rho1) args) as M.
    do 6 (eapply forall_list_apply_dep in H; eauto).
    destruct M; tryfalse. symmetry in HeqM. eapply mapM_monotone in HeqM.
    rewrite HeqM. auto. simpl. auto.
  - simpl. intros. generalize dependent H1. apply lookupEnv_monotone. auto.
  - intros. simpl.
    generalize dependent rho1. generalize dependent rho2. 
    generalize dependent vars1. generalize dependent vars2. 
    induction d; intros.
    + simpl in *. eapply IHe2; eauto. 
    + intros. rewrite adv_ext_step. simpl. simpl in H1. eapply IHe1. do 3 apply adv_ext_monotone. eauto. 
      constructor. simpl. intros. eapply IHd; auto. eauto. apply adv_ext_monotone. eauto.
      apply H2. eauto. rewrite <- adv_ext_step. apply H1.
 Qed.

Corollary Esem_monotone (e : Exp) rho1 rho2 : rho1 ⊆ rho2 -> E[| e |]rho1 ⊆ E[| e |]rho2.
Proof. intros. apply Esem_monotone'; auto. simpl. auto. Qed.

Theorem Csem_monotone c rho1 rho2 : rho1 ⊆ rho2 -> C[| c |]rho1 ⊆ C[| c |]rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  induction c; intros rho2 rho1 S; simpl; intros; auto.
  - remember (E[|e|] rho1) as Y. destruct Y; tryfalse.
    pose (Esem_monotone e rho1 rho2 S). 
    unfold scale_trace in *. unfold compose in *.
    rewrite <- HeqY in *. erewrite -> l. 
    remember (C[|c|] rho1 i) as X.
    pose (IHc _ _ S i) as IHi.
    destruct X; tryfalse. rewrite <- HeqX in * by auto. erewrite IHi by auto.
    eauto. unfold scale_trans in H. rewrite liftM2_none in H. inversion H. reflexivity.
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
      rewrite HeqB. destruct v; tryfalse. destruct b. eapply IHc1; eauto.
      eapply IHc2; eauto. 
    * simpl. simpl in H. remember (E[|e|]rho1) as B.
      pose (Esem_monotone e (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct v; tryfalse. destruct b. eapply IHc1; eauto.
      unfold delay_trace in *. destruct (leb 1 i).
      + eapply IHn. apply adv_ext_monotone. eassumption. assumption.
      + assumption.
Qed.
