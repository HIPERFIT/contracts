Require Import Causality.
Require Import Advance.

(* Weak provable causality *)


Reserved Notation "'R|-' c" (at level 20).

Open Scope Z.

Inductive rpc : forall {n}, rexp' n -> Prop:=
| rpc_obs : forall n o i, i <= 0 -> R|- Obs o i (n:=n)
| rpc_lit : forall n q, R|- RLit q (n:=n)
| rpc_bin : forall n op e1 e2, R|- e1 -> R|- e2 -> R|- RBin op e1 e2 (n:=n)
| rpc_neg : forall n e, R|- e -> R|- RNeg e (n:=n)
| rpc_var : forall n q, R|- RVar q (n:=n)
| rpc_acc : forall n f l z, R|- f -> R|- z -> R|- RAcc f l z (n:=n)
                                         where "'R|-' e" := (rpc e). 

Reserved Notation "'B|-' c" (at level 20).

Inductive bpc : bexp -> Prop:=
| bpc_lit : forall b, B|- (BLit b)
| rpc_ch : forall ch i, Z.le i 0 -> B|- BChoice ch i
| bpc_cmp : forall cmp e1 e2, R|- e1 -> R|- e2 -> B|- RCmp cmp e1 e2
| bpc_op : forall op e1 e2, B|- e1 -> B|- e2 -> B|- BOp op e1 e2
| bpc_not : forall e, B|- e -> B|- BNot e
                                         where "'B|-' e" := (bpc e). 

Reserved Notation "'|-' c" (at level 20).

Inductive pc : contract -> Prop :=
| pc_transl : forall d c, |- c -> |- Transl d c
| pc_transf : forall cur p1 p2, |- TransfOne cur p1 p2
| pc_scale : forall e c, R|- e -> |- c -> |- Scale e c
| pc_both : forall c1 c2, |- c1 -> |- c2 -> |- Both c1 c2
| pc_zero : |- Zero
| pc_if : forall c1 c2 b l, B|- b -> |- c1 -> |- c2 -> |- IfWithin b l c1 c2
                                            where "'|-' c" := (pc c). 

(* Below follows the proof that provable causality is sound (i.e. it
implies semantic causality). *)

Lemma rpc_inp_until' n (e : rexp' n) d r1 r2 vars : 
  R|-e -> 0 <= d -> inp_until d r1 r2 -> R'[|e|]vars r1 = R'[|e|]vars r2.
Proof.
  intros R D O.   generalize dependent vars. generalize dependent r2. generalize dependent r1.
  induction R; intros; simpl; try solve [f_equal; auto].
  - unfold inp_until in O. rewrite O. reflexivity. omega.
  - remember (adv_inp (- Z.of_nat l) r1) as r1'.
    remember (adv_inp (- Z.of_nat l) r2) as r2'.
    assert (inp_until (Z.of_nat l + d) r1' r2') as I.
    subst. rewrite inp_until_adv. 
    assert (- Z.of_nat l + (Z.of_nat l + d) = d) as L.
    omega. rewrite L. assumption.
    clear Heqr1' Heqr2'.
    induction l. 
    + simpl. apply IHR2. simpl in I. assumption.
    + simpl. rewrite IHl. apply IHR1. rewrite inp_until_adv.
      eapply inp_until_le. eassumption. simpl. omega.
      eapply inp_until_le. apply I. rewrite Nat2Z.inj_succ. omega.
Qed.

Corollary rpc_inp_until (e : rexp) d r1 r2 : 
  R|-e -> 0 <= d -> inp_until d r1 r2 -> R[|e|] r1 = R[|e|]r2.
Proof. apply rpc_inp_until'. Qed.

Lemma bpc_env_until e d r1 r2 : B|-e -> 0 <= d -> env_until d r1 r2 -> B[|e|]r1 = B[|e|]r2.
Proof.
  intros R D O. destruct O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in *. rewrite H0. reflexivity. omega.

  f_equal; eapply rpc_inp_until; eauto. 
Qed.


Theorem pc_causal c : |- c -> causal c.
Proof.
  intros. induction H; unfold causal in *; intros; simpl.

  unfold delay_trace.
  remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    apply IHpc. rewrite env_until_adv. assert (Z.of_nat d + Z.of_nat(d0 - d) = Z.of_nat d0) as D.
    rewrite <- Nat2Z.inj_add. f_equal. omega.
    rewrite D. assumption.
    
    reflexivity.

  reflexivity.

  unfold scale_trace, compose. erewrite IHpc by apply H1.
  unfold scale_trans. destruct H1. rewrite rpc_inp_until with (r2:=fst r2) (d:=Z.of_nat d) by (auto; omega).
  reflexivity. 

  unfold add_trace. f_equal; auto.

  reflexivity.

  generalize dependent d. generalize dependent r1. generalize dependent r2. 
  induction l; intros; simpl.
  
  rewrite bpc_env_until with (r2:=r2) (d:=Z.of_nat d) by (eauto;omega). 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0. eapply IHpc1; eassumption. 
  eapply IHpc2; eassumption. reflexivity. 

  rewrite bpc_env_until with (r2:=r2) (d:=Z.of_nat d) by (eauto;omega). 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0.  eapply IHpc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L.  apply IHl. 
  rewrite Nat2Z.inj_sub.
  apply env_until_adv_1. symmetry in HeqL. apply leb_complete in HeqL. apply inj_le in HeqL. auto.
  auto.
  apply leb_complete. auto. auto. reflexivity. 
Qed.
