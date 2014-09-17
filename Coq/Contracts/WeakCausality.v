Require Import Causality.
Require Import Advance.

(* Weak provable causality *)

Reserved Notation "'R|-' c" (at level 20).

Inductive rpc : rexp -> Prop:=
| rpc_obs : forall o i, Z.le i 0 -> R|- Obs o i
| rpc_lit : forall q, R|- (RLit q)
| rpc_bin : forall op e1 e2, R|- e1 -> R|- e2 -> R|- RBin op e1 e2
| rpc_neg : forall e, R|- e -> R|- RNeg e
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

Lemma rpc_inp_until e d r1 r2 : R|-e -> inp_until (Z.of_nat d) r1 r2 -> R[|e|]r1 = R[|e|]r2.
Proof.
  intros R O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in O. rewrite O. reflexivity. 
  eapply Z.le_trans. apply H. apply Nat2Z.is_nonneg.
Qed.

Lemma bpc_env_until e d r1 r2 : B|-e -> env_until (Z.of_nat d) r1 r2 -> B[|e|]r1 = B[|e|]r2.
Proof.
  intros R O. destruct O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in *. rewrite H0. reflexivity.
  eapply Z.le_trans. apply H1. apply Nat2Z.is_nonneg.

  f_equal; eapply rpc_inp_until; eassumption.
Qed.


Theorem pc_causal c : |- c -> causal c.
Proof.
  intros. induction H; unfold causal in *; intros; simpl.

  unfold delay_trace.
  remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    apply IHpc. rewrite env_until_adv. assert (Z.of_nat d + Z.of_nat(d0 - d) = Z.of_nat d0)%Z as D.
    rewrite <- Nat2Z.inj_add. f_equal. omega.
    rewrite D. assumption.
    
    reflexivity.

  reflexivity.

  unfold scale_trace, compose. erewrite IHpc by apply H1.
  unfold scale_trans. destruct H1. rewrite rpc_inp_until with (r2:=fst r2) (d:=d) by assumption. 
reflexivity. 

  unfold add_trace. f_equal; auto.

  reflexivity.

  generalize dependent d. generalize dependent r1. generalize dependent r2. 
  induction l; intros; simpl.
  
  erewrite bpc_env_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0. eapply IHpc1; eassumption. 
  eapply IHpc2; eassumption. reflexivity. 

  erewrite bpc_env_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0.  eapply IHpc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L.  apply IHl. 
  rewrite Nat2Z.inj_sub.
  apply env_until_adv_1. symmetry in HeqL. apply leb_complete in HeqL. apply inj_le in HeqL. auto.
  auto.
  apply leb_complete. auto. auto. reflexivity. 
Qed.
