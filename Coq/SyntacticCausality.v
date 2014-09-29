Require Import Causality.
Require Import Advance.

(* Syntactic causality. We define a simple syntactic notion of
causality that conservatively approximates the semantic notion. In
short a contract is syntactically causal if observables and external
choices are never queried at a positive offset. *)


Reserved Notation "'R|-' c" (at level 20).

Open Scope Z.

Inductive rpc : forall {V}, rexp' V -> Prop:=
| rpc_obs : forall V o i, i <= 0 -> R|- Obs o i (V:=V)
| rpc_lit : forall V q, R|- RLit q (V:=V)
| rpc_bin : forall V op e1 e2, R|- e1 -> R|- e2 -> R|- RBin op e1 e2 (V:=V)
| rpc_neg : forall V e, R|- e -> R|- RNeg e (V:=V)
| rpc_var : forall V q, R|- RVar q (V:=V)
| rpc_acc : forall V f l z, R|- f -> R|- z -> R|- RAcc f l z (V:=V)
                                         where "'R|-' e" := (rpc e). 

Reserved Notation "'B|-' c" (at level 20).

Inductive bpc : bexp -> Prop:=
| bpc_lit : forall b, B|- (BLit b)
| rpc_ch : forall ch i, i <= 0 -> B|- BChoice ch i
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

Hint Constructors rpc bpc pc.

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

Lemma bpc_ext_until e d r1 r2 : B|-e -> 0 <= d -> ext_until d r1 r2 -> B[|e|]r1 = B[|e|]r2.
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
    apply IHpc. rewrite ext_until_adv. assert (Z.of_nat d + Z.of_nat(d0 - d) = Z.of_nat d0) as D.
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
  
  rewrite bpc_ext_until with (r2:=r2) (d:=Z.of_nat d) by (eauto;omega). 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0. eapply IHpc1; eassumption. 
  eapply IHpc2; eassumption. reflexivity. 

  rewrite bpc_ext_until with (r2:=r2) (d:=Z.of_nat d) by (eauto;omega). 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0.  eapply IHpc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L.  apply IHl. 
  rewrite Nat2Z.inj_sub.
  apply ext_until_adv_1. symmetry in HeqL. apply leb_complete in HeqL. apply inj_le in HeqL. auto.
  auto.
  apply leb_complete. auto. auto. reflexivity. 
Qed.

Open Scope bool.

Fixpoint rpc_dec {V} (e : rexp' V) : bool :=
  match e with
    |  Obs _ _ i => Z.leb i 0
    | RLit _ _ => true
    | RBin _ _ e1 e2 => rpc_dec e1 && rpc_dec e2
    | RNeg _ e' => rpc_dec e'
    | RVar _ _ => true
    | RAcc _ f _ z => rpc_dec f && rpc_dec z
  end.

Lemma rpc_dec_correct {V} (e : rexp' V) : rpc_dec e = true <-> R|- e. 
Proof.
  split.
  - intro D. induction e; simpl in *; 
    try first [rewrite Bool.andb_true_iff in D; destruct D|rewrite Z.leb_le in D]; auto.
  - intros D. induction D; simpl; try first [rewrite IHD1, IHD2| apply Z.leb_le]; auto.
Qed.

Fixpoint bpc_dec (e : bexp) : bool :=
  match e with
    | BLit b => true
    | BChoice _ i => Z.leb i 0
    | RCmp _ e1 e2 => rpc_dec e1 && rpc_dec e2
    | BNot e' => bpc_dec e'
    | BOp _ e1 e2 => bpc_dec e1 && bpc_dec e2
  end.

Lemma bpc_dec_correct (e : bexp) : bpc_dec e = true <-> B|- e. 
Proof.
  split.
  - intro D. induction e; simpl in *; 
    try first [rewrite Bool.andb_true_iff in D; destruct D as [D1 D2]|rewrite Z.leb_le in D]; 
    try (rewrite -> rpc_dec_correct in D1, D2);auto.
  - intros D. induction D; simpl; try first [rewrite IHD1, IHD2| apply Z.leb_le]; 
    try (rewrite <- rpc_dec_correct in H, H0; rewrite H, H0);auto.
Qed.


Fixpoint pc_dec (c : contract) : bool :=
  match c with
    | Zero => true
    | TransfOne _ _ _ => true
    | Scale e c => rpc_dec e && pc_dec c
    | Transl _ c => pc_dec c
    | Both c1 c2 => pc_dec c1 && pc_dec c2
    | IfWithin e _ c1 c2 => bpc_dec e && pc_dec c1 && pc_dec c2
  end.

Theorem pc_dec_correct (c : contract) : pc_dec c = true <-> |- c. 
Proof.
  split.
  - intro D. induction c; simpl in *; 
    try first [repeat rewrite Bool.andb_true_iff in D; destruct D as [D1 D2]|rewrite Z.leb_le in D]; auto.
    + rewrite -> rpc_dec_correct in D1. auto.
    + destruct D1. rewrite bpc_dec_correct in *. auto.
  - intros D. induction D; simpl; try first [rewrite IHD1, IHD2| apply Z.leb_le]; auto.
    + rewrite <- rpc_dec_correct in H. rewrite H, IHD. auto.
    + rewrite <-bpc_dec_correct in *. rewrite H. auto.
Qed.
