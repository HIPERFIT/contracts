Require Import Causality.
Require Import Advance.

(* Syntactic causality. We define a simple syntactic notion of
causality that conservatively approximates the semantic notion. In
short a contract is syntactically causal if observables and external
choices are never queried at a positive offset. *)


Reserved Notation "'E|-' c" (at level 20).

Open Scope Z.

Inductive epc : forall {V t}, exp' V t -> Prop:=
| epc_obs : forall t V o i, i <= 0 -> E|- Obs t o i (V:=V)
| epc_lit : forall t V q, E|- Lit q (V:=V) (t:=t)
| epc_bin : forall t s V op e1 e2, E|- e1 -> E|- e2 -> E|- @BinOpE t s V op e1 e2
| epc_if : forall t V b e1 e2, E|- b -> E|- e1 -> E|- e2 -> E|- @IfE t V b e1 e2
| epc_un : forall t s V op e, E|- e -> E|- @UnOpE t s V op e
| epc_var : forall t V q, E|- @VarE t V q 
| epc_acc : forall t V f l z, E|- f -> E|- z -> E|- @Acc t V f l z
                                         where "'E|-' e" := (epc e). 

Reserved Notation "'|-' c" (at level 20).

Inductive pc : contract -> Prop :=
| pc_transl : forall d c, |- c -> |- Transl d c
| pc_transf : forall cur p1 p2, |- TransfOne cur p1 p2
| pc_scale : forall e c, E|- e -> |- c -> |- Scale e c
| pc_both : forall c1 c2, |- c1 -> |- c2 -> |- Both c1 c2
| pc_zero : |- Zero
| pc_if : forall c1 c2 b l, E|- b -> |- c1 -> |- c2 -> |- IfWithin b l c1 c2
                                            where "'|-' c" := (pc c). 

Hint Constructors epc pc.

(* Below follows the proof that provable causality is sound (i.e. it
implies semantic causality). *)

Lemma epc_ext_until' V t (e : exp' V t) d r1 r2 vars : 
  E|-e -> 0 <= d -> ext_until d r1 r2 -> E'[|e|]vars r1 = E'[|e|]vars r2.
Proof.
  intros R D O.   generalize dependent vars. generalize dependent r2. generalize dependent r1.
  induction R; intros; simpl; try solve [f_equal; auto].
  - unfold ext_until in O. rewrite O. reflexivity. omega.
  - erewrite IHR1 by eassumption. erewrite IHR2 by eassumption. erewrite IHR3 by eassumption.
    reflexivity.
  - remember (adv_ext (- Z.of_nat l) r1) as r1'.
    remember (adv_ext (- Z.of_nat l) r2) as r2'.
    assert (ext_until (Z.of_nat l + d) r1' r2') as I.
    subst. rewrite ext_until_adv. 
    assert (- Z.of_nat l + (Z.of_nat l + d) = d) as L.
    omega. rewrite L. assumption.
    clear Heqr1' Heqr2'.
    induction l. 
    + simpl. apply IHR2. simpl in I. assumption.
    + simpl. rewrite IHl. apply IHR1. rewrite ext_until_adv.
      eapply ext_until_le. eassumption. simpl. omega.
      eapply ext_until_le. apply I. rewrite Nat2Z.inj_succ. omega.
Qed.

Corollary epc_ext_until t (e : exp t) d r1 r2 : 
  E|-e -> 0 <= d -> ext_until d r1 r2 -> E[|e|] r1 = E[|e|]r2.
Proof. apply epc_ext_until'. Qed.



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
  unfold scale_trans. rewrite epc_ext_until with (r2:=r2) (d:=Z.of_nat d) by (auto; omega).
  reflexivity. 

  unfold add_trace. f_equal; auto.

  reflexivity.

  generalize dependent d. generalize dependent r1. generalize dependent r2. 
  induction l; intros; simpl.
  
  rewrite epc_ext_until with (r2:=r2) (d:=Z.of_nat d) by (eauto;omega). 
  remember (E[|b|]r2) as bl. destruct bl. destruct t. eapply IHpc1; eassumption. 
  eapply IHpc2; eassumption. reflexivity. 

  rewrite epc_ext_until with (r2:=r2) (d:=Z.of_nat d) by (eauto;omega). 
  remember (E[|b|]r2) as bl. destruct bl. destruct t.  eapply IHpc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L.  apply IHl. 
  rewrite Nat2Z.inj_sub.
  apply ext_until_adv_1. symmetry in HeqL. apply leb_complete in HeqL. apply inj_le in HeqL. auto.
  auto.
  apply leb_complete. auto. auto. reflexivity. 
Qed.

Open Scope bool.

Fixpoint epc_dec {V t} (e : exp' V t) : bool :=
  match e with
    | Obs _ _ _ i => Z.leb i 0
    | Lit _ _ _ => true
    | BinOpE _ _ _ _ e1 e2 => epc_dec e1 && epc_dec e2
    | UnOpE _ _ _ _ e' => epc_dec e'
    | IfE _ _ b e1 e2 => epc_dec b && epc_dec e1 && epc_dec e2
    | VarE _ _ _ => true
    | Acc _  _ f _ z => epc_dec f && epc_dec z
  end.

Lemma epc_dec_correct {V t} (e : exp' V t) : epc_dec e = true <-> E|- e. 
Proof.
  split.
  - intro D. induction e; simpl in *; 
    try first [rewrite Z.leb_le in D|
               repeat rewrite Bool.andb_true_iff in D; decompose [and] D]; auto.
  - intros D. induction D; simpl; try first [rewrite IHD1, IHD2| apply Z.leb_le]; auto.
Qed.


Fixpoint pc_dec (c : contract) : bool :=
  match c with
    | Zero => true
    | TransfOne _ _ _ => true
    | Scale e c => epc_dec e && pc_dec c
    | Transl _ c => pc_dec c
    | Both c1 c2 => pc_dec c1 && pc_dec c2
    | IfWithin e _ c1 c2 => epc_dec e && pc_dec c1 && pc_dec c2
  end.

Theorem pc_dec_correct (c : contract) : pc_dec c = true <-> |- c. 
Proof.
  split.
  - intro D. induction c; simpl in *; 
    try first [repeat rewrite Bool.andb_true_iff in D; decompose [and] D
              |rewrite Z.leb_le in D]; auto.
    + rewrite -> epc_dec_correct in H. auto.
    + rewrite epc_dec_correct in H1. auto.
  - intros D. induction D; simpl; try first [rewrite IHD1, IHD2| apply Z.leb_le]; auto.
    + rewrite <- epc_dec_correct in H. rewrite H, IHD. auto.
    + rewrite <-epc_dec_correct in H. rewrite H. auto.
Qed.
