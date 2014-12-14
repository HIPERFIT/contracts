Require Import Causality.
Require Import Advance.
Require Import Tactics.

(* Syntactic causality. We define a simple syntactic notion of
causality that conservatively approximates the semantic notion. In
short a contract is syntactically causal if observables and external
choices are never queried at a positive offset. *)


Inductive Epc : Exp -> Prop:=
| epc_obs : forall o i, i <= 0 -> Epc (Obs o i)
| epc_op : forall op es, all Epc es -> Epc (OpE op es)
| epc_var : forall v, Epc (VarE v)
| epc_acc : forall f l z, Epc f -> Epc z -> Epc (Acc f l z).


(* Custom induction principle *)

Definition Epc_ind' : forall P : Exp -> Prop,
       (forall (o : ObsLabel) (i : Z), i <= 0 -> P (Obs o i)) ->
       (forall (op : Op) (es : list Exp), all Epc es -> all P es -> P (OpE op es)) ->
       (forall v : Var, P (VarE v)) ->
       (forall (f2 : Exp) (l : nat) (z : Exp),
        Epc f2 -> P f2 -> Epc z -> P z -> P (Acc f2 l z)) ->
       forall e : Exp, Epc e -> P e
  := 
fun (P : Exp -> Prop)
  (f : forall (o : ObsLabel) (i : Z), i <= 0 -> P (Obs o i))
  (f0 : forall (op : Op) (es : list Exp), all Epc es -> all P es -> P (OpE op es))
  (f1 : forall v : Var, P (VarE v))
  (f2 : forall (f2 : Exp) (l : nat) (z : Exp),
        Epc f2 -> P f2 -> Epc z -> P z -> P (Acc f2 l z)) =>
fix F (e : Exp) (e0 : Epc e) {struct e0} : P e :=
  match e0 in (Epc e1) return (P e1) with
  | epc_obs o i l => f o i l
  | epc_op op es f3 => let fix step {es} (ps : all Epc es) : all P es := 
                           match ps in all _ es return all P es with
                             | forall_nil => forall_nil P
                             | forall_cons e es p ps' => forall_cons P (F e p) (step ps')
                           end
                       in f0 op es f3 (step f3)
  | epc_var v => f1 v
  | epc_acc f3 l z e1 e2 => f2 f3 l z e1 (F f3 e1) e2 (F z e2)
  end.



Inductive Pc : Contr -> Prop :=
| pc_transl : forall d c, Pc c -> Pc (Translate d c)
| pc_let : forall e c, Epc e -> Pc c -> Pc (Let e c)
| pc_transf : forall cur p1 p2, Pc (Transfer cur p1 p2)
| pc_scale : forall e c, Epc e -> Pc c -> Pc (Scale e c)
| pc_both : forall c1 c2, Pc c1 -> Pc c2 -> Pc (Both c1 c2)
| pc_zero : Pc Zero
| pc_if : forall c1 c2 b l, Epc b -> Pc c1 -> Pc c2 -> Pc (If b l c1 c2).


Hint Constructors Epc Pc.

(* Below follows the proof that provable causality is sound (i.e. it
implies semantic causality). *)

Lemma epc_ext_until (e : Exp) d r1 r2 vars : 
  Epc e -> 0 <= d -> ext_until d r1 r2 -> E[|e|]vars r1 = E[|e|]vars r2.
Proof.
  intros R D O.   generalize dependent vars. generalize dependent r2. generalize dependent r1.
  induction R using Epc_ind'; intros; try solve [simpl; f_equal; auto].
  - simpl; unfold ext_until in O. rewrite O. reflexivity. omega.
  - do 4 (eapply all_apply in H0;eauto).
    apply map_rewrite in H0. simpl. rewrite H0. reflexivity.
  - generalize dependent vars. generalize dependent r2. generalize dependent r1. induction l; intros. 
    + simpl. apply IHR2. assumption.
    + pose (adv_ext_step l (A:=Val)) as RE. simpl in *. do 2 rewrite RE.
      erewrite IHl. apply bind_equals. apply IHl. apply ext_until_adv. eapply ext_until_le. eauto.
      omega. intros. apply IHR1.  apply ext_until_adv. do 2 rewrite adv_ext_iter. apply ext_until_adv. 
      eapply ext_until_le.  apply O. rewrite Zpos_P_of_succ_nat.
      omega. constructor.
Qed.

(* Causality of (open) contracts *)

Definition causal' (c : Contr) : Prop :=
  forall d vars r1 r2 t1 t2,  ext_until (Z.of_nat d) r1 r2 -> C[|c|]vars r1 = Some t1 -> C[|c|] vars r2 = Some t2
                        -> t1 d = t2 d.


Lemma pc_causal' c : Pc c -> causal' c.
Proof.
  intros. induction H; unfold causal' in *; intros; simpl.
  
  - simpl in *. option_inv_auto. unfold delay_trace.
    remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    assert (Z.of_nat d + Z.of_nat(d0 - d) = Z.of_nat d0) as D.
    rewrite <- Nat2Z.inj_add. f_equal. omega.
    eapply IHPc; eauto. rewrite ext_until_adv with (t:=Z.of_nat d).  
    rewrite D. eassumption. reflexivity.
  - simpl in *. option_inv_auto. erewrite epc_ext_until in H4; eauto. rewrite H4 in H5. 
    inversion H5. subst. eauto. omega.
  - simpl in *. rewrite H0 in H1. inversion H1. reflexivity.
  - simpl in *. rewrite epc_ext_until with (r2:=r2) (d:=Z.of_nat d) in H2 by first[eassumption|omega].
    option_inv_auto. rewrite H7 in H3. inversion H3. clear H3. subst. 
    rewrite H9 in H8. inversion H8. clear H8. subst.
    unfold scale_trace, compose. erewrite IHPc by eassumption. reflexivity. 
  - simpl in *. option_inv_auto. unfold add_trace. f_equal; eauto.
  - simpl in *. inversion H0. inversion H1. reflexivity.
  - generalize dependent d. generalize dependent r1. generalize dependent r2. 
    generalize dependent t1. generalize dependent t2. 
    induction l; intros; simpl in *.
    + rewrite epc_ext_until with (r2:=r2) (d:=Z.of_nat d) in * by (eauto;omega).
      remember (E[|b|] vars r2) as bl. destruct bl;tryfalse. destruct v;tryfalse. 
      destruct b0; [eapply IHPc1|eapply IHPc2]; eassumption. 
    +rewrite epc_ext_until with (r2:=r2) (d:=Z.of_nat d) in * by (eauto;omega). 
     remember (E[|b|] vars r2) as bl. destruct bl;tryfalse. destruct v;tryfalse.
     destruct b0.  eapply IHPc1; eassumption. 
     option_inv_auto. pose (IHl _ _ _ H5 _ H6) as IH.
     unfold delay_trace in *. remember (leb 1 d) as L. destruct L;try reflexivity. eapply IH.
     symmetry in HeqL. apply leb_complete in HeqL. rewrite Nat2Z.inj_sub by assumption.
     apply ext_until_adv_1. apply inj_le in HeqL. assumption. assumption.
Qed.

Theorem pc_causal c : Pc c -> causal c.
Proof.
  unfold causal. intros. eapply pc_causal';eauto.
Qed.


Open Scope bool.

Fixpoint epc_dec (e : Exp) : bool :=
  match e with
    | Obs _ i => Z.leb i 0
    | OpE _ args => let fix run es := 
                           match es with
                             | nil => true
                             | e' :: es' => epc_dec e' && run es'
                           end
                       in run args
    | VarE _ => true
    | Acc f _ z => epc_dec f && epc_dec z
  end.

Require Import Tactics.

Lemma epc_dec_correct (e : Exp) : epc_dec e = true <-> Epc e. 
Proof.
  split.
  - intro D. induction e using Exp_ind'; simpl in *; try first [rewrite Z.leb_le in D|
               repeat rewrite Bool.andb_true_iff in D; decompose [and] D]; auto.
    constructor. induction H. 
    + auto.
    + constructor.  destruct (epc_dec x); tryfalse. auto.
      apply IHall. destruct ((fix run (es : list Exp) : bool :=
      match es with
      | Datatypes.nil => true
      | e' :: es' => epc_dec e' && run es'
      end) xs). reflexivity. rewrite Bool.andb_false_r in *. tryfalse.

  - intros D. induction D using Epc_ind'; try first [simpl; rewrite IHD1, IHD2| apply Z.leb_le]; auto.
    induction H0.
    + auto.
    + simpl in *. rewrite IHall. rewrite H0. reflexivity. inversion H. auto.
Qed.


Fixpoint pc_dec (c : Contr) : bool :=
  match c with
    | Zero => true
    | Let e c => epc_dec e && pc_dec c
    | Transfer _ _ _ => true
    | Scale e c => epc_dec e && pc_dec c
    | Translate _ c => pc_dec c
    | Both c1 c2 => pc_dec c1 && pc_dec c2
    | If e _ c1 c2 => epc_dec e && pc_dec c1 && pc_dec c2
  end.

Theorem pc_dec_correct (c : Contr) : pc_dec c = true <-> Pc c. 
Proof.
  split.
  - intro D. induction c; simpl in *; 
    try first [repeat rewrite Bool.andb_true_iff in D; decompose [and] D
              |rewrite Z.leb_le in D]; auto.
    + rewrite -> epc_dec_correct in H. auto.
    + rewrite -> epc_dec_correct in H. auto.
    + rewrite epc_dec_correct in H1. auto.
  - intros D. induction D; simpl; try first [rewrite IHD1, IHD2| apply Z.leb_le]; auto.
    + rewrite <- epc_dec_correct in H. rewrite H, IHD. auto.
    + rewrite <-epc_dec_correct in H. rewrite H. auto.
    + rewrite <-epc_dec_correct in H. rewrite H. auto.
Qed.
