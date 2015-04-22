Require Import Causality.
Require Import TranslateExp.
Require Import FunctionalExtensionality.
Require Import Tactics.
Require Import Utils.

(* Contextual syntactic causality. This syntactic notion of causality
is more permissive than plain syntactic causality. *)

Open Scope Z.


(* Definition of the inference rules for contextual causality. *)

Inductive TimeB := Time (t:Z) | TimeBot.

Definition TimeEnv := list TimeB.

Inductive tle : TimeB -> TimeB -> Prop:=
| tle_bot t : tle TimeBot t
| tle_notbot t1 t2 : t1 <= t2 -> tle (Time t1) (Time t2).

Notation "n <= m" := (tle n m) : time.

Inductive tlt : TimeB -> TimeB -> Prop:=
| tlt_bot t : tlt TimeBot (Time t)
| tlt_notbot t1 t2 : t1 < t2 -> tlt (Time t1) (Time t2).

Notation "n < m" := (tlt n m) : time.

Hint Constructors tle tlt.

Definition tleb (t1 t2 : TimeB) : bool :=
  match t1,t2 with
    | Time t1', Time t2' => t1' <=? t2'
    | TimeBot, _ => true
    | _,_ => false
  end.

Notation "n <=? m" := (tleb n m) : time.

Open Scope time.

Lemma tleb_tle t1 t2 : t1 <=? t2 = true <-> t1 <= t2.
Proof.
  split; intro S; destruct t1, t2; simpl in *;inversion S;eauto using Zle_bool_imp_le, Zle_imp_le_bool. 
Qed.

Lemma tleb_tgt t1 t2 : t1 <=? t2 = false <-> t2 < t1.
Proof.
  split; intro S; destruct t1, t2; simpl in *;inversion S; eauto; rewrite Z.leb_gt in *;  auto.
Qed.

Definition tmin t1 t2 := if t1 <=? t2 then t1 else t2.

Lemma tle_tlt t1 t2 : t1 < t2 -> t1 <= t2.
Proof.
  intro L. destruct L;constructor. omega.
Qed.


Inductive CausalV : TimeEnv -> TimeB -> Var -> Prop :=
| causal_V1 t t' g  : t <= t' -> CausalV (t :: g) t' V1
| causal_VS g v t t' : CausalV g t v -> CausalV (t' :: g) t (VS v).

Definition tadd (d : Z) (t : TimeB) : TimeB := 
  match t with
      | TimeBot => TimeBot
      | Time t' => Time (t' + d)
  end.
Definition tsub d : TimeB -> TimeB := tadd (-d).


Definition tadd' d : TimeB -> TimeB := tadd (Z.of_nat d).
Definition tsub' d : TimeB -> TimeB := tsub (Z.of_nat d).



Hint Unfold tsub tadd' tsub'.

Inductive CausalE : TimeEnv -> TimeB -> Exp -> Prop:= 
 | causal_op t ts op args : all (CausalE ts t) args -> CausalE ts t (OpE op args)
 | causal_obs l t' t ts : Time t' <= t -> CausalE ts t (Obs l t')
 | causal_var t ts v : CausalV ts t v -> CausalE ts t (VarE v)
 | causal_acc t ts e1 e2 n : CausalE (map (tadd' n) ts) (tadd' n t) e2
                                -> CausalE (TimeBot :: ts) t e1
                                -> CausalE ts t (Acc e1 n e2)
  .



Inductive CausalC : TimeEnv -> TimeB -> Contr -> Prop :=
| causal_zero ts t : CausalC ts t Zero
| causal_translate ts t d c : CausalC (map (tsub' d) ts) (tsub' d t) c
                                     -> CausalC ts t (Translate d c)
| causal_let ts t t' e c : CausalE ts t' e -> CausalC (t' :: ts) t c -> CausalC ts t (Let e c)
| causal_scale ts t t' e c : t' <= t -> CausalE ts t e -> CausalC ts t c -> CausalC ts t' (Scale e c)
| causal_both ts t c1 c2 : CausalC ts t c1 -> CausalC ts t c2 -> CausalC ts t (Both c1 c2)
| causal_transfer t ts p1 p2 a : t <= Time 0 -> CausalC ts t (Transfer p1 p2 a)
| causal_if ts t d e c1 c2 : CausalE ts (Time 0) e -> CausalC ts t c1
                             -> CausalC (map (tsub' d) ts) (tsub' d t) c2
                             -> CausalC ts t (If e d c1 c2)
.

Hint Constructors CausalV CausalE CausalC.

Lemma tle_refl t : t <= t.
Proof.
  destruct t; auto using Z.le_refl.
Qed.


Lemma tle_trans n m p: n <= m -> m <= p -> n <= p.
Proof.
  intros A B. destruct n, m, p; inversion A; inversion B;
  eauto using Z.le_trans. 
Qed.

Lemma tle_tadd n m d : n <= m -> tadd d n <= tadd d m.
Proof.
  intro A. destruct n,m; inversion A; simpl; autounfold; constructor. omega.
Qed.

Lemma tle_tadd_rev n m d : tadd d n <= tadd d m -> n <= m.
Proof.
  intro A. destruct n,m; inversion A; simpl; autounfold; constructor. omega.
Qed.


Lemma tle_tadd' n m d : n <= m -> tadd' d n <= tadd' d m.
eauto using tle_tadd. Qed.


Lemma tle_tsub' n m d : n <= m -> tsub' d n <= tsub' d m.
eauto 10 using tle_tadd. Qed.

Lemma tle_tsub'_rev n m d : tsub' d n <= tsub' d m -> n <= m.
eauto 10 using tle_tadd_rev. Qed.


Lemma tadd_swap d e t : tadd d (tadd e t) = tadd e (tadd d t).
Proof. 
  destruct t; simpl; f_equal. omega. reflexivity.
Qed.

Lemma tadd_tadd d e t : tadd d (tadd e t) = tadd (d + e) t.
Proof. 
  destruct t; simpl;f_equal. omega. reflexivity.
Qed.

Lemma tadd_0 t : tadd 0 t = t.
Proof. 
  destruct t; simpl; f_equal. omega. reflexivity.
Qed.

Lemma tadd'_0 t : tadd' 0 t = t.
autounfold. simpl. apply tadd_0. Qed.

Lemma tsub'_0 t : tsub' 0 t = t.
autounfold. simpl. apply tadd_0. Qed.


Hint Immediate tle_refl tadd_swap tadd_0 tadd'_0 tsub'_0.

Hint Resolve tle_trans tle_tadd  tle_tadd' tle_tsub'.


Lemma tmin_tle_l t1 t2 : tmin t1 t2 <= t1.
Proof.
  unfold tmin. cases (t1 <=? t2) as L. auto.
  rewrite tleb_tgt in L; auto using tle_tlt.
Qed.

Lemma tmin_tle_r t1 t2 : tmin t1 t2 <= t2.
Proof.
  unfold tmin. cases (t1 <=? t2) as L. 
  rewrite tleb_tle in L; auto using tle_tlt.
  auto.
Qed.

Lemma tsub_tadd_tle d x y : tsub d x <= y ->  x <= tadd d y.
Proof.
  intros T.
  destruct x, y; simpl in *;eauto;inversion T; constructor. omega. 
Qed.


Lemma map_tsub'_0 ts : map (tsub' 0) ts = ts.
Proof.
  erewrite map_ext. apply map_id. intros. eauto.
Qed.


(* Contextual causality is 'open': i.e. it is (anti-)monotone w.r.t. ordering on time. *)

Lemma CausalV_open t t' ts ts' (v : Var) : all2 tle ts' ts -> t <= t' -> CausalV ts t v -> CausalV ts' t' v.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'. generalize dependent ts. generalize dependent ts'.
  induction v; intros; inversion P; subst; inversion Is; eauto.
Qed.

Lemma CausalE_open t t' ts ts' (e : Exp) : all2 tle ts' ts -> t <= t' -> CausalE ts t e -> CausalE ts' t' e.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'.
  generalize dependent ts. generalize dependent ts'.
  induction e using Exp_ind'; intros;inversion P;subst;econstructor.
  - induction args.
    * constructor.
    * inversion H3. inversion H. subst. constructor. eauto. apply IHargs. auto. constructor. auto. auto.
  - eauto.
  - eapply CausalV_open; eauto. 
  - eapply IHe2;try eassumption;eauto using all2_map.
  - eapply IHe1 in H5;eauto.
Qed.


Lemma CausalV_shift ts t v d : (0 <= d)%Z -> CausalV ts t v -> CausalV (map (tadd d) ts) (tadd d t) v.
Proof.
  intros D V. induction V;constructor; auto.
Qed.

Lemma CausalE_shift ts t e d : (0 <= d)%Z -> CausalE ts t e -> CausalE (map (tadd d) ts) (tadd d t) e.
Proof.
  intros D C. generalize dependent d. generalize dependent ts. generalize dependent t.
  induction e using Exp_ind';intros;inversion C; subst. 
  - constructor. do 2 eapply all_apply in H; eauto. 
    eapply all_mp in H3; try eapply H. do 2 eapply all_apply in H3; eauto.
  - constructor. destruct t; inversion H2; constructor. omega.
  - constructor. apply CausalV_shift;assumption.
  - econstructor.
    * eapply IHe2 in H3. rewrite map_map in *. 
      unfold tadd' in *. rewrite tadd_swap. erewrite map_ext.
      apply H3. simpl. auto. auto.
    * eapply IHe1 in H5. simpl in H5. apply H5. assumption.
Qed.

Corollary CausalE_shift_1 ts t e : CausalE ts t e -> CausalE (map (tadd 1) ts) (tadd 1 t) e.
Proof.
  intros. apply CausalE_shift. omega. assumption.
Qed.

Definition env_until {A} t := all3 (B:=A) (fun t' x y => t' <= t -> x = y).

Lemma env_until_monotone {A} t ts f (e1 e2 : list A) : (forall x y, f x <= f y -> x <= y)
                                                  -> env_until t ts e1 e2 -> env_until (f t) (map f ts) e1 e2.
Proof.
  intros M U. induction U; constructor;auto. 
Qed.


Lemma env_until_weaken {A} t t' ts (env1 env2 : list A) : 
  env_until t ts env1 env2 -> t' <= t ->  env_until t' ts env1 env2.
Proof.
  intros U I. induction U;constructor;auto. intro. apply H. eauto.
Qed.

Lemma env_until_weaken' {A} t ts ts' (env1 env2 : list A) : 
  env_until t ts env1 env2 -> all2 tle ts ts' ->  env_until t ts' env1 env2.
Proof.
  intros U I. generalize dependent env1. generalize dependent env2. induction I;intros.
  inversion U. subst. constructor.
  inversion U. subst. constructor. intros. apply H2. eauto.
  unfold env_until in *. auto.
Qed.

Definition ext_until' t (ext1 ext2 : ExtEnv) :=
  match t with
    | Time t' => ext_until t' ext1 ext2
    | TimeBot => True
  end.

Lemma ext_until'_bot e1 e2 : ext_until' TimeBot e1 e2.
simpl. trivial.
Qed.

Hint Immediate ext_until'_bot.

Definition causalE ts t e := forall env1 env2 ext1 ext2, env_until t ts env1 env2 -> ext_until' t ext1 ext2
                                                        -> E[|e|] env1 ext1 = E[|e|]env2 ext2.

(* Contextual causality implies semantic causality. *)


Lemma succ_of_nat t d : t + 1 + Z.of_nat d = (t + Z.of_nat (S d)).
Proof.
  rewrite Nat2Z.inj_succ. omega. 
Qed.

Lemma CausalE_sound ts t e : CausalE ts t e -> causalE ts t e.
Proof.
  intro C. generalize dependent t. generalize dependent ts.
  induction e using Exp_ind'; intros;inversion C; subst. 
  - eapply all_apply in H. apply all_mp with (Q:=causalE ts t) in H; auto. unfold causalE in *. 
    intros. simpl. do 6 eapply all_apply in H; eauto. erewrite map_rewrite; eauto. clear C.
    induction args; inversion H3; subst; constructor; auto.  apply IHargs; auto. inversion H. auto.
  - unfold causalE. intros. simpl. inversion H2. subst. simpl in H0. unfold ext_until in *. rewrite H0; auto.
  - induction H2. 
    + unfold causalE. intros. inversion H0. subst. simpl. f_equal. auto.
    + unfold causalE in *. intros. inversion H. subst. simpl in *. eapply IHCausalV; eauto. 
  - unfold causalE. intros. simpl.
    generalize dependent t. generalize dependent ts.
    generalize dependent ext1. generalize dependent ext2. unfold Fsem in *. induction d; intros.
    + simpl. do 2 rewrite adv_ext_0. unfold causalE in IHe2. rewrite tadd'_0 in *.
      eapply IHe2; eauto. erewrite map_ext. rewrite map_id. assumption.
      auto. 
    + simpl. apply bind_equals. 
      * do 2 rewrite adv_ext_step'. eapply IHd with (t := tadd 1 t) (ts:= map (tadd 1) ts); eauto. 
        apply causal_acc. 
        rewrite map_map. erewrite map_ext. unfold tadd' in *. rewrite tadd_tadd. 
        rewrite Nat2Z.inj_succ in *. unfold Z.succ in *.
        eassumption. intros. autounfold. apply tadd_tadd.
        eapply CausalE_shift_1 in H5. simpl in H5. apply H5. 
        rewrite map_map. unfold tadd' in *. rewrite tadd_tadd. erewrite map_ext.
        rewrite Nat2Z.inj_succ in *. unfold Z.succ in *.
        apply H3. intros. apply tadd_tadd.
        eapply CausalE_shift_1 in H5. simpl in H5. apply H5.
        apply env_until_monotone with (f := tadd 1) in H. assumption. intros. eauto using tle_tadd_rev.
        destruct t;auto. simpl in *. rewrite Z.add_comm. rewrite <- ext_until_adv. 
        do 2 rewrite adv_ext_iter. simpl. do 2 rewrite adv_ext_0. assumption.
      * intros. unfold causalE in IHe1. eapply IHe1. eassumption. constructor. auto. auto.
        do 2 rewrite adv_ext_iter. rewrite Pos2Z.add_neg_pos. rewrite Z.pos_sub_diag.
        do 2 rewrite adv_ext_0. assumption.
Qed.

Lemma prec_of_nat t n : t - 1 - Z.of_nat n = t - Z.pos (Pos.of_succ_nat n).
Proof. rewrite Zpos_P_of_succ_nat. omega. Qed.


Lemma all_tsub_monotone ts' ts u : all2 tle ts' ts -> all2 tle (map (tsub u) ts') (map (tsub u) ts).
Proof.
  intro A. induction A;simpl;constructor.
  - destruct x,y; inversion H; simpl; constructor. omega.
  - assumption.
Qed.


Lemma all2_tle_refl x : all2 tle x x.
Proof.
  induction x;eauto using tle_refl.
Qed.

Lemma CausalC_open t t' ts ts' c : all2 tle ts' ts -> t' <= t -> CausalC ts t c -> CausalC ts' t' c.
Proof.
  intros A T C. generalize dependent ts'. generalize dependent ts. 
  generalize dependent t. generalize dependent t'. 
  induction c; intros;inversion C;subst;eauto using CausalE_open, all_tsub_monotone.
  - econstructor; eauto. eapply CausalE_open in H4; eauto. 
    eapply IHc2; eauto using all_tsub_monotone, all2_tle_refl.
Qed.


Lemma CausalC_empty ts t c tr i env ext : CausalC ts (Time t) c -> C[|c|]env ext = Some tr -> (Z.of_nat i < t)%Z
                                           -> tr i = empty_trans.
Proof.
  generalize dependent env. generalize dependent ext. generalize dependent tr. 
  generalize dependent i. generalize dependent ts. generalize dependent t.
  induction c;intros t ts i tr ext env C R I; simpl in *.
  - inversion R. reflexivity.
  - option_inv_auto. inversion C. subst. eapply IHc; eauto.
  - inversion C. subst. inversion H2. subst. eapply Z.lt_le_trans in H1;eauto. 
    assert (0 = Z.of_nat 0) as Z by reflexivity.
    rewrite Z in H1. rewrite <- Nat2Z.inj_lt in H1. inversion H1.
  - option_inv_auto. inversion C. subst. rewrite <- scale_empty_trans with (r:=x). unfold scale_trace,compose.
    f_equal. eapply IHc; eauto. 
    eapply CausalC_open with (ts:=ts) (t:=t0); eauto using all2_tle_refl,tle_trans.
  - option_inv_auto. inversion C. subst. unfold delay_trace. remember (leb n i) as L. destruct L;try reflexivity. 
    symmetry in HeqL. apply leb_complete in HeqL. eapply IHc in H0. apply H0. 
    apply H3. rewrite Nat2Z.inj_sub by assumption. omega.
  - option_inv_auto. erewrite <- add_empty_trans_l. inversion C. subst. unfold add_trace. 
    f_equal; [eapply IHc1|eapply IHc2]; eauto.
  - inversion C. clear C. subst. 
    assert (
        forall (i : nat) (tr : Trace) 
                      (ext : ExtEnv) (env : Env),
                 C[|c1|] env ext = Some tr -> (Z.of_nat i < t)%Z -> tr i = empty_trans) as IH1.
    intros. eauto. clear H6. clear H4.
    generalize dependent ext. generalize dependent env. 
    generalize dependent t. generalize dependent ts. generalize dependent tr. generalize dependent i. 
    induction n; intros.
    + simpl in *. destruct (E[|e|] env ext);tryfalse. destruct v;tryfalse. destruct b.
      * eapply IH1;eauto.
      * eapply IHc2; eauto. rewrite Z.add_0_r. assumption.
    + simpl in *.  destruct (E[|e|] env ext);tryfalse. destruct v;tryfalse. destruct b.
      * eapply IH1 in R; eauto.
      * option_inv_auto. unfold delay_trace. remember (leb 1 i) as L. destruct L; try reflexivity.
        symmetry in HeqL. apply leb_complete in HeqL.
        eapply IHn with (t:=(t - 1)) (ts:=map (tsub 1) ts); auto. 
        rewrite Nat2Z.inj_sub by assumption. 
        simpl. omega. autounfold. simpl. rewrite Z.add_opp_r. rewrite prec_of_nat. 
        rewrite map_map. erewrite map_ext. eassumption. 
        intros. autounfold. rewrite tadd_tadd. f_equal. rewrite Nat2Z.inj_succ. omega.
        intros. eapply IH1; eauto. omega. apply H0.
Qed.

Lemma CausalC_empty' ts t c tr i env ext : CausalC ts t c -> C[|c|]env ext = Some tr -> Time (Z.of_nat i) < t
                                           -> tr i = empty_trans.
Proof.
  intros. destruct t; inversion H1. eapply CausalC_empty;eauto.
Qed.

Lemma all2_map_forall {A B} f l (P : A -> B -> Prop) : (forall x, P (f x) x) -> all2 P (map f l) l.
Proof.
  intro G. induction l;simpl;constructor;auto.
Qed.

Lemma CausalC_sound' ts t t1 t2 i env1 env2 r1 r2 c : 
  CausalC ts t c -> env_until (Time (Z.of_nat i)) ts env1 env2 ->
  ext_until (Z.of_nat i) r1 r2 -> C[|c|]env1 r1 = Some t1 -> C[|c|] env2 r2 = Some t2 ->
  t1 i = t2 i.
Proof.
  intros C V X C1 C2. 
  generalize dependent ts. generalize dependent t. generalize dependent r1. generalize dependent r2.
  generalize dependent env1. generalize dependent env2. generalize dependent i.
  generalize dependent t1. generalize dependent t2.
  induction c; intros; inversion C;subst;clear C.
  - simpl in *. inversion C1. inversion C2. reflexivity.
  - simpl in *. option_inv_auto. eapply IHc; eauto. constructor;auto.
    intro. rewrite CausalE_sound in H0;eauto. rewrite H0 in H2. 
    inversion H2. subst. reflexivity. eapply env_until_weaken; eassumption.
    destruct t';auto. simpl. inversion H. subst.
    eapply ext_until_le. eassumption. assumption. 
  - simpl in *. inversion C1. inversion C2. reflexivity.
  - simpl in *. option_inv_auto. unfold scale_trace, compose. erewrite IHc; eauto.
    cases (t0 <=? Time (Z.of_nat i)) as I. rewrite tleb_tle in I.
    rewrite CausalE_sound in H6;eauto. rewrite H6 in H7. inversion H7. subst.
    destruct x3; tryfalse. rewrite H8 in H9. inversion H9. reflexivity.
    eapply env_until_weaken. eassumption. assumption.
    destruct t0;auto. eapply ext_until_le. eassumption. inversion I. assumption.
    rewrite tleb_tgt in I. eapply CausalC_empty' in H3;eauto. rewrite H3. 
    do 2 rewrite scale_empty_trans. reflexivity.
  - simpl in *. option_inv_auto. 
    cases (t <=? Time (Z.of_nat i)) as I. rewrite tleb_tle in I.
    unfold delay_trace. remember (leb n i) as L.
    destruct L; try reflexivity. symmetry in HeqL. apply leb_complete in HeqL.
    eapply IHc with (t:= tsub' n t). eauto. rewrite ext_until_adv. rewrite Nat2Z.inj_sub by assumption.
    eapply ext_until_le. eassumption.  omega. eauto. 
    destruct t; inversion I;subst; simpl;autounfold; eauto.
    rewrite Nat2Z.inj_sub by assumption. 
    apply env_until_monotone with (f := tsub' n) in V. 
    eassumption.
    intros. eauto using tle_tsub'_rev. 
    
    rewrite tleb_tgt in I. unfold delay_trace. cases (leb n i) as L;try reflexivity.
    apply leb_complete in L.
    assert (Time (Z.of_nat (i - n)) < tsub' n t) as I'.
    unfold tsub'. inversion I. subst. simpl. constructor. rewrite Nat2Z.inj_sub by assumption.
    omega.
    eapply CausalC_empty' in H0;eauto. eapply CausalC_empty' in H1;eauto.
    rewrite H0, H1. reflexivity.
  - simpl in *. option_inv_auto. unfold add_trace. f_equal; [eapply IHc1|eapply IHc2]; eauto.
  - simpl in *. apply CausalE_sound in H4. unfold causalE in *.
    assert (
        forall (t2 t1 : Trace) (i : nat) (env2 env1 : list Val)
           (r2 : ExtEnv),
         C[|c1|] env2 r2 = Some t2 ->
         forall r1 : ExtEnv,
         C[|c1|] env1 r1 = Some t1 ->
         ext_until (Z.of_nat i) r1 r2 ->
         env_until (Time (Z.of_nat i)) ts env1 env2 -> t1 i = t2 i) as IH1.
    intros. remember (t <=? Time (Z.of_nat i0)) as L. symmetry in HeqL. destruct L.
    rewrite tleb_tle in HeqL. eapply IHc1;eauto. rewrite tleb_tgt in HeqL.
    eapply CausalC_empty' in H; eauto. eapply CausalC_empty' in H0; eauto. 
    rewrite H. rewrite H0. reflexivity. 

    clear H6. clear IHc1.
    generalize dependent ts. generalize dependent t. generalize dependent r1. generalize dependent r2.
    generalize dependent env1. generalize dependent env2. generalize dependent i.
    generalize dependent t1. generalize dependent t2.
    induction n;intros.
    + simpl in *. rewrite H4 with (env2:=env2) (ext2:=r2) in C1;auto.
      destruct (E[|e|] env2 r2);tryfalse. destruct v;tryfalse. rewrite tsub'_0 in *. 
      destruct b; [eapply IH1|eapply IHc2]; eauto. erewrite map_ext. rewrite map_id. assumption.
      intros. eauto.
      eapply env_until_weaken. eassumption. constructor. omega.
      eapply ext_until_le. eassumption. omega.
    + simpl in *. rewrite H4 with (env2:=env2) (ext2:=r2) in C1;auto.
      destruct (E[|e|] env2 r2);tryfalse. destruct v;tryfalse. destruct b.
        eapply IH1; eauto.
        option_inv_auto. unfold delay_trace. remember (leb 1 i) as L. destruct L;try reflexivity.
        symmetry in HeqL. apply leb_complete in HeqL.
        eapply IHn with (t:=tsub' 1 t) (ts :=map (tsub' 1) ts);clear IHn;eauto. 
        * rewrite ext_until_adv. eapply ext_until_le.
          apply X. rewrite Nat2Z.inj_sub by assumption. 
          assert (Z.of_nat 1 = 1) as E by reflexivity. rewrite E. omega. 
        * apply env_until_monotone with (f:=tsub' 1) in V. 
          rewrite Nat2Z.inj_sub by assumption. apply V.
          intros. eauto using tle_tsub'_rev.
        * intros. apply H4. 
          eapply env_until_weaken'. eassumption. apply all2_map_forall. intro. 
          destruct x1. simpl. autounfold. constructor. omega. auto.
          assumption.
        * assert (- Z.of_nat n + - Z.of_nat 1 = - Z.of_nat (S n)) as E
            by (repeat rewrite Nat2Z.inj_succ; simpl; omega).
          rewrite map_map. autounfold in *. 
          rewrite tadd_tadd. erewrite map_ext. 
          rewrite E. apply H7. intros. rewrite tadd_tadd. rewrite E. reflexivity.
        * intros. eapply IH1;eauto. 
          eapply env_until_weaken'. eassumption. apply all2_map_forall. intro. 
          destruct x1. simpl. autounfold. constructor. omega. auto.
        * eapply env_until_weaken. eassumption. constructor. omega.
        * eapply ext_until_le. eassumption. omega.
Qed.


Theorem CausalC_sound t c : CausalC nil t c  -> causal c.
Proof.
  intros C. unfold causal. intros. 
  remember (t <=? Time (Z.of_nat d)) as L. symmetry in HeqL. destruct L.
  - rewrite tleb_tle in HeqL. eapply CausalC_sound'; eauto. constructor.
  - rewrite tleb_tgt in HeqL.
    eapply CausalC_empty' in H0; eauto. eapply CausalC_empty' in H1; eauto. 
    rewrite H0. rewrite H1. reflexivity.
Qed.


Lemma map_tadd_swap n m l : map (tadd n) (map (tadd m) l) = map (tadd m) (map (tadd n) l).
Proof. 
  repeat rewrite map_map. apply map_ext. auto using tadd_swap.
Qed.

Lemma translateExp_timed d e ts t : CausalE ts t e -> CausalE (map (tadd d) ts) (tadd d t) (translateExp d e).
Proof.
  intro T. generalize dependent ts.  generalize dependent t. generalize dependent d. 
  induction e using Exp_ind'; intros; simpl; inversion T; clear T;subst; auto.
  - econstructor. induction H;simpl in *;constructor;inversion H3;subst;eauto.
  - econstructor. eapply tle_tadd in H2. simpl in H2. rewrite Z.add_comm. apply H2.
  - econstructor. induction H2;simpl;eauto.
  - econstructor. unfold tadd'. rewrite tadd_swap. rewrite map_tadd_swap.
    eauto. eauto. eapply IHe1 in H5. simpl in *. eauto.
Qed.