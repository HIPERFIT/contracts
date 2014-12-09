Require Import Causality.
Require Import Advance.
Require Import FunctionalExtensionality.
Require Import Tactics.
Require Import Utils.

(* Contextual syntactic causality. This syntactic notion of causality
is more permissive than plain syntactic causality. However, the
causality property that follows from this syntactic notion of
causality is slightly weaker. *)

Open Scope Z.


(* Definition of the inference rules for contextual causality. *)

Definition TimeEnv := list Z.

Inductive CausalV : TimeEnv -> Z -> Var -> Prop :=
| causal_V1 t t' g  : t <= t' -> CausalV (t :: g) t' V1
| causal_VS g v t t' : CausalV g t v -> CausalV (t' :: g) t (VS v).


Inductive CausalE : TimeEnv -> Z -> Exp -> Prop:= 
 | causal_op t ts op args : all (CausalE ts t) args -> CausalE ts t (OpE op args)
 | causal_obs l t' t ts : t' <= t -> CausalE ts t (Obs l t')
 | causal_var t ts v : CausalV ts t v -> CausalE ts t (VarE v)
 | causal_acc t t' ts e1 e2 n : CausalE (map (fun x => x + Z.of_nat n) ts) (t + Z.of_nat n) e2
                                -> CausalE (t' :: ts) t e1
                                -> CausalE ts t (Acc e1 n e2)
  .



Inductive CausalC : TimeEnv -> Z -> Contr -> Prop :=
| causal_zero ts t : CausalC ts t Zero
| causal_translate ts t d c : CausalC (map (fun x => x - Z.of_nat d) ts) (t - Z.of_nat d) c
                                     -> CausalC ts t (Translate d c)
| causal_let ts t t' e c : CausalE ts t' e -> CausalC (t' :: ts) t c -> CausalC ts t (Let e c)
| causal_scale ts t e c : CausalE ts t e -> CausalC ts t c -> CausalC ts t (Scale e c)
| causal_both ts t c1 c2 : CausalC ts t c1 -> CausalC ts t c2 -> CausalC ts t (Both c1 c2)
| causal_transfer t ts p1 p2 a : t <= 0 -> CausalC ts t (Transfer p1 p2 a)
| causal_if ts t d e c1 c2 : CausalE ts 0 e -> CausalC ts t c1
                             -> CausalC (map (fun x => x - Z.of_nat d) ts) (t - Z.of_nat d) c2
                             -> CausalC ts t (If e d c1 c2)
.

(* Contextual causality is 'open': i.e. it is (anti-)monotone w.r.t. ordering on time. *)

Lemma CausalV_open t t' ts ts' (v : Var) : all2 Z.le ts' ts -> t <= t' -> CausalV ts t v -> CausalV ts' t' v.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'. generalize dependent ts. generalize dependent ts'.
  induction v; intros; inversion P; subst.
  - inversion Is. subst. constructor. omega.
  - inversion Is. subst. constructor. eauto.
Qed.

Lemma CausalE_open t t' ts ts' (e : Exp) : all2 Z.le ts' ts -> t <= t' -> CausalE ts t e -> CausalE ts' t' e.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'.
  generalize dependent ts. generalize dependent ts'.
  induction e using Exp_ind'; intros;inversion P;subst;econstructor.
  - induction args.
    * constructor.
    * inversion H3. inversion H. subst. constructor. eauto. apply IHargs. auto. constructor. auto. auto.
  - omega.
  - eapply CausalV_open; eauto. 
  - eapply IHe2; eauto. apply all2_map. intros. omega. assumption. omega.
  - eapply IHe1 in H5.  apply H5; auto. constructor; auto. apply Z.le_refl. assumption.
Qed.


Lemma CausalV_shift ts t v d : 0 <= d -> CausalV ts t v -> CausalV (map (fun x => x + d) ts) (t + d) v.
Proof.
  intros D V. induction V;constructor. omega. assumption.
Qed.

Lemma CausalE_shift ts t e d : 0 <= d -> CausalE ts t e -> CausalE (map (fun x => x + d) ts) (t + d) e.
Proof.
  intros D C. generalize dependent d. generalize dependent ts. generalize dependent t.
  induction e using Exp_ind';intros;inversion C; subst. 
  - constructor. do 2 eapply all_apply in H; eauto. 
    eapply all_mp in H3; try eapply H. do 2 eapply all_apply in H3; eauto.
  - constructor. omega.
  - constructor. apply CausalV_shift;assumption.
  - econstructor.
    * eapply IHe2 in H3. rewrite map_map in *. 
      rewrite <- Z.add_assoc. rewrite Z.add_comm with (n:=d0). rewrite Z.add_assoc. erewrite map_ext.
      apply H3. intros. simpl. omega. omega.
    * eapply IHe1 in H5. simpl in H5. apply H5. assumption.
Qed.

Corollary CausalE_shift_1 ts t e : CausalE ts t e -> CausalE (map (fun x => x + 1) ts) (t + 1) e.
Proof.
  intros. apply CausalE_shift. omega. assumption.
Qed.

Definition env_until {A} t := all3 (B:=A) (fun t' x y => t' <= t -> x = y).

Lemma env_until_monotone {A} t ts f (e1 e2 : list A) : (forall x y, f x <= f y -> x <= y)
                                                  -> env_until t ts e1 e2 -> env_until (f t) (map f ts) e1 e2.
Proof.
  intros M U. induction U; constructor;auto. 
Qed.


Lemma env_until_monotone' {A} t ts f (e1 e2 : list A) : (forall x y, x <= y -> f x <= f y)
                                                        -> env_until (f t) (map f ts) e1 e2
                                                        ->  env_until t ts e1 e2.
Proof.
  intros M U. remember (map f ts) as ts'. induction U; destruct ts;tryfalse;constructor;
                                          simpl in *; inversion Heqts'; subst; auto. admit.
Qed.


Lemma env_until_weaken {A} t t' ts (vars1 vars2 : list A) : 
  env_until t ts vars1 vars2 -> t' <= t ->  env_until t' ts vars1 vars2.
Proof.
  intros U I. induction U;constructor;auto. intro. apply H. omega.
Qed.

Definition causalE ts t e := forall vars1 vars2 rho1 rho2, env_until t ts vars1 vars2 -> ext_until t rho1 rho2
                                                        -> E[|e|] vars1 rho1 = E[|e|]vars2 rho2.

(* Contextual causality implies semantic causality. *)

Lemma all_le_refl ts :  all2 Z.le ts ts.
Proof.
  induction ts; constructor; eauto. apply Z.le_refl.
Qed.

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
  - unfold causalE. intros. simpl. unfold ext_until in *. rewrite H0; auto.
  - induction H2. 
    + unfold causalE. intros. inversion H0. subst. simpl. f_equal. auto.
    + unfold causalE in *. intros. inversion H. subst. simpl in *. eapply IHCausalV; eauto. constructor. auto.
  - unfold causalE. intros. simpl. generalize dependent t'. 
    generalize dependent t. generalize dependent ts.
    generalize dependent rho1. generalize dependent rho2. induction d; intros.
    + simpl. do 2 rewrite adv_ext_0. unfold causalE in IHe2. simpl in H3.
      rewrite Z.add_0_r in H3. eapply IHe2; eauto. erewrite map_ext. rewrite map_id. assumption.
      intros; omega.
    + simpl. apply bind_equals. 
      * do 2 rewrite adv_ext_step'. eapply IHd with (t := (t + 1)) (ts:= map (fun x => x + 1) ts); eauto. 
        apply causal_acc with (t' := t' +1). 
        rewrite succ_of_nat. rewrite map_map. rewrite map_ext with (g:=(fun x : Z => x + Z.of_nat (S d))).
        assumption. intros. apply succ_of_nat. eapply CausalE_shift_1 in H5. simpl in H5. apply H5. 
        rewrite map_map. rewrite succ_of_nat. erewrite map_ext. apply H3. intros. apply succ_of_nat.
        apply env_until_monotone with (f := fun x => x + 1) in H. assumption. intros; omega.
        rewrite Z.add_comm. rewrite <- ext_until_adv. 
        do 2 rewrite adv_ext_iter. simpl. do 2 rewrite adv_ext_0. assumption.
        eapply CausalE_shift_1 in H5. simpl in H5. apply H5.
      * intros. unfold causalE in IHe1. eapply IHe1. eassumption. constructor. auto. auto.
        do 2 rewrite adv_ext_iter. rewrite Pos2Z.add_neg_pos. rewrite Z.pos_sub_diag.
        do 2 rewrite adv_ext_0. assumption.
Qed.

Lemma prec_of_nat t n : t - 1 - Z.of_nat n = t - Z.pos (Pos.of_succ_nat n).
Proof. rewrite Zpos_P_of_succ_nat. omega. Qed.

Lemma CausalC_empty ts t c tr i vars rho : CausalC ts t c -> C[|c|]vars rho = Some tr -> Z.of_nat i < t
                                           -> tr i = empty_trans.
Proof.
  generalize dependent vars. generalize dependent rho. generalize dependent tr. 
  generalize dependent i. generalize dependent ts. generalize dependent t.
  induction c;intros t ts i tr rho vars C R I; simpl in *.
  - inversion R. reflexivity.
  - option_inv_auto. inversion C. subst. eapply IHc; eauto.
  - inversion C. subst. eapply Z.lt_le_trans in H2;eauto. assert (0 = Z.of_nat 0) as Z by reflexivity.
    rewrite Z in H2. rewrite <- Nat2Z.inj_lt in H2. inversion H2.
  - option_inv_auto. inversion C. subst. rewrite <- scale_empty_trans with (r:=x). unfold scale_trace,compose.
    f_equal. eapply IHc; eauto.
  - option_inv_auto. inversion C. subst. unfold delay_trace. remember (leb n i) as L. destruct L;try reflexivity. 
    symmetry in HeqL. apply leb_complete in HeqL. eapply IHc in H0. apply H0. 
    apply H3. rewrite Nat2Z.inj_sub by assumption. omega.
  - option_inv_auto. erewrite <- add_empty_trans. inversion C. subst. unfold add_trace. 
    f_equal; [eapply IHc1|eapply IHc2]; eauto.
  - inversion C. clear C. subst. 
    assert (
        forall (i : nat) (tr : Trace) 
                      (rho : ExtEnv) (vars : Env),
                 C[|c1|] vars rho = Some tr -> Z.of_nat i < t -> tr i = empty_trans) as IH1.
    intros. eauto. clear H6. clear H4.
    generalize dependent rho. generalize dependent vars. 
    generalize dependent t. generalize dependent ts. generalize dependent tr. generalize dependent i. 
    induction n; intros.
    + simpl in *. destruct (E[|e|] vars rho);tryfalse. destruct v;tryfalse. destruct b.
      * eapply IH1;eauto.
      * eapply IHc2; eauto. rewrite Z.sub_0_r. assumption.
    + simpl in *.  destruct (E[|e|] vars rho);tryfalse. destruct v;tryfalse. destruct b.
      * eapply IH1 in R; eauto.
      * option_inv_auto. unfold delay_trace. remember (leb 1 i) as L. destruct L; try reflexivity.
        symmetry in HeqL. apply leb_complete in HeqL.
        eapply IHn with (t:=(t - 1)) (ts:=map (fun x => x - 1) ts); auto. 
        rewrite Nat2Z.inj_sub by assumption. 
        simpl. omega. rewrite prec_of_nat. rewrite map_map. erewrite map_ext. eassumption. 
        intros. simpl. apply prec_of_nat.
        intros. eapply IH1; eauto. omega. apply H0.
Qed.




Lemma CausalC_sound ts t t1 t2 i vars1 vars2 r1 r2 c : 
  CausalC ts t c -> env_until t ts vars1 vars2 ->
  ext_until (Z.of_nat i) r1 r2 -> C[|c|]vars1 r1 = Some t1 -> C[|c|] vars2 r2 = Some t2 ->
  t <= Z.of_nat i -> t1 i = t2 i.
Proof.
  intros C V X C1 C2 I. 
  generalize dependent ts. generalize dependent t. generalize dependent r1. generalize dependent r2.
  generalize dependent vars1. generalize dependent vars2. generalize dependent i.
  generalize dependent t1. generalize dependent t2.
  induction c; intros; inversion C;subst;clear C.
  - simpl in *. inversion C1. inversion C2. reflexivity.
  - simpl in *. option_inv_auto. eapply IHc; eauto. constructor;auto.
    intro. rewrite CausalE_sound in H0;eauto. rewrite H0 in H2. 
    inversion H2. subst. reflexivity. eapply env_until_weaken; eassumption.
    eapply ext_until_le. eassumption. omega.
  - simpl in *. inversion C1. inversion C2. reflexivity.
  - simpl in *. option_inv_auto. unfold scale_trace, compose. erewrite IHc; eauto.
    rewrite CausalE_sound in H5; eauto. rewrite H5 in H6. inversion H6. subst.
    destruct x3; tryfalse. rewrite H7 in H8. inversion H8. reflexivity.
    eapply ext_until_le. eassumption. omega.
  - simpl in *. option_inv_auto. unfold delay_trace. remember (leb n i) as L.
    destruct L; try reflexivity. symmetry in HeqL. apply leb_complete in HeqL.
    eapply IHc; eauto. rewrite ext_until_adv. rewrite Nat2Z.inj_sub by assumption.
    eapply ext_until_le. eassumption.  omega. rewrite Nat2Z.inj_sub by assumption. omega.
    apply env_until_monotone with (f := (fun x1 : Z => x1 - Z.of_nat n)) in V. apply V.
    intros. omega.
  - simpl in *. option_inv_auto. unfold add_trace. f_equal; [eapply IHc1|eapply IHc2]; eauto.
  - simpl in *. apply CausalE_sound in H4. unfold causalE in *.
    assert (
        forall (t2 t1 : Trace) (i : nat) (vars2 vars1 : list Val)
           (r2 : ExtEnv),
         C[|c1|] vars2 r2 = Some t2 ->
         forall r1 : ExtEnv,
         C[|c1|] vars1 r1 = Some t1 ->
         ext_until (Z.of_nat i) r1 r2 ->
         t <= Z.of_nat i ->
         env_until t ts vars1 vars2 -> t1 i = t2 i) as IH1.
    intros. eapply IHc1;eauto. clear H6. clear IHc1.
    generalize dependent ts. generalize dependent t. generalize dependent r1. generalize dependent r2.
    generalize dependent vars1. generalize dependent vars2. generalize dependent i.
    generalize dependent t1. generalize dependent t2.
    induction n;intros.
    + simpl in *. rewrite H4 with (vars2:=vars2) (rho2:=r2) in C1;auto.
      destruct (E[|e|] vars2 r2);tryfalse. destruct v;tryfalse. rewrite Z.sub_0_r in *. 
      destruct b; [eapply IH1|eapply IHc2]; eauto. erewrite map_ext. rewrite map_id. assumption.
      intros. omega.
    + simpl in *. rewrite H4 with (vars2:=vars2) (rho2:=r2) in C1;auto.
      destruct (E[|e|] vars2 r2);tryfalse. destruct v;tryfalse. destruct b.
        eapply IH1; eauto.
        option_inv_auto. unfold delay_trace. remember (leb 1 i) as L. destruct L;try reflexivity.
        symmetry in HeqL. apply leb_complete in HeqL.
        eapply IHn with (t:=t-1) (ts :=map (fun x => x - 1) ts);clear IHn;eauto. 
        * rewrite ext_until_adv. eapply ext_until_le.
          apply X. omega. 
        * rewrite Nat2Z.inj_sub by assumption. simpl. omega.
        * apply env_until_monotone with (f:=fun x1 : Z => x1 - 1) in V. apply V.
          intros. omega. 
        * intros. apply H4. apply env_until_monotone' with (f:=fun x1 : Z => x1 - 1) in H. apply H.
          intros. omega. auto. admit.
        * rewrite map_map. rewrite prec_of_nat. erewrite map_ext. apply H7. intros. apply prec_of_nat.
        *   intros. eapply IH1;eauto.