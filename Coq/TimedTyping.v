Require Import Typing.
Require Import ContextualCausality.
Require Import Tactics.
Require Import Utils.
Require Import Environments.

(* A type system with time-indexed types. This system subsumes both
the type system and the contextual causality system. *)

Open Scope Z.

(* Timed types *)

Inductive TiTy := TimedType (ty : Ty) (ti : TimeB).

Infix "^" := TimedType.

(* Selector functions to extract the time and the type of a timed
type. *)

Definition time (t : TiTy)  := match t with TimedType _ ti => ti end.
Definition type (t : TiTy) := match t with TimedType ty _ => ty end.

(* Convenience function to add time to a timed type. *)

Definition add_time d (t : TiTy) := match t with TimedType ty ti => TimedType ty (tadd' d ti) end.
Definition sub_time d (t : TiTy) := match t with TimedType ty ti => TimedType ty (tsub' d ti) end.

(* A time timed time environment maps variables to timed types.  *)

Definition TiTyEnv := Env' TiTy.

Open Scope time.

(* Definition of the timed type inference rules for variables,
operators, expressions and contracts. *)

Inductive TiTyV : TiTyEnv -> TiTy -> Var -> Prop :=
| causal_V1 t t' g  : type t = type t' -> time t <= time t' -> TiTyV (t :: g) t' V1
| causal_VS g v t t' : TiTyV g t v -> TiTyV (t' :: g) t (VS v).

Definition TiTyOp (op : Op) (ts : list TiTy) (t:TiTy) : Prop
  := (all (fun t' => time t' = time t) ts) /\ TypeOp op (map type ts) (type t).

Lemma TiTyOp_TypeOp op ts t ty tys : 
  TypeOp op tys ty -> 
  (all (fun t' => time t' = time t) ts) -> 
  tys = map type ts -> ty = type t -> 
  TiTyOp op ts t.
Proof.
  intros. subst. firstorder.
Qed.

Inductive TiTyE : TiTyEnv -> TiTy -> Exp -> Prop:= 
 | causal_op t ts ts' op args : TiTyOp op ts' t -> all2 (TiTyE ts) ts' args -> TiTyE ts t (OpE op args)
 | causal_obs l t' t ts : Some t' <= time t -> |-O l ∶ type t ->  TiTyE ts t (Obs l t')
 | causal_var t ts v : TiTyV ts t v -> TiTyE ts t (VarE v)
 | causal_acc t ts e1 e2 n : TiTyE (map (add_time n) ts) (add_time n t) e2
                             -> TiTyE (type t ^ None :: ts) t e1
                             -> TiTyE ts t (Acc e1 n e2)
  .



Inductive TiTyC : TiTyEnv -> TimeB -> Contr -> Prop :=
| causal_zero ts t : TiTyC ts t Zero
| causal_translate ts t d c : TiTyC (map (sub_time d) ts) (tsub' d t) c
                                     -> TiTyC ts t (Translate d c)
| causal_let ts t t' e c : TiTyE ts t' e -> TiTyC (t' :: ts) t c -> TiTyC ts t (Let e c)
| causal_scale ts ti e c : TiTyE ts (REAL ^ ti) e -> TiTyC ts ti c -> TiTyC ts ti (Scale e c)
| causal_both ts t c1 c2 : TiTyC ts t c1 -> TiTyC ts t c2 -> TiTyC ts t (Both c1 c2)
| causal_transfer t ts p1 p2 a : t <= Some 0 -> TiTyC ts t (Transfer p1 p2 a)
| causal_if ts t d e c1 c2 : TiTyE ts (BOOL ^ Some 0) e -> TiTyC ts t c1
                             -> TiTyC (map (sub_time d) ts) (tsub' d t) c2
                             -> TiTyC ts t (If e d c1 c2)
.

Hint Constructors TiTyV TiTyE TiTyC.

(* We now show that timed typing implies both well-typing and
contextual causality. *)

Lemma TiTyV_type ts t v : TiTyV ts t v -> map type ts |-X v ∶ type t.
Proof. 
  intro T. induction T;simpl in *; try rewrite H; auto.
Qed.

Lemma type_add_time d t :  type (add_time d t) = type t.
Proof.
  destruct t. reflexivity.
Qed.
Lemma type_sub_time d t :  type (sub_time d t) = type t.
Proof.
  destruct t. reflexivity.
Qed.

(* Timed typing on expressions implies well-typing. *)

Lemma TiTyE_type ts t e : TiTyE ts t e -> map type ts |-E e ∶ type t.
Proof.
  intros T. generalize dependent ts. generalize dependent t.
  induction e using Exp_ind';intros;inversion T;simpl in T; subst.
  - unfold TiTyOp in *. destruct H4. econstructor;eauto. clear H1. clear T.
    generalize dependent t.
    induction H5;intros; simpl in *; constructor;inversion H;inversion H1;subst; auto.
    eapply IHall2;eauto. 
  - auto.
  - constructor. apply TiTyV_type. assumption.
  - constructor. 
    + apply IHe1 in H5. simpl in *. assumption.
    + apply IHe2 in H3. rewrite map_map in *. rewrite type_add_time in *. 
      erewrite map_ext. eassumption. intros. simpl. rewrite type_add_time. reflexivity.
Qed.

Hint Resolve TiTyE_type.

(* Timed typing implies well-typing. *)

Theorem TiTyC_type ts t e : TiTyC ts t e -> map type ts |-C e.
Proof.
  intros T. induction T; econstructor;simpl in *;eauto.
  - rewrite map_map in IHT. erewrite map_ext. eassumption. intro. simpl.
    rewrite type_sub_time. reflexivity.
  - apply TiTyE_type in H. simpl in H. apply H.
  - apply TiTyE_type in H. simpl in H. apply H.
  - rewrite map_map in IHT2. erewrite map_ext. eassumption. intro. simpl.
    rewrite type_sub_time. reflexivity.
Qed.


Lemma TiTyV_time ts t v : TiTyV ts t v -> CausalV (map time ts) (time t) v.
Proof. 
  intro T. induction T;simpl in *; try rewrite H; auto.
Qed.

Lemma time_add_time d t :  time (add_time d t) = tadd' d (time t).
Proof.
  destruct t. reflexivity.
Qed.
Lemma time_sub_time d t :  time (sub_time d t) = tsub' d (time t).
Proof.
  destruct t. reflexivity.
Qed.

(* Timed typing on expressions implies contextual causality. *)

Lemma TiTyE_time ts t e : TiTyE ts t e -> CausalE (map time ts) (time t) e.
Proof.
  intros T. generalize dependent ts. generalize dependent t.
  induction e using Exp_ind';intros;inversion T;simpl in T; subst.
  - unfold TiTyOp in *. destruct H4. econstructor;eauto. clear H1. clear T.
    generalize dependent t.
    induction H5;intros; simpl in *; constructor;inversion H;inversion H1;subst; auto.
    rewrite <- H9. auto.
  - auto.
  - constructor. apply TiTyV_time. assumption.
  - econstructor. 
    + apply IHe2 in H3. rewrite map_map in *. rewrite time_add_time in *. 
      erewrite map_ext. eassumption. intros. simpl. rewrite time_add_time. reflexivity.
    + apply IHe1 in H5. simpl in *. eassumption.
Qed.

Hint Resolve TiTyE_type.

(* Timed typing implies contextual causality. *)

Theorem TiTyC_time ts t c : TiTyC ts t c -> CausalC (map time ts) t c.
Proof.
  intros T. induction T; econstructor;simpl in *;eauto.
  - rewrite map_map in *. erewrite map_ext. eassumption. intro. simpl.
    rewrite time_sub_time. reflexivity.
  - apply TiTyE_time in H. simpl in H. apply H.
  - apply TiTyE_time in H. simpl in H. apply H.
  - apply TiTyE_time in H. simpl in H. apply H.
  - rewrite map_map in *. erewrite map_ext. eassumption. intro. simpl.
    rewrite time_sub_time. reflexivity.
Qed.

(* Below we show that the conjunction of well typing and contextual
causality implies timed typing. *)

Infix "^^" := (zipWith TimedType) (at level 1).

Fixpoint repeat {A} (n : nat) (x : A) : list A :=
  match n with
    | O => nil
    | S m => x :: repeat m x
  end.


Lemma map_type tys tis : length tys = length tis -> map type tys ^^ tis = tys.
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis;tryfalse. simpl. f_equal. auto.
Qed.

Lemma map_time tys tis : length tys = length tis -> map time tys ^^ tis = tis.
Proof.
  generalize dependent tys. induction tis;intros. destruct tys; reflexivity.
  destruct tys;tryfalse. simpl. f_equal. auto.
Qed.

Lemma map_type_time ts : (map type ts) ^^ (map time ts) = ts.
Proof.
  induction ts;simpl;f_equal;try destruct a;eauto.
Qed.

Lemma map_type_repeat tys t : map type tys ^^ (repeat (length tys) t) = tys.
Proof.
  induction tys. reflexivity. simpl. f_equal. auto.
Qed.

Lemma map_add_time n tys tis : map (add_time n) tys ^^ tis = tys ^^ (map (tadd' n) tis).
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis. reflexivity.
  simpl. rewrite IHtys. reflexivity.
Qed.

Lemma map_sub_time n tys tis : map (sub_time n) tys ^^ tis = tys ^^ (map (tsub' n) tis).
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis. reflexivity.
  simpl. rewrite IHtys. reflexivity.
Qed.


Lemma type_TiTyE tis tys ti ty e : tys |-E e ∶ ty -> CausalE tis ti e -> TiTyE tys^^tis (ty^ti) e.
Proof.
  intros Ty Ti. generalize dependent tis. generalize dependent ti. 
  induction Ty using TypeExp_ind';intros;inversion Ti;subst;clear Ti.
  - apply causal_op with (ts' := ts ^^ (repeat (length ts) ti)). unfold TiTyOp. split. 
    clear H. clear H0. clear H1. induction ts;simpl; constructor. reflexivity. apply IHts.
    rewrite map_type_repeat. simpl. assumption.
    clear H. induction H0;simpl;constructor;inversion H1;inversion H5;subst;auto.
  - eauto.
  - econstructor. generalize dependent tis. generalize dependent ti. 
    induction H;intros;inversion H3; clear H3;subst;simpl; econstructor; eauto.
  - apply causal_acc. simpl. rewrite map_add_time. eauto.
    specialize (IHTy1 ti (None :: tis)). eauto.
Qed.

Theorem type_TiTyC tis tys ti  c : tys |-C c -> CausalC tis ti c -> TiTyC tys^^tis ti c.
Proof.
  intros Ty Ti. generalize dependent tis. generalize dependent ti. 
  induction Ty;intros;inversion Ti;subst;clear Ti;eauto using type_TiTyE.
  - specialize (IHTy ti (t' :: tis)).  eauto using type_TiTyE.
  - econstructor. rewrite map_sub_time. eauto.
  - econstructor; eauto using type_TiTyE. rewrite map_sub_time. eauto.
Qed.


Theorem TiTyE_decompose ts t e : TiTyE ts t e <-> map type ts |-E e ∶ type t /\ CausalE (map time ts) (time t) e.
Proof.
  split; intros. split; eauto using TiTyE_type, TiTyE_time. destruct H. 
  eapply type_TiTyE in H;eauto. rewrite map_type_time in H. destruct t;simpl in H. assumption.
Qed.


Theorem TiTyC_decompose ts ti c : TiTyC ts ti c <-> map type ts |-C c /\ CausalC (map time ts) ti c.
Proof.
  split; intros. split; eauto using TiTyC_type, TiTyC_time. destruct H. 
  eapply type_TiTyC in H;eauto. rewrite map_type_time in H. assumption.
Qed.

Theorem TiTyC_decompose' tis tys ti c : length tys = length tis ->
                                       (TiTyC tys^^tis ti c <-> tys |-C c /\ CausalC tis ti c).
Proof.
  intro L. split; intros. split. apply TiTyC_type in H. rewrite map_type in H;auto. 
  apply TiTyC_time in H. rewrite map_time in H; auto. destruct H. apply type_TiTyC;auto.
Qed.

Definition subtype (t1 t2 : TiTy) := type t1 = type t2 /\ time t1 <= time t2.

Infix "<|" := subtype (at level 1).

Hint Unfold subtype.

Lemma subtype_type t1 t2 : t1 <| t2 -> type t1 = type t2.
Proof.
  intros. unfold subtype in *. tauto.
Qed.
Lemma subtype_time t1 t2 : t1 <| t2 -> time t1 <= time t2.
Proof.
  intros. unfold subtype in *. tauto.
Qed.

Hint Resolve subtype_time subtype_type.

Lemma all_subtype_type ts1 ts2 : all2 subtype ts1 ts2 -> map type ts1 = map type ts2.
Proof.
  intro H. induction H; simpl; f_equal; eauto.
Qed.

Lemma all_subtype_time ts1 ts2 : all2 subtype ts1 ts2 -> all2 tle (map time ts1) (map time ts2).
Proof.
  intro H. induction H; simpl; f_equal; eauto.
Qed.

Hint Resolve all_subtype_time all_subtype_type.

Lemma TiTyE_open t t' ts ts' (e : Exp) : all2 subtype ts' ts -> t <| t' -> TiTyE ts t e -> TiTyE ts' t' e.
Proof.
  intros Ss S T. rewrite TiTyE_decompose in *. destruct T. destruct S as [S1 S2].
  split. rewrite <- S1. erewrite all_subtype_type by eassumption. assumption.
  eapply CausalE_open;eauto.
Qed.


Definition inferObs (l : ObsLabel) : Ty :=
  match l with
    | LabR _ => REAL
    | LabB _ => BOOL
  end.


Lemma inferObs_sound l : |-O l ∶ inferObs l.
Proof.
  destruct l; auto.
Qed.

Import ListNotations. 

Definition tyeqb (t1 t2 : Ty) : bool :=
  match t1, t2 with
    | REAL, REAL => true
    | BOOL, BOOL => true
    | _,_ => false
  end.

Lemma tyeqb_iff t1 t2 : tyeqb t1 t2 = true <-> t1 = t2.
Proof.
  destruct t1;destruct t2; split;intro;simpl in *; congruence.
Qed.

Definition inferOp (op : Op) (args : list Ty) : option Ty :=
  match op with
    | Add => match args with [REAL;REAL] => Some REAL | _ => None end
    | Sub => match args with [REAL;REAL] => Some REAL | _ => None end
    | Mult => match args with [REAL;REAL] => Some REAL | _ => None end
    | Div => match args with [REAL;REAL] => Some REAL | _ => None end
    | And => match args with [BOOL;BOOL] => Some BOOL | _ => None end
    | Or => match args with [BOOL;BOOL] => Some BOOL | _ => None end
    | Less => match args with [REAL;REAL] => Some BOOL | _ => None end
    | Leq => match args with [REAL;REAL] => Some BOOL | _ => None end
    | Equal => match args with [REAL;REAL] => Some BOOL | _ => None end
    | Not => match args with [BOOL] => Some BOOL | _ => None end
    | Neg => match args with [REAL] => Some REAL | _ => None end
    | BLit _ => match args with [] => Some BOOL | _ => None end
    | RLit _ => match args with [] => Some REAL | _ => None end
    | Cond => match args with [BOOL;t1;t2] => if tyeqb t1 t2 then Some t1 else None | _ => None end
  end.

Lemma inferOp_TypeOp op args ty : inferOp op args = Some ty <-> |-Op op ∶ args => ty.
Proof.
  destruct op; split; intro H; repeat (destruct args;try destruct t; simpl in *; try solve [inversion H;eauto]).
Qed.

Definition tmax (t1 t2 : option Z) : option Z :=
  match t1,t2 with
    | None, _ => t2
    | _, None => t1
    | Some t1', Some t2' => Some (Z.max t1' t2')
  end.


Lemma tmax_tle_iff t t1 t2 : t <= tmax t1 t2 <-> t <= t1 \/ t <= t2.
Proof.
  destruct t;split;firstorder; destruct t1, t2; inversion H; try rewrite -> Z.max_le_iff in H2; firstorder;
  constructor; rewrite -> Z.max_le_iff; tauto.
Qed.

Lemma tmax_lub_iff  t t1 t2 : tmax t1 t2 <= t <-> t1 <= t /\ t2 <= t.
Proof.
    destruct t;split;firstorder destruct t1, t2; simpl in H; inversion_clear H;
    try constructor; try rewrite -> Z.max_lub_iff in H0; firstorder.
    rewrite -> Z.max_lub_iff. inversion H0. tauto. inversion H0. tauto.
Qed.

(* Define as left fold instead (and then prove that it is equal to the right fold). *)
Definition tmaxs (ts : list (option Z)) : option Z :=fold_right tmax None ts.

Lemma tmaxs_cons x xs : tmaxs (x :: xs) = tmax x (tmaxs xs).
Proof.
  unfold tmaxs. fold ([x] ++ xs). rewrite fold_right_app. reflexivity.
Qed.

Fixpoint inferE (env : TiTyEnv) (e:Exp) : option TiTy :=
  match e with
    | OpE op args => sequence (map (inferE env) args) >>=
                              (fun args' => liftM (fun ty => ty ^ tmaxs (map time args')) 
                                                  (inferOp op (map type args')))
    | VarE v => lookupEnv v env
    | Obs l i => Some (inferObs l ^ Some i)
    | Acc f d z => inferE (map (add_time d) env) z >>= 
                  (fun t => inferE (type t ^ None :: env) f >>= 
                  (fun t' => if tyeqb (type t) (type t') 
                             then Some (type t ^ tmax (tsub' d (time t)) (time t')) 
                             else None))
  end.


Lemma subtype_refl t : t <| t.
Proof. destruct t. auto. Qed.

Hint Immediate subtype_refl.

Lemma all_subtype_refl ts :  all2 subtype ts ts.
Proof.
  induction ts; eauto. 
Qed.

Lemma all_type_tle args ts env m : 
  all2 (TiTyE env) ts args
  -> tmaxs (map time ts) <= m
  -> all2 (TiTyE env) (map (fun t => type t ^ m) ts) args.
Proof.
  intros T M. rewrite <- map_id. apply all2_map'. generalize dependent m. induction T;intros m M;constructor.
  - simpl. eapply TiTyE_open with (t:=x). apply all_subtype_refl. constructor. reflexivity.
    simpl in *. rewrite tmax_lub_iff in M. tauto. assumption.
  - apply IHT. simpl in M. rewrite tmax_lub_iff in M. tauto.
Qed.

Corollary all_type_max args ts env : 
  all2 (TiTyE env) ts args
  -> all2 (TiTyE env) (map (fun t => type t ^ tmaxs (map time ts)) ts) args.
Proof.
  intros. apply all_type_tle;auto.
Qed.

Theorem inferE_sound env e t :
   inferE env e = Some t -> TiTyE env t e.
Proof.
  intros I. generalize dependent env. generalize dependent t.
  induction e using Exp_ind'; intros; simpl in *;option_inv_auto.
  - assert (all2 (TiTyE env) x args) as T. clear H3.
    generalize dependent x. induction H; simpl in *; intros.
    inversion H1. auto.
    option_inv_auto. constructor. eapply TiTyE_open with (t:=x2). apply all_subtype_refl.
    auto. auto. apply IHall. auto.

    apply all_type_max in T. remember (map (fun t => type t ^ tmaxs (map time x)) x) as x'.
    rewrite inferOp_TypeOp in *. apply causal_op with (ts':= x').
    constructor. simpl. subst. apply all_map_forall. auto. simpl.
    assert (map type x = map type x') as Tx.
    subst. induction x;simpl;f_equal. rewrite map_map. simpl. reflexivity.
    rewrite <- Tx. assumption. assumption.
  - inversion I as [I']. destruct l;eauto.
  - generalize dependent t. generalize dependent env.
    induction v.
    + constructor; destruct env; simpl in I; inversion I; auto.
    + constructor. destruct env; simpl in I;tryfalse. apply IHv in I. inversion I. auto.
  - destruct x; destruct x0; simpl in H3. cases (tyeqb ty ty0) as E;tryfalse. apply tyeqb_iff in E.
    inversion_clear H3. subst. eapply IHe1 in H2. eapply IHe2 in H0.
    econstructor;simpl in *.
    + eapply TiTyE_open with (t:=ty0 ^ ti). 
      * apply all_subtype_refl. 
      * constructor. reflexivity. simpl. destruct ti,ti0;auto; 
        simpl; autounfold;constructor; try omega. rewrite <- Z.add_max_distr_r. 
        rewrite Z.max_le_iff. left. omega.
      * assumption.
    + eapply TiTyE_open with (t:=ty0 ^ ti0).
      * apply all_subtype_refl. 
      * constructor. reflexivity. simpl. destruct ti,ti0;auto; 
        simpl; autounfold;constructor; try omega. 
        rewrite Z.max_le_iff. right. omega.
      * assumption. 
Qed.