Require Import Typing.
Require Export ContextualCausality.
Require Import Tactics.
Require Import Utils.
Require Import Environments.
Require Import Causality.

Import ListNotations. 


(* A type system with time-indexed types. This system subsumes both
the type system and the contextual causality system. *)

Open Scope Z.

(* Timed types *)

Inductive TiTy := TimedType (ty : Ty) (ti : TimeB).

Infix "@" := TimedType (at level 50).

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
 | causal_obs l t' t ts : Time t' <= time t -> |-O l ∶ type t ->  TiTyE ts t (Obs l t')
 | causal_var t ts v : TiTyV ts t v -> TiTyE ts t (VarE v)
 | causal_acc t ts e1 e2 n : TiTyE (map (add_time n) ts) (add_time n t) e2
                             -> TiTyE (type t @ TimeBot :: ts) t e1
                             -> TiTyE ts t (Acc e1 n e2)
  .



Inductive TiTyC : TiTyEnv -> TimeB -> Contr -> Prop :=
| causal_zero ts t : TiTyC ts t Zero
| causal_translate ts t d c : TiTyC (map (sub_time d) ts) (tsub' d t) c
                                     -> TiTyC ts t (Translate d c)
| causal_let ts t t' e c : TiTyE ts t' e -> TiTyC (t' :: ts) t c -> TiTyC ts t (Let e c)
| causal_scale ts ti ti' e c : ti' <= ti -> TiTyE ts (REAL @ ti) e -> TiTyC ts ti c -> TiTyC ts ti' (Scale e c)
| causal_both ts t c1 c2 : TiTyC ts t c1 -> TiTyC ts t c2 -> TiTyC ts t (Both c1 c2)
| causal_transfer t ts p1 p2 a : t <= Time 0 -> TiTyC ts t (Transfer p1 p2 a)
| causal_if ts t d e c1 c2 : TiTyE ts (BOOL @ Time 0) e -> TiTyC ts t c1
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
  - apply TiTyE_type in H0. simpl in H0. apply H0.
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
  - apply TiTyE_time in H0. simpl in H0. apply H0.
  - apply TiTyE_time in H. simpl in H. apply H.
  - rewrite map_map in *. erewrite map_ext. eassumption. intro. simpl.
    rewrite time_sub_time. reflexivity.
Qed.

Corollary TiTyC_causal t c : TiTyC [] t c -> causal c.
Proof.
  intros T. apply TiTyC_time in T. simpl in *. eauto using CausalC_sound.
Qed.

(* Below we show that the conjunction of well typing and contextual
causality implies timed typing. *)

Infix "@@" := (zipWith TimedType) (at level 1).

Fixpoint repeat {A} (n : nat) (x : A) : list A :=
  match n with
    | O => nil
    | S m => x :: repeat m x
  end.


Lemma map_type tys tis : length tys = length tis -> map type tys @@ tis = tys.
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis;tryfalse. simpl. f_equal. auto.
Qed.

Lemma map_time tys tis : length tys = length tis -> map time tys @@ tis = tis.
Proof.
  generalize dependent tys. induction tis;intros. destruct tys; reflexivity.
  destruct tys;tryfalse. simpl. f_equal. auto.
Qed.

Lemma map_type_time ts : (map type ts) @@ (map time ts) = ts.
Proof.
  induction ts;simpl;f_equal;try destruct a;eauto.
Qed.

Lemma map_type_repeat tys t : map type tys @@ (repeat (length tys) t) = tys.
Proof.
  induction tys. reflexivity. simpl. f_equal. auto.
Qed.

Lemma map_add_time n tys tis : map (add_time n) tys @@ tis = tys @@ (map (tadd' n) tis).
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis. reflexivity.
  simpl. rewrite IHtys. reflexivity.
Qed.

Lemma map_sub_time n tys tis : map (sub_time n) tys @@ tis = tys @@ (map (tsub' n) tis).
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis. reflexivity.
  simpl. rewrite IHtys. reflexivity.
Qed.


Lemma type_TiTyE tis tys ti ty e : tys |-E e ∶ ty -> CausalE tis ti e -> TiTyE tys@@tis (ty@ti) e.
Proof.
  intros Ty Ti. generalize dependent tis. generalize dependent ti. 
  induction Ty using TypeExp_ind';intros;inversion Ti;subst;clear Ti.
  - apply causal_op with (ts' := ts @@ (repeat (length ts) ti)). unfold TiTyOp. split. 
    clear H. clear H0. clear H1. induction ts;simpl; constructor. reflexivity. apply IHts.
    rewrite map_type_repeat. simpl. assumption.
    clear H. induction H0;simpl;constructor;inversion H1;inversion H5;subst;auto.
  - eauto.
  - econstructor. generalize dependent tis. generalize dependent ti. 
    induction H;intros;inversion H3; clear H3;subst;simpl; econstructor; eauto.
  - apply causal_acc. simpl. rewrite map_add_time. eauto.
    specialize (IHTy1 ti (TimeBot :: tis)). eauto.
Qed.

Theorem type_TiTyC tis tys ti  c : tys |-C c -> CausalC tis ti c -> TiTyC tys@@tis ti c.
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
                                       (TiTyC tys@@tis ti c <-> tys |-C c /\ CausalC tis ti c).
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

Lemma subtype_refl t : t <| t.
Proof. destruct t. auto. Qed.

Hint Immediate subtype_refl.

Lemma all_subtype_refl ts :  all2 subtype ts ts.
Proof.
  induction ts; eauto. 
Qed.


(* Special case of [TiTyE_open] where the type environment stays the same. *)
Corollary TiTyE_open' t t' ts (e : Exp) : t <| t' -> TiTyE ts t e -> TiTyE ts t' e.
Proof. eauto using TiTyE_open, all_subtype_refl. Qed.

Definition inferObs (l : ObsLabel) : Ty :=
  match l with
    | LabR _ => REAL
    | LabB _ => BOOL
  end.


Lemma inferObs_sound l : |-O l ∶ inferObs l.
Proof.
  destruct l; auto.
Qed.

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

Definition tmax (t1 t2 : TimeB) : TimeB :=
  match t1,t2 with
    | TimeBot, _ => t2
    | _, TimeBot => t1
    | Time t1', Time t2' => Time (Z.max t1' t2')
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
Definition tmaxs (ts : list TimeB) : TimeB :=fold_right tmax TimeBot ts.

Lemma tmaxs_cons x xs : tmaxs (x :: xs) = tmax x (tmaxs xs).
Proof.
  unfold tmaxs. fold ([x] ++ xs). rewrite fold_right_app. reflexivity.
Qed.

Fixpoint inferE (env : TiTyEnv) (e:Exp) : option TiTy :=
  match e with
    | OpE op args => sequence (map (inferE env) args) >>=
                              (fun args' => liftM (fun ty => ty @ tmaxs (map time args')) 
                                                  (inferOp op (map type args')))
    | VarE v => lookupEnv v env
    | Obs l i => Some (inferObs l @ Time i)
    | Acc f d z => inferE (map (add_time d) env) z >>= 
                  (fun t => inferE (type t @ TimeBot :: env) f >>= 
                  (fun t' => if tyeqb (type t) (type t') 
                             then Some (type t @ tmax (tsub' d (time t)) (time t')) 
                             else None))
  end.


(* Time intervals *)
Open Scope Z.

Definition ole (lo hi : option Z) := forall l h, lo = Some l -> hi = Some h -> l <= h.

Hint Unfold ole.

(* Time intervals are always non-empty. *)
Inductive TimeI := Time' (t : TimeB) | TimeTop.

Definition iadd d t := match t with
                         | TimeTop => TimeTop
                         | Time' t' => Time' (tadd' d t')
                       end.

Definition tileb l t := match t with
                           | TimeTop => true
                           | Time' t' => tleb l t'
                       end.

Definition ileb t1 t2 := match t1,t2 with
                         | _,TimeTop => true
                         | Time' s1, Time' s2 => tleb s1 s2
                         | _, _ => false
                       end.


Definition imin t1 t2 := if ileb t1 t2 then t1 else t2.

Open Scope time.

Fixpoint inferC (env : TiTyEnv) (c:Contr) : option TimeI :=
  match c with
    | Zero => Some TimeTop
    | Transfer p1 p2 a => Some (Time' (Time 0))
    | Translate d c' => liftM (iadd d) (inferC (map (sub_time d) env) c')
    | Scale e c' => inferE env e >>= fun ty => 
                   inferC env c' >>= fun t => if tyeqb (type ty) REAL && tileb (time ty) t
                                              then Some t
                                              else None
    | Both c1 c2 => liftM2 imin (inferC env c1) (inferC env c2)
    | Let e c' => inferE env e >>= fun t => inferC (t :: env) c'
    | If e d c1 c2 => inferE env e >>= fun t =>
                      if tyeqb (type t) BOOL && tleb (time t) (Time 0)
                      then liftM2 imin (inferC env c1) (liftM (iadd d) (inferC (map (sub_time d) env) c2))
                      else None
  end.




Lemma all_type_tle args ts env m : 
  all2 (TiTyE env) ts args
  -> tmaxs (map time ts) <= m
  -> all2 (TiTyE env) (map (fun t => type t @ m) ts) args.
Proof.
  intros T M. rewrite <- map_id. apply all2_map'. generalize dependent m. induction T;intros m M;constructor.
  - simpl. eapply TiTyE_open' with (t:=x);auto. constructor. reflexivity.
    simpl in *. rewrite tmax_lub_iff in M. tauto.
  - apply IHT. simpl in M. rewrite tmax_lub_iff in M. tauto.
Qed.

Corollary all_type_max args ts env : 
  all2 (TiTyE env) ts args
  -> all2 (TiTyE env) (map (fun t => type t @ tmaxs (map time ts)) ts) args.
Proof.
  intros. apply all_type_tle;auto.
Qed.

Theorem inferE_sound env e t :
   inferE env e = Some t -> TiTyE env t e.
Proof.
  intros I. generalize dependent env. generalize dependent t.
  induction e using Exp_ind'; intros; simpl in *;option_inv_auto.
  - assert (all2 (TiTyE env) x args) as T 
    by (clear H3; generalize dependent x; induction H; simpl in *; 
        intros; option_inv_auto; eauto using TiTyE_open').
    apply all_type_max in T. remember (map (fun t => type t @ tmaxs (map time x)) x) as x'.
    rewrite inferOp_TypeOp in *. apply causal_op with (ts':= x').
    constructor. simpl. subst. apply all_map_forall. auto. simpl.
    assert (map type x = map type x') as Tx.
    subst. induction x;simpl;f_equal. rewrite map_map. simpl. reflexivity.
    rewrite <- Tx. assumption. assumption.
  - destruct l;eauto.
  - generalize dependent t. generalize dependent env.
    induction v;constructor; destruct env; simpl in I; inversion I; auto.
    apply IHv in I. inversion I. auto.
  - destruct x; destruct x0; simpl in H3. cases (tyeqb ty ty0) as E;tryfalse. apply tyeqb_iff in E.
    inversion_clear H3. subst. eapply IHe1 in H2. eapply IHe2 in H0.
    econstructor;simpl in *;
    [eapply TiTyE_open' with (t:=ty0 @ ti)|eapply TiTyE_open' with (t:=ty0 @ ti0)]; try assumption;
    constructor; try reflexivity; simpl; destruct ti,ti0;auto; 
    simpl; autounfold;constructor; try omega. 
    + rewrite <- Z.add_max_distr_r. rewrite Z.max_le_iff. left. omega.
    + rewrite Z.max_le_iff. right. omega.
Qed.

Open Scope Z.

Inductive tile : TimeB -> TimeI -> Prop :=
| tile_top t : tile t TimeTop
| tile_time s t : tle s t -> tile s (Time' t).

Lemma tileb_tile s t : tileb s t = true <-> tile s t.
admit. Qed.

Open Scope time.
Lemma tadd_tsub_tle d x y : x <= tadd d y ->  tsub d x <= y.
Proof.
  intros T.
  destruct x, y; simpl in *;eauto;inversion T; constructor. omega. 
Qed.


Lemma tile_tsub_iadd t n x :  tile t (iadd n x) -> tile (tsub' n t) x.
Proof.
  intro L. destruct x. inversion L. subst. unfold tsub', tadd' in *.
  constructor. auto using tadd_tsub_tle. constructor.
Qed.
  
Lemma tile_imin_l t x y : tile t (imin x y) -> tile t x.
Proof.
  (* intro T. unfold imin in *. *)
  (* cases (ileb x y) as L. assumption. destruct x, y;simpl in *;eauto. *)
admit.
Qed.

Lemma tile_imin_r t x y : tile t (imin x y) -> tile t y.
Proof.
  (* intro T. unfold imin in *. *)
  (* cases (ileb x y) as L. assumption. destruct x, y;simpl in *;eauto. *)
admit.
Qed.

Lemma tile_imin_iadd s t x n : tile t (imin x (iadd n s)) -> tile (tsub' n t) s.
Proof. 
  intros T. eauto using tile_imin_r, tile_tsub_iadd.
Qed.


Theorem inferC_sound env c i : inferC env c = Some i -> forall t, tile t i -> TiTyC env t c.
Proof.
  generalize dependent env. generalize dependent i.
  induction c; intros i env I t E;simpl in *; option_inv_auto;
  try solve [eauto using inferE_sound |inversion E;auto].
  - cases (tyeqb (type x) REAL && tileb (time x) x0) as TE;tryfalse.
    rewrite Bool.andb_true_iff in TE.
    destruct TE as [TE1 TE2]. rewrite tyeqb_iff in TE1.
    rewrite tileb_tile in TE2.
    destruct x. simpl in *. subst. inversion H3. subst.
    apply inferE_sound in H0.
    cases (tleb t ti) as TL. rewrite tleb_tle in TL.
    eapply IHc in H2;try eassumption.
    econstructor;eauto.
    rewrite tleb_tgt in TL.
    eapply IHc in H2; try apply E.
    eapply causal_scale in H2. eassumption.
    apply tle_refl. apply TiTyE_open' with (t:=REAL@ti);eauto.
    constructor. reflexivity. simpl. auto using tle_tlt.
  - eapply IHc in H0;eauto using tile_tsub_iadd.
  - constructor; eauto using tile_imin_l, tile_imin_r. 
  - cases (tyeqb (type x) BOOL && tleb (time x) (Time 0)) as B;tryfalse.
    rewrite Bool.andb_true_iff in B. destruct B as [B1 B2].
    rewrite tleb_tle, tyeqb_iff in *.
    option_inv_auto.
    constructor. eapply TiTyE_open' with (t:=x);eauto using inferE_sound.
    eapply IHc1; eauto using tile_imin_l. 
    eapply IHc2; eauto using tile_imin_iadd.
Qed.

Definition has_type (c : Contr) : bool := 
  match inferC nil c with
    | Some _ => true
    | None => false
  end.

Definition select_time t := match t with
                              | TimeTop => Time 0
                              | Time' t => t
                            end.

Lemma select_time_tile t : tile (select_time t) t.
Proof.
  destruct t; simpl; constructor. apply tle_refl. 
Qed.

Corollary has_type_causal c : has_type c = true -> causal c.
Proof.
  unfold has_type. intros. cases (inferC [] c) as T;tryfalse.
  eauto using inferC_sound,select_time_tile, TiTyC_causal.
Qed.
