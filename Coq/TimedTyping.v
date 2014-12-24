Require Import Typing.
Require Import ContextualCausality.
Require Import Tactics.
Require Import Utils.
Require Import Environments.

(* A type system with time-indexed types. This system subsumes both
the type system and the contextual causality system. *)

Open Scope Z.

(* Timed types *)

Inductive TiTy := TimedType (ty : Ty) (ti : Z).

Infix "^" := TimedType.

(* Selector functions to extract the time and the type of a timed
type. *)

Definition time t := match t with TimedType _ ti => ti end.
Definition type t := match t with TimedType ty _ => ty end.

(* Convenience function to add time to a timed type. *)

Definition add_time d t := match t with TimedType ty ti => TimedType ty (ti + Z.of_nat d) end.
Definition sub_time d t := match t with TimedType ty ti => TimedType ty (ti - Z.of_nat d) end.

(* A time timed time environment maps variables to timed types.  *)

Definition TiTyEnv := Env' TiTy.


(* Definition of the timed type inference rules for variables,
operators, expressions and contracts. *)

Inductive TiTyV : TiTyEnv -> TiTy -> Var -> Prop :=
| causal_V1 t t' g  : type t = type t' -> time t <= time t' -> TiTyV (t :: g) t' V1
| causal_VS g v t t' : TiTyV g t v -> TiTyV (t' :: g) t (VS v).

Definition TiTyOp (op : Op) (ts : list TiTy) (t:TiTy) : Prop
  := (all (fun t' => time t' = time t) ts) /\ TypeOp op (map type ts) (type t).

Inductive TiTyE : TiTyEnv -> TiTy -> Exp -> Prop:= 
 | causal_op t ts ts' op args : TiTyOp op ts' t -> all2 (TiTyE ts) ts' args -> TiTyE ts t (OpE op args)
 | causal_obs l t' t ts : t' <= time t -> |-O l ∶ type t ->  TiTyE ts t (Obs l t')
 | causal_var t ts v : TiTyV ts t v -> TiTyE ts t (VarE v)
 | causal_acc t t' ts e1 e2 n : type t = type t'
                                -> TiTyE (map (add_time n) ts) (add_time n t) e2
                                -> TiTyE (t' :: ts) t e1
                                -> TiTyE ts t (Acc e1 n e2)
  .



Inductive TiTyC : TiTyEnv -> Z -> Contr -> Prop :=
| causal_zero ts t : TiTyC ts t Zero
| causal_translate ts t d c : TiTyC (map (sub_time d) ts) (t - Z.of_nat d) c
                                     -> TiTyC ts t (Translate d c)
| causal_let ts t t' e c : TiTyE ts t' e -> TiTyC (t' :: ts) t c -> TiTyC ts t (Let e c)
| causal_scale ts ti e c : TiTyE ts (REAL ^ ti) e -> TiTyC ts ti c -> TiTyC ts ti (Scale e c)
| causal_both ts t c1 c2 : TiTyC ts t c1 -> TiTyC ts t c2 -> TiTyC ts t (Both c1 c2)
| causal_transfer t ts p1 p2 a : t <= 0 -> TiTyC ts t (Transfer p1 p2 a)
| causal_if ts t d e c1 c2 : TiTyE ts (BOOL ^ 0) e -> TiTyC ts t c1
                             -> TiTyC (map (sub_time d) ts) (t - Z.of_nat d) c2
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
    + apply IHe1 in H6. simpl in *. rewrite H4 in *. assumption.
    + apply IHe2 in H5. rewrite map_map in *. rewrite type_add_time in *. 
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

Lemma time_add_time d t :  time (add_time d t) = time t + Z.of_nat d.
Proof.
  destruct t. reflexivity.
Qed.
Lemma time_sub_time d t :  time (sub_time d t) = time t - Z.of_nat d.
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
    + apply IHe2 in H5. rewrite map_map in *. rewrite time_add_time in *. 
      erewrite map_ext. eassumption. intros. simpl. rewrite time_add_time. reflexivity.
    + apply IHe1 in H6. simpl in *. eassumption.
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

Lemma map_add_time n tys tis : map (add_time n) tys ^^ tis = tys ^^ (map (fun t => t + Z.of_nat n) tis).
Proof.
  generalize dependent tis. induction tys;intros. reflexivity.
  destruct tis. reflexivity.
  simpl. rewrite IHtys. reflexivity.
Qed.

Lemma map_sub_time n tys tis : map (sub_time n) tys ^^ tis = tys ^^ (map (fun t => t - Z.of_nat n) tis).
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
  - apply causal_acc with (t' := t ^ t'). reflexivity. simpl. rewrite map_add_time. eauto.
    specialize (IHTy1 ti (t' :: tis)). eauto.
Qed.

Hint Resolve type_TiTyE.

Theorem type_TiTyC tis tys ti  c : tys |-C c -> CausalC tis ti c -> TiTyC tys^^tis ti c.
Proof.
  intros Ty Ti. generalize dependent tis. generalize dependent ti. 
  induction Ty;intros;inversion Ti;subst;clear Ti;eauto.
  - specialize (IHTy ti (t' :: tis)).  eauto.
  - econstructor. rewrite map_sub_time. eauto.
  - econstructor; eauto. rewrite map_sub_time. eauto.
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

Lemma all_subtype_time ts1 ts2 : all2 subtype ts1 ts2 -> all2 Z.le (map time ts1) (map time ts2).
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



