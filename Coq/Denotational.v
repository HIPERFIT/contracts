Require Export Syntax.
Require Export ZArith.
Require Export Basics.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Tactics.

Infix "∘" := compose (at level 40, left associativity).

(********** Denotational Semantics **********)

(* Observations: mapping observables to values *)

Definition ExtEnv := ObsLabel -> Z -> option Val.


Reserved Notation "'|-V'' e '∶' t" (at level 20).

Inductive TypeVal' : option Val -> Ty -> Prop := 
| type_some v t : |-V v ∶ t -> |-V' Some v ∶ t
| type_none t : |-V' None ∶ t
        where "'|-V'' v '∶' t" := (TypeVal' v t).

Definition TypeExt (rho : ExtEnv) := forall z l t, |-O l ∶ t -> |-V' (rho l z)  ∶ t.

Definition eq_str (s1 s2 : string) : bool :=
  match string_dec s1 s2 with
      | left  _ => true
      | right _ => false
  end.

Lemma eq_str_iff s1 s2 : eq_str s1 s2 = true <-> s1 = s2.
Proof.
  split.
  + unfold eq_str. destruct (string_dec s1 s2). auto. intro H. inversion H.
  + intro H. rewrite H. unfold eq_str. destruct (string_dec s2 s2). reflexivity. 
    tryfalse.
Qed.
  

Class Partial t := {
  lep : t -> t -> Prop
                  }. 

Infix "⊆" := lep (at level 40).

Instance none_Partial A : Partial (option A) := {
  lep t1 t2  := forall z , t1 = Some z -> t2 = Some z
  }.



Instance ext_Partial : Partial ExtEnv := {
  lep t1 t2  := forall i (o : ObsLabel) (v : Val) , t1 o i = Some v -> t2 o i = Some v
  }.



(* Move observations into the future. *)

Definition adv_ext (d : Z) (e : ExtEnv) : ExtEnv
  := fun l x => e l (d + x)%Z.

Lemma adv_ext_0 (e : ExtEnv) : adv_ext 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_ext. reflexivity.
Qed.

Lemma adv_ext_iter d d' (e : ExtEnv) : adv_ext d (adv_ext d' e) = adv_ext (d' + d) e.
Proof.
  apply functional_extensionality. intro. apply functional_extensionality. induction d'; intros.
  - simpl. rewrite adv_ext_0. reflexivity.
  - simpl. unfold adv_ext in *.  rewrite Z.add_assoc. reflexivity.
  - unfold adv_ext. rewrite Z.add_assoc.  reflexivity.
Qed.


Lemma adv_ext_swap d d' (e : ExtEnv) : 
  adv_ext d (adv_ext d' e) = adv_ext d' (adv_ext d e).
Proof.
  repeat rewrite adv_ext_iter. rewrite Z.add_comm. reflexivity.
Qed.


Lemma adv_ext_type e d : TypeExt e -> TypeExt (adv_ext d e).
Proof.
  unfold TypeExt, adv_ext. intros. auto.
Qed.

Hint Resolve adv_ext_type.

(* Semantics of (real) binary operations. *)

Definition Rleb (x y : R) : bool :=
  match Rle_dec x y with
    | left _ => true
    | right _ => false
  end.

Definition Rltb (s1 s2 : R) : bool :=
  match Rlt_dec s1 s2 with
      | left  _ => true
      | right _ => false
  end.

Open Scope bool.
Definition Reqb (x y : R) : bool := Rleb x y && Rleb y x.

(* Lifts binary functions into [option] types. *)


Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
    | None => None
    | Some x' => f x'
  end.

Definition pure {A} : A -> option A := fun x => Some x.

Infix ">>=" := bind (at level 55, left associativity).

Definition liftM {A B} (f : A -> B) (x : option A) : option B :=
 x >>= (pure ∘ f).

Definition liftM2 {A B C} (f : A -> B -> C) (x : option A) (y : option B) : option C :=
 x >>= (fun x' => y >>= pure ∘ f x').

Fixpoint mapM {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
    | nil => Some nil
    | x :: xs => liftM2 (fun x' xs' => x' :: xs') (f x) (mapM f xs)
  end.


Lemma liftM2_none {A B C :Type} (f:A->B->C) o : liftM2 f o None = None.
Proof.
  destruct o; reflexivity.
Qed.

(* Semantics of real expressions. *)

Fixpoint Acc_sem {A} (f : nat -> A -> A) (n : nat) (z : A) : A :=
  match n with
    | 0 => z
    | S n' => f n (Acc_sem f n' z)
  end.

Reserved Notation "'E'[|' e '|]'" (at level 9).

Import ListNotations.

Fixpoint OpSem (op : Op) (vs : list Val) : option Val :=
  match op with
    | Add => match vs with ([RVal x; RVal y ]) => Some (RVal (x + y)) | _ => None end
    | Sub => match vs with ([RVal x; RVal y ]) => Some (RVal (x - y)) | _ => None end
    | Mult => match vs with ([RVal x; RVal y ]) => Some (RVal (x * y)) | _ => None end
    | Div => match vs with ([RVal x; RVal y ]) => Some (RVal (x / y)) | _ => None end
    | And => match vs with ([BVal x; BVal y ]) => Some (BVal (x && y)) | _ => None end
    | Or => match vs with ([BVal x; BVal y ]) => Some (BVal (x || y)) | _ => None end
    | Less => match vs with ([RVal x; RVal y ]) => Some (BVal (Rltb x y)) | _ => None end
    | Leq => match vs with ([RVal x; RVal y ]) => Some (BVal (Rleb x y)) | _ => None end
    | Equal => match vs with ([RVal x; RVal y ]) => Some (BVal (Reqb x y)) | _ => None end
    | BLit b => match vs with ([]) => Some (BVal b) | _ => None end
    | RLit r => match vs with ([]) => Some (RVal r) | _ => None end
    | Cond => match vs with
                | ([BVal b; RVal x; RVal y ]) => Some (RVal (if b then x else y))
                | ([BVal b; BVal x; BVal y ]) => Some (BVal (if b then x else y))
                | _ => None end
    | Neg => match vs with ([RVal x]) => Some (RVal (0 - x) %R) | _ => None end
    | Not => match vs with ([BVal x]) => Some (BVal (negb x)) | _ => None end
  end.


Definition Env := list (option Val).

Instance Env_Partial : Partial Env := {
  lep t1 t2  := forall_zip lep t1 t2
  }.


Fixpoint lookupEnv (v : Var) (rho : Env) : option Val :=
  match v, rho with
    | V1, x::_ => x
    | VS v, _::xs => lookupEnv v xs
    | _,_ => None
  end.

Fixpoint Esem' (e : Exp) (rho : Env) (erho : ExtEnv) : option Val :=
    match e with
      | OpE op args => (* (mapM (fun e => E'[|e|] rho erho) args) >>= OpSem op *)
        let fix run l :=  
            match l with
              | nil => Some nil
              | x :: xs => liftM2 (@cons _) (E'[| x |] rho erho) (run xs)
            end
        in run args >>= OpSem op
      | Obs l i => erho l i
      | VarE v => lookupEnv v rho
      | Acc f l z => let erho' := adv_ext (- Z.of_nat l) erho
                     in Acc_sem (fun m x => E'[| f |] (x :: rho) 
                                              (adv_ext (Z.of_nat m) erho')) l (E'[|z|] rho erho')
    end
      where "'E'[|' e '|]'" := (Esem' e ). 


Notation "'E[|' e '|]' r" := (E'[|e|] nil r) (at level 9).

Hint Constructors TypeVal'.


Definition TypeEnv (g : TyEnv) (rho : Env) : Prop := forall_zip TypeVal' rho g.

Definition TypeArgs (ts : list Ty) (args : list Val) : Prop := forall_zip TypeVal args ts.


Lemma OpSem_typed' {A} op ts t (args : list A) (f : A -> option Val) :
|-Op op ∶ ts => t -> forall_zip (fun x t => |-V' (f x) ∶ t) args ts -> |-V' (mapM f args >>= OpSem op) ∶ t.
Proof.
  intros O T. induction O; 
  repeat (idtac; match goal with
      | [H : forall_zip _ _ _ |- _] => inversion H; clear H
      | [ |- context [match ?x with 
                      | _ => _ 
                    end]] => is_var x; destruct x
      | [ |- context [match ?x ?y with 
                      | _ => _ 
                    end]] => is_var x; is_var y; destruct (x y)
       
  end; subst; simpl; unfold liftM2, bind, pure,compose; auto).
Qed.

Lemma OpSem_typed_total {A} op ts t (args : list A) (f : A -> option Val) :
|-Op op ∶ ts => t -> forall_zip (fun x t => |-V' (f x) ∶ t /\ exists v, f x = Some v) args ts -> 
                     exists v, (mapM f args >>= OpSem op) = Some v.
Proof.
  intros O T. induction O;
  repeat (match goal with
      | [ H : _ /\ _ |- _ ] => 
        let H1 := fresh in let H2 := fresh in let H3 := fresh in
        let H4 := fresh in let H5 := fresh in let H6 := fresh in
        let H7 := fresh in
        destruct H as [H1 H2]; destruct H2 as [H3 H4]; rewrite H4 in *
      ; inversion H1 as [ H5 H6 H7| H5 ]; inversion H7
      | [H : forall_zip _ _ _ |- _] => inversion H; clear H
  end; subst; simpl; unfold liftM2, bind); eexists; auto.
Qed.

Lemma EsemOpE op es rho erho : 
  E'[|OpE op es|] rho erho = (mapM (fun e => E'[|e|] rho erho) es) >>= OpSem op.
Proof.
  simpl. f_equal.
  induction es.
  + reflexivity.
  + simpl. f_equal. apply IHes.
Qed.


Lemma lookupEnv_typed g rho v t : TypeEnv g rho -> g |-X v ∶ t -> |-V' (lookupEnv v rho) ∶ t.
Proof.
  intros E V. generalize dependent rho. dependent induction V; intros.
  + simpl. inversion E. auto.
  + simpl. inversion E. apply IHV. auto.
Qed.

Lemma adv_ext_step n erho : ((adv_ext (- Z.of_nat (S n)) erho) = (adv_ext (- Z.of_nat n) (adv_ext (-1) erho))).
Proof.
  rewrite adv_ext_iter. f_equal. rewrite Nat2Z.inj_succ. omega.
Qed.

Theorem Esem_typed' g e t (rho : Env) (erho : ExtEnv) : 
  g |-E e ∶ t -> TypeEnv g rho -> TypeExt erho -> |-V' E'[|e|] rho erho ∶ t.
Proof.
  intros E R V'. generalize dependent rho. generalize dependent erho.
  dependent induction E using TypeExp_ind'; intros.
  + rewrite EsemOpE. eapply OpSem_typed'. apply H. 
    do 4 (eapply forall_zip_apply_dep in H1;eauto).  
  + apply V'. auto.
  + simpl. eapply lookupEnv_typed; eauto.
  + simpl. generalize dependent erho. induction n; intros.
    - simpl. auto.
    - apply IHE1. auto. constructor. 
      rewrite adv_ext_step. apply IHn. auto. auto.
Qed.

Corollary Esem_typed e t (erho : ExtEnv) : 
  nil |-E e ∶ t -> TypeExt erho -> |-V' E[|e|] erho ∶ t.
Proof.
  intros. eapply Esem_typed'; eauto. constructor.
Qed.

Definition total_ext (erho : ExtEnv) : Prop := forall l i, exists v, erho l i = Some v.

Lemma total_ext_adv d e : total_ext e -> total_ext (adv_ext d e).
Proof.
  unfold total_ext. intros. apply H.
Qed.

Hint Resolve total_ext_adv.

Definition total_env (rho : Env) : Prop := forall_list (fun x => exists v , x = Some v) rho.


Theorem Esem_typed_total' g e t (rho : Env) (erho : ExtEnv) : 
  total_env rho -> total_ext erho -> 
  g |-E e ∶ t -> TypeEnv g rho -> TypeExt erho -> exists v, E'[|e|] rho erho = Some v.
Proof.
  intros T' T E R V'. generalize dependent rho. generalize dependent erho.
  dependent induction E using TypeExp_ind'; intros.
  + rewrite EsemOpE in *. eapply OpSem_typed_total. apply H. 
    apply forall_zip_and. eapply forall_zip_impl in H0; auto.
    apply H0. intros. eapply Esem_typed'; eauto. 
    do 6 (eapply forall_zip_apply_dep in H1;eauto). 
  + apply T.
  + simpl. generalize dependent rho. 
    generalize dependent g. induction v; intros.
    - inversion H. subst. inversion R. subst. simpl.
      inversion T'. subst. auto.
    - simpl. inversion H. subst. inversion R. subst. eapply IHv. 
      apply H2. inversion T'. subst. auto. auto.
  + apply proj1 with (B:= |-V' E'[|Acc e1 n e2|] rho erho ∶ t).
    simpl. generalize dependent erho. induction n; intros.
    - simpl. split. apply IHE2; auto. eapply Esem_typed'; eauto.
    - rewrite adv_ext_step. split. apply IHE1; auto. constructor;auto. apply IHn; auto.
      constructor. eapply proj2. apply IHn; auto.
      auto. eapply Esem_typed'; eauto.
      constructor. eapply proj2. apply IHn; eauto. auto.
Qed.

Corollary Esem_typed_total e t (erho : ExtEnv) : 
  total_ext erho -> nil |-E e ∶ t -> TypeExt erho -> exists v, E[|e|] erho = Some v /\ |-V v ∶ t.
Proof.
  intros. pose H0 as H'. eapply Esem_typed_total' in H'; eauto. destruct H'.
  eexists. split; eauto. eapply Esem_typed in H0; eauto. rewrite H2 in *. inversion H0. 
  auto. constructor. constructor.
Qed.

(* Semantic structures for contracts. *)

(* An elemtn of type [transfers] represents a set of transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of transfers is undefined (read:
 "bottom"). *)

Definition trans := party -> party -> currency -> R.

Definition transfers := option trans.


Open Scope R.
Definition empty_trans' : trans := fun p1 p2 c => 0.
Definition empty_trans : transfers := Some empty_trans'.
Definition bot_trans : transfers := None.
Definition singleton_trans' (p1 p2 : party) (c : currency) r : trans
  := fun p1' p2' c' => if eq_str p1 p2
                       then 0
                       else if eq_str p1 p1' && eq_str p2 p2' && eq_str c c'
                            then r
                            else if eq_str p1 p2' && eq_str p2 p1' && eq_str c c'
                                 then -r
                                 else 0.
Definition singleton_trans (p1 p2 : party) (c : currency) r : transfers  := Some (singleton_trans' p1 p2 c r).
Definition add_trans' : trans -> trans -> trans := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c).
Definition add_trans : transfers -> transfers -> transfers := liftM2 add_trans'.
Definition scale_trans' : R -> trans -> trans := fun s t p1 p2 c => (t p1 p2 c * s).
Definition scale_trans : option R -> transfers -> transfers := liftM2 scale_trans'.


Lemma scale_empty_trans' r : scale_trans' r empty_trans' = empty_trans'.
Proof.
  unfold scale_trans', empty_trans'. rewrite Rmult_0_l. reflexivity.
Qed.

Lemma scale_empty_trans r : scale_trans (Some r) empty_trans = empty_trans.
Proof.
  simpl. unfold pure, compose. rewrite scale_empty_trans'. reflexivity.
Qed.

Lemma add_empty_trans' : add_trans' empty_trans' empty_trans' = empty_trans'.
Proof.
  unfold add_trans', empty_trans'. rewrite Rplus_0_l. reflexivity.
Qed.

Lemma add_empty_trans : add_trans empty_trans empty_trans = empty_trans.
Proof.
  simpl. unfold pure, compose. rewrite add_empty_trans'. reflexivity.
Qed.

Hint Resolve scale_empty_trans' scale_empty_trans add_empty_trans' add_empty_trans.

(* Traces represent the sequence of obligations that a contract
specifies. *)

Definition trace := nat -> transfers.


Instance trace_Partial : Partial trace := {
  lep t1 t2  := forall i z , t1 i = Some z -> t2 i = Some z
  }.


(* The following are combinators to contruct traces. *)

Definition const_trace (t : transfers) : trace := fun x => t.
Definition empty_trace : trace := const_trace empty_trans.
Definition singleton_trace (t : transfers) : trace
  := fun x => match x with 
                | O => t
                | _ => empty_trans
              end.
Definition scale_trace (s : option R) (t : trace) : trace
  := scale_trans s ∘ t.

Open Scope nat.

Definition delay_trace (d : nat) (t : trace) : trace :=
  fun x => if leb d x
           then t (x - d)
           else empty_trans.

Definition add_trace (t1 t2 : trace) : trace 
  := fun x => add_trans (t1 x) (t2 x).

(* Some lemmas about [delay_trace]. *)

Lemma delay_trace_0 t : delay_trace 0 t = t.
Proof.
  apply functional_extensionality.
  unfold delay_trace. simpl. intros. f_equal. omega.
Qed.

Lemma delay_trace_iter d d' t : delay_trace d (delay_trace d' t) = delay_trace (d' + d) t.
Proof.
  apply functional_extensionality. induction d'; intros.
  simpl. rewrite delay_trace_0. reflexivity.
  simpl. unfold delay_trace in *. 
  remember (leb d x) as L. destruct L;
  remember (leb (S d') (x - d)) as L1; destruct L1;
  remember (leb (S (d' + d)) x) as L2; destruct L2;
  symmetry in HeqL; symmetry in HeqL1;  symmetry in HeqL2;
 
  try apply leb_complete in HeqL; try apply leb_complete in HeqL1;
  try apply leb_complete in HeqL2;
  try apply leb_complete_conv in HeqL; try apply leb_complete_conv in HeqL1;
  try apply leb_complete_conv in HeqL2; f_equal; try omega; try reflexivity.
Qed.


Lemma delay_trace_swap d d' e : 
  delay_trace d (delay_trace d' e) = delay_trace d' (delay_trace d e).
Proof.
  repeat rewrite delay_trace_iter. rewrite plus_comm. reflexivity.
Qed.

(* The following function is needed to define the semantics of [IfWithin]. *)

Fixpoint within_sem (c1 c2 : ExtEnv -> trace) 
         (e : Exp) (rc : ExtEnv) (i : nat) : trace 
  := match E[|e|]rc with
       | Some (BVal true) => c1 rc
       | Some (BVal false) => match i with
                         | O => c2 rc
                         | S j => delay_trace 1 (within_sem c1 c2 e (adv_ext 1 rc) j)
                       end
       | _ => const_trace bot_trans
     end.


(* Semantics of contracts. *)

Reserved Notation "'C[|' e '|]'" (at level 9).

Definition toReal (v : Val) : option R := 
  match v with
    | RVal r => Some r
    | BVal _ => None
  end.

Fixpoint Csem (c : Contr) : ExtEnv -> trace :=
  fun rho => 
    match c with
      | Zero => empty_trace
      | Transfer p1 p2 c => singleton_trace (singleton_trans p1 p2 c  1)
      | Scale e c' => scale_trace (E[|e|]rho >>= toReal) (C[|c'|]rho) 
      | Translate d c' => (delay_trace d) (C[|c'|](adv_ext (Z.of_nat d) rho))
      | Both c1 c2 => add_trace (C[|c1|]rho) (C[|c2|]rho)
      | If e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).

Definition total_trace (t : trace) := forall i, exists v, t i = Some v.

Hint Unfold empty_trace empty_trans const_trace empty_trans 
     total_trace singleton_trace singleton_trans scale_trace scale_trans.

Theorem Csem_typed_total c (erho : ExtEnv) : 
  total_ext erho -> |-C c -> TypeExt erho -> total_trace (C[|c|] erho).
Proof.
  intros T C R. generalize dependent erho. unfold total_trace. induction C.
  + simpl. repeat autounfold. eauto.
  + simpl. repeat autounfold. intros. destruct i; eauto.
  + simpl. repeat autounfold. intros. unfold liftM2, bind.
    destruct (IHC erho T R i). 
    eapply Esem_typed_total in H; eauto. decompose [and ex] H.
    rewrite H2. inversion H3. simpl. rewrite  H0.
    unfold pure, compose. eauto.
  + intros. simpl. unfold delay_trace. destruct (leb d i).
    simpl. apply IHC; auto. autounfold; eauto.
  + intros. simpl. unfold add_trace, add_trans, liftM2, bind. 
    destruct (IHC1 erho T R i). rewrite H.
    destruct (IHC2 erho T R i). rewrite H0.
    unfold pure, compose. eauto.
  + simpl. induction d; intros.
    - simpl. eapply  Esem_typed_total in H; eauto. decompose [and ex] H.
      rewrite H1. inversion H2. destruct b; auto.
    - simpl. eapply  Esem_typed_total in H; eauto. decompose [and ex] H.
      rewrite H1. inversion H2. destruct b; auto. 
      unfold delay_trace. destruct (leb 1 i). apply IHd; eauto. autounfold. eauto.
Qed.