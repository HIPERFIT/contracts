(********** Denotational Semantics **********)

Require Export Typing.
Require Export ZArith.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Tactics.

(* Observations: mapping observables to values *)

Inductive Val : Set := BVal : bool -> Val | RVal : R -> Val.

Definition ExtEnv := ObsLabel -> Z -> option Val.

Instance ext_Partial : Partial ExtEnv := {
  lep t1 t2  := forall i (o : ObsLabel) (v : Val) , t1 o i = Some v -> t2 o i = Some v
  }.

Reserved Notation "'|-V' e '∶' t" (at level 20).

Inductive TypeVal : Val -> Ty -> Prop := 
| type_bool b : |-V BVal b ∶ BOOL
| type_real b : |-V RVal b ∶ REAL
        where "'|-V' v '∶' t" := (TypeVal v t).


Reserved Notation "'|-V'' e '∶' t" (at level 20).

Inductive TypeVal' : option Val -> Ty -> Prop := 
| type_some v t : |-V v ∶ t -> |-V' Some v ∶ t
| type_none t : |-V' None ∶ t
        where "'|-V'' v '∶' t" := (TypeVal' v t).

Hint Constructors TypeVal TypeVal'.

Definition TypeExt (rho : ExtEnv) := forall z l t, |-O l ∶ t -> |-V' (rho l z)  ∶ t.


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


Lemma EsemOpE op es rho erho : 
  E'[|OpE op es|] rho erho = (mapM (fun e => E'[|e|] rho erho) es) >>= OpSem op.
Proof.
  simpl. f_equal.
  induction es.
  + reflexivity.
  + simpl. f_equal. apply IHes.
Qed.


Lemma adv_ext_step n erho : ((adv_ext (- Z.of_nat (S n)) erho) = (adv_ext (- Z.of_nat n) (adv_ext (-1) erho))).
Proof.
  rewrite adv_ext_iter. f_equal. rewrite Nat2Z.inj_succ. omega.
Qed.


(* Semantic structures for contracts. *)

(* An elemtn of type [trans] represents a set of transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of transfers is undefined (read:
 "bottom"). *)

Definition trans' := party -> party -> currency -> R.

Definition trans := option trans'.


Open Scope R.
Definition empty_trans' : trans' := fun p1 p2 c => 0.
Definition empty_trans : trans := Some empty_trans'.
Definition bot_trans : trans := None.
Definition singleton_trans' (p1 p2 : party) (c : currency) r : trans'
  := fun p1' p2' c' => if eq_str p1 p2
                       then 0
                       else if eq_str p1 p1' && eq_str p2 p2' && eq_str c c'
                            then r
                            else if eq_str p1 p2' && eq_str p2 p1' && eq_str c c'
                                 then -r
                                 else 0.
Definition singleton_trans (p1 p2 : party) (c : currency) r : trans  := Some (singleton_trans' p1 p2 c r).
Definition add_trans' : trans' -> trans' -> trans' := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c).
Definition add_trans : trans -> trans -> trans := liftM2 add_trans'.
Definition scale_trans' : R -> trans' -> trans' := fun s t p1 p2 c => (t p1 p2 c * s).
Definition scale_trans : option R -> trans -> trans := liftM2 scale_trans'.


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

Definition trace := nat -> trans.


Instance trace_Partial : Partial trace := {
  lep t1 t2  := forall i z , t1 i = Some z -> t2 i = Some z
  }.


(* The following are combinators to contruct traces. *)

Definition const_trace (t : trans) : trace := fun x => t.
Definition empty_trace : trace := const_trace empty_trans.
Definition singleton_trace (t : trans) : trace
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