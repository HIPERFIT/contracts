(********** Denotational Semantics **********)

Require Export Typing.
Require Export ZArith.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Tactics.

Import ListNotations.

(* The type of values for evaluating expressions *)

Inductive Val : Set := BVal : bool -> Val | RVal : R -> Val.

(* External environments map observables to values *)

Definition ExtEnv' A := ObsLabel -> Z -> A.

Definition ExtEnv := ExtEnv' Val.



(* Move external environments into the future. *)

Definition adv_ext {A} (d : Z) (e : ExtEnv' A) : ExtEnv' A
  := fun l x => e l (d + x)%Z.

Lemma adv_ext_0 {A} (e : ExtEnv' A) : adv_ext 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_ext. reflexivity.
Qed.

Lemma adv_ext_iter {A} d d' (e : ExtEnv' A) : adv_ext d (adv_ext d' e) = adv_ext (d' + d) e.
Proof.
  apply functional_extensionality. intro. apply functional_extensionality. induction d'; intros.
  - simpl. rewrite adv_ext_0. reflexivity.
  - simpl. unfold adv_ext in *.  rewrite Z.add_assoc. reflexivity.
  - unfold adv_ext. rewrite Z.add_assoc.  reflexivity.
Qed.

Lemma adv_ext_iter' {A} d d' (e : ExtEnv' A) : adv_ext d (adv_ext d' e) = adv_ext (d + d') e.
Proof.
  apply functional_extensionality. intro. apply functional_extensionality. destruct d; intros;
  unfold adv_ext; f_equal; omega.
Qed.


Lemma adv_ext_swap {A} d d' (e : ExtEnv' A) : 
  adv_ext d (adv_ext d' e) = adv_ext d' (adv_ext d e).
Proof.
  repeat rewrite adv_ext_iter. rewrite Z.add_comm. reflexivity.
Qed.


(* Semantics of real expressions. *)

Fixpoint Acc_sem {A} (f : nat -> A -> A) (n : nat) (z : A) : A :=
  match n with
    | 0 => z
    | S n' => f n (Acc_sem f n' z)
  end.

(* Induction principle for Acc_sem *)
Lemma Acc_sem_ind A (P : A -> Prop) f n z : (forall i (x : A), P x -> P (f i x)) ->  
                                            P z -> P (Acc_sem f n z).
Proof.
  intros F Z. induction n; simpl;auto.
Qed.

(* Semantics of operations *)

Definition OpSem (op : Op) (vs : list Val) : option Val :=
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

(* (Internal) environments map variables to values. *)

Definition Env' A := list A.
Definition Env := Env' Val.


Fixpoint lookupEnv {A} (v : Var) (rho : Env' A) : option A :=
  match v, rho with
    | V1, x::_ => Some x
    | VS v, _::xs => lookupEnv v xs
    | _,_ => None
  end.

(* Semantics of expressions. *)

Reserved Notation "'E[|' e '|]'" (at level 9).

Definition Fsem {A} (f : Env -> ExtEnv -> option A) (rho : Env) (erho : ExtEnv) 
  := (fun m x => x >>= fun x' =>  f (x' :: rho) (adv_ext (Z.of_nat m) erho)).

Fixpoint Esem (e : Exp) (rho : Env) (erho : ExtEnv) : option Val :=
    match e with
      | OpE op args => sequence (map (fun e => E[|e|] rho erho) args) >>= OpSem op
      | Obs l i => Some (erho l i)
      | VarE v => lookupEnv v rho
      | Acc f l z => let erho' := adv_ext (- Z.of_nat l) erho
                     in Acc_sem (Fsem E[|f|] rho erho') l (E[|z|] rho erho')
    end
      where "'E[|' e '|]'" := (Esem e ). 


Lemma adv_ext_step {A} n (erho : ExtEnv' A) : 
  ((adv_ext (- Z.of_nat (S n)) erho) = (adv_ext (- Z.of_nat n) (adv_ext (-1) erho))).
Proof.
  rewrite adv_ext_iter. f_equal. rewrite Nat2Z.inj_succ. omega.
Qed.

Axiom Zneg_of_succ_nat : forall n, Z.neg (Pos.of_succ_nat n) = (- Z.of_nat (S n))%Z.

Lemma adv_ext_step' {A} n (erho : ExtEnv' A) : ((adv_ext (Z.neg (Pos.of_succ_nat n)) erho) = (adv_ext (- Z.of_nat n) (adv_ext (-1) erho))).
Proof.
  rewrite Zneg_of_succ_nat. apply adv_ext_step.
Qed.


(* Semantic structures for contracts. *)

(* An elemtn of type [trans] represents a set of Transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of Transfers is undefined (read:
 "bottom"). *)

Definition Trans := Party -> Party -> Asset -> R.


Open Scope R.
Definition empty_trans : Trans := fun p1 p2 c => 0.
Definition singleton_trans (p1 p2 : Party) (a : Asset) r : Trans
  := fun p1' p2' a' => if Party.eqb p1 p2
                       then 0
                       else if Party.eqb p1 p1' && Party.eqb p2 p2' && Asset.eqb a a'
                            then r
                            else if Party.eqb p1 p2' && Party.eqb p2 p1' && Asset.eqb a a'
                                 then -r
                                 else 0.
Definition add_trans : Trans -> Trans -> Trans := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c).
Definition scale_trans : R -> Trans -> Trans := fun s t p1 p2 c => (t p1 p2 c * s).


Lemma scale_empty_trans r : scale_trans r empty_trans = empty_trans.
Proof.
  unfold scale_trans, empty_trans. rewrite Rmult_0_l. reflexivity.
Qed.

Lemma scale_trans_0 t : scale_trans 0 t = empty_trans.
Proof.
  unfold scale_trans, empty_trans. do 3 (apply functional_extensionality;intro). rewrite Rmult_0_r. reflexivity.
Qed.



Lemma add_empty_trans_l t : add_trans empty_trans t = t.
Proof.
  unfold add_trans, empty_trans. do 3 (apply functional_extensionality;intro). rewrite Rplus_0_l. reflexivity.
Qed.

Lemma add_empty_trans_r t : add_trans t empty_trans = t.
Proof.
  unfold add_trans, empty_trans. do 3 (apply functional_extensionality;intro). rewrite Rplus_0_r. reflexivity.
Qed.


Hint Resolve scale_empty_trans add_empty_trans_l add_empty_trans_r.

(* Traces represent the sequence of obligations that a contract
specifies. *)

Definition Trace := nat -> Trans.



(* The following are combinators to contruct traces. *)

Definition const_trace (t : Trans) : Trace := fun x => t.
Definition empty_trace : Trace := const_trace empty_trans.
Definition singleton_trace (t : Trans) : Trace
  := fun x => match x with 
                | O => t
                | _ => empty_trans
              end.
Definition scale_trace (s : R) (t : Trace) : Trace
  := scale_trans s ∘ t.

Lemma scale_trace_0 t : scale_trace 0 t = empty_trace.
Proof.
  unfold scale_trace, empty_trace,compose. apply functional_extensionality. intros.
  simpl. apply scale_trans_0.
Qed.

Lemma scale_empty_trace r : scale_trace r empty_trace = empty_trace.
Proof.
  unfold scale_trace, empty_trace,compose. apply functional_extensionality. intros.
  simpl. apply scale_empty_trans.
Qed.


Open Scope nat.

Definition delay_trace (d : nat) (t : Trace) : Trace :=
  fun x => if leb d x
           then t (x - d)
           else empty_trans.

Definition add_trace (t1 t2 : Trace) : Trace 
  := fun x => add_trans (t1 x) (t2 x).


Lemma add_empty_trace_l t : add_trace empty_trace t = t.
Proof.
  unfold add_trace, empty_trace. apply functional_extensionality;intro. apply add_empty_trans_l.
Qed.

Lemma add_empty_trace_r t : add_trace t empty_trace = t.
Proof.
  unfold add_trace, empty_trace. apply functional_extensionality;intro. apply add_empty_trans_r.
Qed.


(* Some lemmas about [delay_trace]. *)

Lemma delay_trace_0 t : delay_trace 0 t = t.
Proof.
  apply functional_extensionality.
  unfold delay_trace. simpl. intros. f_equal. omega.
Qed.


Lemma delay_empty_trace r : delay_trace r empty_trace = empty_trace.
Proof.
  apply functional_extensionality. intros. 
  unfold delay_trace, empty_trace,const_trace. destruct (leb r x);reflexivity.
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

Fixpoint within_sem (c1 c2 : Env -> ExtEnv -> option Trace) 
         (e : Exp) (i : nat)  (vars : Env) (rc : ExtEnv) : option Trace 
  := match E[|e|] vars rc with
       | Some (BVal true) => c1 vars rc
       | Some (BVal false) => match i with
                         | O => c2 vars rc
                         | S j => liftM (delay_trace 1) (within_sem c1 c2 e j vars (adv_ext 1 rc))
                       end
       | _ => None
     end.


(* Semantics of contracts. *)

Reserved Notation "'C[|' e '|]'" (at level 9).

Definition toReal (v : Val) : option R := 
  match v with
    | RVal r => Some r
    | BVal _ => None
  end.

Fixpoint Csem (c : Contr) (vars : Env) (rho : ExtEnv) : option Trace :=
    match c with
      | Zero => Some empty_trace
      | Let e c => E[|e|] vars rho >>= fun val => C[|c|] (val :: vars) rho
      | Transfer p1 p2 c => Some (singleton_trace (singleton_trans p1 p2 c 1))
      | Scale e c' => liftM2 scale_trace (E[|e|] vars rho >>= toReal) (C[|c'|] vars rho) 
      | Translate d c' => liftM (delay_trace d) (C[|c'|]vars (adv_ext (Z.of_nat d) rho))
      | Both c1 c2 => liftM2 add_trace (C[|c1|]vars rho) (C[|c2|]vars rho)
      | If e d c1 c2 => within_sem C[|c1|] C[|c2|] e d vars rho
    end
      where "'C[|' e '|]'" := (Csem e).