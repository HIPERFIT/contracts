Require Export Syntax.
Require Export ZArith.
Require Export Basics.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Tactics.

Infix "∘" := compose (at level 40, left associativity).

(********** Denotational Semantics **********)

(* Observations: mapping observables to values *)

Definition ext := Z -> forall (A : Ty), ObsLabel A -> option [|A|].

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


Instance option_Partial (f : Ty -> Type) t : Partial ((option ∘ f) t) := {
  lep t1 t2  := forall z , t1 = Some z -> t2 = Some z
  }.

Lemma lep_some A (o : option A) x : Some x ⊆ o -> Some x = o.
Proof.
  simpl. intros. symmetry. auto.
Qed. 

Inductive EnvLe {f : Ty -> Type} : forall {V}, Env (option ∘ f) V -> Env (option ∘ f) V -> Prop :=
| EnvLeNil : EnvLe (EnvNil _) (EnvNil _)
| EnvLeExtend i V (e1 e2 : Env (option ∘ f) V) (x1 x2 : option (f i)) : 
    x1 ⊆ x2 -> EnvLe e1 e2 (V:=V) -> EnvLe (EnvCons x1 e1) (EnvCons x2 e2).

Hint Constructors EnvLe.

Instance env_Partial (f : Ty -> Type) V : Partial (Env (option ∘ f) V) := {
  lep := EnvLe
  }.

Lemma EnvLeEmpty' (f : Ty -> Type) : EnvNil (option ∘ f) ⊆ EnvNil (option ∘ f).
constructor. Qed.

Lemma EnvLeExtend' (f: Ty -> Type) V (e1 e2 : Env (option ∘ f) V) i (x1 x2 : option (f i)) :
  x1 ⊆ x2 -> e1 ⊆ e2 -> EnvCons x1 e1 ⊆ EnvCons x2 e2.
constructor; assumption. Qed.

Lemma EnvLe_lookup {t} {V : list Ty} {f : Ty -> Type} (e1 e2 : Env (option ∘ f) V) (v : Var V t) : 
  e1 ⊆ e2 -> lookupEnv v e1 ⊆ lookupEnv v e2.
Proof.
  intros L. induction L. simpl. auto. dependent destruction v. apply H. apply IHL. 
Qed.

Hint Resolve EnvLe_lookup EnvLeEmpty' EnvLeExtend'.

Instance ext_Partial : Partial ext := {
  lep t1 t2  := forall i t (o : ObsLabel t) (z : [|t|]) , t1 i t o = Some z -> t2 i t o = Some z
  }.

(* Move observations into the future. *)

Definition adv_ext (d : Z) (e : ext) : ext
  := fun x => e (d + x)%Z.

Lemma adv_ext_0 (e : ext) : adv_ext 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_ext. reflexivity.
Qed.

Lemma adv_ext_iter d d' (e : ext) : adv_ext d (adv_ext d' e) = adv_ext (d' + d) e.
Proof.
  apply functional_extensionality. induction d'; intros.
  - simpl. rewrite adv_ext_0. reflexivity.
  - simpl. unfold adv_ext in *.  rewrite Z.add_assoc. reflexivity.
  - unfold adv_ext. rewrite Z.add_assoc.  reflexivity.
Qed.


Lemma adv_ext_swap d d' (e : ext) : 
  adv_ext d (adv_ext d' e) = adv_ext d' (adv_ext d e).
Proof.
  repeat rewrite adv_ext_iter. rewrite Z.add_comm. reflexivity.
Qed.


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

Definition option_map2 {A B C :Type} (f:A->B->C) o1 o2 :=
  match o1,o2 with
    | Some a, Some b => Some (f a b)
    | _,_ => None
  end.

Lemma option_map2_none {A B C :Type} (f:A->B->C) o : option_map2 f o None = None.
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



Definition BinOpSem {s t} (op : BinOp s t) : TySem s -> TySem s -> TySem t :=
  match op in BinOp s t return TySem s -> TySem s -> TySem t with
    | Add => Rplus
    | Sub => Rminus
    | Mult => Rmult
    | And => andb
    | Or => orb
    | Less => Rltb
    | Equal => Rleb
  end.

Definition UnOpSem {s t} (op : UnOp s t) : TySem s -> TySem t :=
  match op in UnOp s t return TySem s -> TySem t with
    | Not => negb
    | Neg => fun x => (0 - x) %R
  end.

Fixpoint Esem' {t l} (e : exp' l t) : Env (option ∘ TySem) l -> ext -> option [|t|] :=
    match e with
      | Lit r => fun vars rho => Some r
      | BinOpE _ op e1 e2 => fun vars rho =>  option_map2 (BinOpSem op) (E'[|e1|] vars rho) (E'[|e2|] vars rho)
      | UnOpE _ op e => fun vars rho => option_map (UnOpSem op) (E'[|e|] vars rho)
      | IfE b e1 e2 => fun vars rho => match E'[|b|] vars rho with
                                             | Some true => E'[|e1|] vars rho
                                             | Some false => E'[|e2|] vars rho
                                             | None => None
                                           end
      | Obs obs t => fun vars rho => rho t _ obs
      | VarE v => fun vars rho => lookupEnv v vars
      | Acc f l z => fun vars rho => 
                          let rho' := adv_ext (- Z.of_nat l) rho
                          in Acc_sem (fun m x => E'[| f |] (EnvCons x vars) 
                                            (adv_ext (Z.of_nat m) rho')) l (E'[|z|] vars rho')
    end
      where "'E'[|' e '|]'" := (Esem' e ). 

Definition empty_env := (EnvNil (option ∘ TySem)).

Notation "'E[|' e '|]' r" := (E'[|e|] empty_env r) (at level 9).



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
Definition add_trans : transfers -> transfers -> transfers := option_map2 add_trans'.
Definition scale_trans' : R -> trans -> trans := fun s t p1 p2 c => (t p1 p2 c * s).
Definition scale_trans : option R -> transfers -> transfers := option_map2 scale_trans'.


Lemma scale_empty_trans' r : scale_trans' r empty_trans' = empty_trans'.
Proof.
  unfold scale_trans', empty_trans'. rewrite Rmult_0_l. reflexivity.
Qed.

Lemma scale_empty_trans r : scale_trans (Some r) empty_trans = empty_trans.
Proof.
  simpl. rewrite scale_empty_trans'. reflexivity.
Qed.

Lemma add_empty_trans' : add_trans' empty_trans' empty_trans' = empty_trans'.
Proof.
  unfold add_trans', empty_trans'. rewrite Rplus_0_l. reflexivity.
Qed.

Lemma add_empty_trans : add_trans empty_trans empty_trans = empty_trans.
Proof.
  simpl. rewrite add_empty_trans'. reflexivity.
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

Fixpoint within_sem (c1 c2 : ext -> trace) 
         (e : exp BTy) (rc : ext) (i : nat) : trace 
  := match E[|e|]rc with
       | Some true => c1 rc
       | Some false => match i with
                         | O => c2 rc
                         | S j => delay_trace 1 (within_sem c1 c2 e (adv_ext 1 rc) j)
                       end
       | None => const_trace bot_trans
     end.


(* Semantics of contracts. *)

Reserved Notation "'C[|' e '|]'" (at level 9).

Fixpoint Csem (c : contract) : ext -> trace :=
  fun rho => 
    match c with
      | Zero => empty_trace
      | TransfOne p1 p2 c => singleton_trace (singleton_trans p1 p2 c  1)
      | Scale e c' => scale_trace E[|e|]rho (C[|c'|]rho) 
      | Transl d c' => (delay_trace d) (C[|c'|](adv_ext (Z.of_nat d) rho))
      | Both c1 c2 => add_trace (C[|c1|]rho) (C[|c2|]rho)
      | IfWithin e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).
