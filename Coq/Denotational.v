Require Export Syntax.
Require Export ZArith.
Require Export Basics.
Require Import FunctionalExtensionality.

Infix "∘" := compose (at level 40, left associativity).

(********** Denotational Semantics **********)

(* Observations: mapping observables to values *)

Definition inp (A : Set) := Z -> observable -> option A.
Definition obs := inp Z.

Definition choices := inp bool.


Class Partial t := {
  lep : t -> t -> Prop
                  }. 

Infix "⊆" := lep (at level 40).

Instance none_Partial A : Partial (option A) := {
  lep t1 t2  := forall z , t1 = Some z -> t2 = Some z
  }.

Lemma lep_some A (o : option A) x : Some x ⊆ o -> Some x = o.
Proof.
  simpl. intros. symmetry. auto.
Qed. 

Inductive EnvLe {A} : forall {V}, Env (option A) V -> Env (option A) V -> Prop :=
| EnvLeEmpty V (f : V -> option A) : EnvLe (Empty f) (Empty f)
| EnvLeExtend V (e1 e2 : Env (option A) V) x1 x2 : x1 ⊆ x2 -> EnvLe e1 e2 -> EnvLe (Extend x1 e1) (Extend x2 e2)
.

Hint Constructors EnvLe.

Instance env_Partial A V : Partial (Env (option A) V) := {
  lep := EnvLe
  }.

Lemma EnvLeEmpty' A V (f : V -> option A) : Empty f ⊆ Empty f.
constructor. Qed.

Lemma EnvLeExtend' A V (e1 e2 : Env (option A) V) x1 x2 : 
  x1 ⊆ x2 -> e1 ⊆ e2 -> Extend x1 e1 ⊆ Extend x2 e2.
constructor; assumption. Qed.

Lemma EnvLe_lookup {V A} (e1 e2 : Env (option A) V) (v : V) : e1 ⊆ e2 -> lookupEnv e1 v ⊆ lookupEnv e2 v.
Proof. 
  intros L. induction L. simpl. auto. destruct v. simpl. intros. apply IHL. auto.
  simpl. intros. destruct u. auto.
Qed.

Hint Resolve EnvLe_lookup EnvLeEmpty' EnvLeExtend'.

Instance single_Partial A B : Partial (A -> option B) := {
  lep t1 t2  := forall i z , t1 i = Some z -> t2 i = Some z
  }.


Instance double_Partial A B C : Partial (A -> B -> option C) := {
  lep t1 t2  := forall i j z , t1 i j = Some z -> t2 i j = Some z
  }.

Instance nested_Partial T1 T2 (p1:Partial T1) (p2 : Partial T2) : Partial (T1 * T2) := {
  lep t1 t2  := lep (fst t1) (fst t2) /\ lep (snd t1) (snd t2)
  }.


(* Move observations into the future. *)

Definition adv_inp {A} (d : Z) (e : inp A) : inp A
  := fun x => e (d + x)%Z.

Lemma adv_inp_0 A (e : inp A) : adv_inp 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_inp. reflexivity.
Qed.

Lemma adv_inp_iter {A} d d' (e : inp A) : adv_inp d (adv_inp d' e) = adv_inp (d' + d) e.
Proof.
  apply functional_extensionality. induction d'; intros.
  - simpl. rewrite adv_inp_0. reflexivity.
  - simpl. unfold adv_inp in *.  rewrite Z.add_assoc. reflexivity.
  - unfold adv_inp. rewrite Z.add_assoc.  reflexivity.
Qed.


Lemma adv_inp_swap {A} d d' (e : inp A) : 
  adv_inp d (adv_inp d' e) = adv_inp d' (adv_inp d e).
Proof.
  repeat rewrite adv_inp_iter. rewrite Z.add_comm. reflexivity.
Qed.


(* External environment *)

Definition ext := (obs * choices)%type.

Definition adv_ext (d : Z) (rho : ext) : ext :=
  let (obs, ch) := rho in (adv_inp d obs, adv_inp d ch).
                                             

Lemma adv_ext_0 e : adv_ext 0 e = e.
Proof.
  unfold adv_ext. destruct e. repeat rewrite adv_inp_0. reflexivity.
Qed.

Lemma adv_ext_iter d d' e : adv_ext d (adv_ext d' e) = adv_ext (d' + d) e.
Proof.
  unfold adv_ext. destruct e. repeat rewrite adv_inp_iter. reflexivity.  
Qed.


Lemma adv_ext_swap d d' e : 
  adv_ext d (adv_ext d' e) = adv_ext d' (adv_ext d e).
Proof.
    unfold adv_ext. destruct e. f_equal; apply adv_inp_swap. 
Qed.


(* Semantics of (real) binary operations. *)

Definition RBinOp (op : BinOp) : Z -> Z -> Z :=
  match op with
    | Add => Zplus
    | Subt => Zminus
    | Mult => Zmult
    | Min => fun x y => if Z.leb x y then x else y
    | Max => fun x y => if Z.leb x y then y else x
  end.

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

Fixpoint RAcc_sem {A} (f : nat -> A -> A) (n : nat) (z : A) : A :=
  match n with
    | 0 => z
    | S n' => f n (RAcc_sem f n' z)
  end.

Reserved Notation "'R'[|' e '|]'" (at level 9).

Fixpoint Rsem' {A} (e : rexp' A) : Env (option Z) A -> obs -> option Z :=
    match e with
      | RLit _ r => fun vars rho => Some r
      | RBin _ op e1 e2 => fun vars rho =>  option_map2 (RBinOp op) (R'[|e1|] vars rho) (R'[|e2|] vars rho)
      | RNeg _ e => fun vars rho => option_map (Zminus 0) (R'[|e|] vars rho)
      | Obs _ obs t => fun vars rho => rho t obs
      | RVar _ v => fun vars rho => lookupEnv vars v 
      | RAcc _ f l z => fun vars rho => 
                          let rho' := adv_inp (- Z.of_nat l) rho
                          in RAcc_sem (fun m x => R'[| f |] (Extend x vars) 
                                            (adv_inp (Z.of_nat m) rho')) l (R'[|z|] vars rho')
    end
      where "'R'[|' e '|]'" := (Rsem' e ). 


Notation "'R[|' e '|]' r" := (R'[|e|] (Empty (zero _)) r) (at level 9).

(* Semantics of binary Boolean operations. *)

Definition BBinOp (op : BoolOp) : bool -> bool -> bool :=
  match op with
    | And => andb
    | Or => orb
  end.

(* Semantics of binary comparison operators. *)

Definition RCompare (cmp : Cmp) : Z -> Z -> bool :=
  match cmp with
    | EQ => Z.eqb
    | LTE => Z.leb
    | LT => fun x y => negb (Z.leb y x)
  end.

(* Semantics of Boolean expressions *)

Reserved Notation "'B[|' e '|]' rc " (at level 9).

Fixpoint Bsem (e : bexp) : ext -> option bool :=
  fun rho => 
    match e with
      | BLit r => Some r
      | BChoice choice z => snd rho z choice
      | BOp op e1 e2 => option_map2 (BBinOp op) B[|e1|]rho B[|e2|]rho
      | BNot e => option_map negb B[|e|]rho
      | RCmp cmp e1 e2 => option_map2 (RCompare cmp) R[|e1|](fst rho) R[|e2|](fst rho)
    end
      where "'B[|' e '|]' rho" := (Bsem e rho). 

(* Semantic structures for contracts. *)

(* An elemtn of type [transfers] represents a set of transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of transfers is undefined (read:
 "bottom"). *)

Definition trans := party -> party -> currency -> Z.

Definition transfers := option trans.


Definition empty_trans' : trans := fun p1 p2 c => 0%Z.
Definition empty_trans : transfers := Some empty_trans'.
Definition bot_trans : transfers := None.
Definition singleton_trans' p1 p2 c r : trans 
  := fun p1' p2' c' => if andb (eq_str p1 p1') (andb (eq_str p2 p2') (eq_str c c')) then r else 0%Z.
Definition singleton_trans p1 p2 c r : transfers  := Some (singleton_trans' p1 p2 c r).
Definition add_trans' : trans -> trans -> trans := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c)%Z.
Definition add_trans : transfers -> transfers -> transfers := option_map2 add_trans'.
Definition scale_trans' : Z -> trans -> trans := fun s t p1 p2 c => (t p1 p2 c * s)%Z.
Definition scale_trans : option Z -> transfers -> transfers := option_map2 scale_trans'.

(* Traces represent the sequence of obligations that a contract
specifies. *)

Definition trace := nat -> transfers.

(* The following are combinators to contruct traces. *)

Definition const_trace (t : transfers) : trace := fun x => t.
Definition empty_trace : trace := const_trace empty_trans.
Definition singleton_trace (t : transfers) : trace
  := fun x => match x with 
                | O => t
                | _ => empty_trans
              end.
Definition scale_trace (s : option Z) (t : trace) : trace
  := scale_trans s ∘ t.

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
         (e : bexp) (rc : ext) (i : nat) : trace 
  := match B[|e|]rc with
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
      | Scale e c' => scale_trace R[|e|](fst rho) (C[|c'|]rho) 
      | Transl d c' => (delay_trace d) (C[|c'|](adv_ext (Z.of_nat d) rho))
      | Both c1 c2 => add_trace (C[|c1|]rho) (C[|c2|]rho)
      | IfWithin e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).
