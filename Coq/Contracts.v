Require Import String.
Require Import FunctionalExtensionality.
Require Import Basics.
Require Import ZArith.
Require Import LibTactics.
Require Import NPeano.

Import Compare_dec.

Infix "∘" := compose (at level 40, left associativity).


(********** Syntax **********)

Definition observable := string.
Definition currency := string.
Definition party := string.
Definition choice := string.

Definition eq_str (s1 s2 : string) : bool :=
  match string_dec s1 s2 with
      | left  _ => true
      | right _ => false
  end.

Inductive BinOp : Set :=
| Add : BinOp
| Mult : BinOp
| Subt : BinOp
| Min : BinOp
| Max : BinOp.

Inductive Cmp : Set :=
| EQ : Cmp
| LT : Cmp
| LTE : Cmp.

Inductive BoolOp : Set :=
| And : BoolOp
| Or : BoolOp.

Inductive iexp : Set :=
| ILit : Z -> iexp
| IBin : BinOp -> iexp -> iexp -> iexp 
| INeg : iexp -> iexp.

(* Real expressions (for simplicity, we use integers, though). *)

Inductive rexp : Set :=
| RLit : Z -> rexp
| RBin : BinOp -> rexp -> rexp -> rexp 
| RNeg : rexp -> rexp
| Obs : observable -> Z -> rexp.

Inductive bexp : Set :=
| BLit : bool -> bexp
| BChoice : choice -> Z -> bexp
| RCmp : Cmp -> rexp -> rexp -> bexp
| BNot : bexp -> bexp
| BOp : BoolOp -> bexp -> bexp -> bexp.

Inductive contract : Set :=
 | Zero : contract
 | TransfOne : currency -> party -> party -> contract
 | Scale : rexp -> contract -> contract
 | Transl : nat -> contract -> contract
 | Both : contract -> contract -> contract
 | IfWithin : bexp -> nat -> contract -> contract -> contract.

(********** Semantics **********)

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


Definition env := (obs * choices)%type.

Definition adv_env (d : Z) (rho : env) : env :=
  let (obs, ch) := rho in (adv_inp d obs, adv_inp d ch).
                                             

Lemma adv_env_0 e : adv_env 0 e = e.
Proof.
  unfold adv_env. destruct e. repeat rewrite adv_inp_0. reflexivity.
Qed.

Lemma adv_env_iter d d' e : adv_env d (adv_env d' e) = adv_env (d' + d) e.
Proof.
  unfold adv_env. destruct e. repeat rewrite adv_inp_iter. reflexivity.  
Qed.


Lemma adv_env_swap d d' e : 
  adv_env d (adv_env d' e) = adv_env d' (adv_env d e).
Proof.
    unfold adv_env. destruct e. f_equal; apply adv_inp_swap. 
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

Reserved Notation "'R[|' e '|]' r" (at level 9).

Fixpoint Rsem (e : rexp) : obs -> option Z :=
  fun rho => 
    match e with
      | RLit r => Some r
      | RBin op e1 e2 => option_map2 (RBinOp op) R[|e1|]rho R[|e2|]rho
      | RNeg e => option_map (Zminus 0) R[|e|]rho
      | Obs obs t => rho t obs
    end
      where "'R[|' e '|]' r" := (Rsem e r). 

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

Fixpoint Bsem (e : bexp) : env -> option bool :=
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

Fixpoint within_sem (c1 c2 : env -> trace) 
         (e : bexp) (rc : env) (i : nat) : trace 
  := match B[|e|]rc with
       | Some true => c1 rc
       | Some false => match i with
                         | O => c2 rc
                         | S j => delay_trace 1 (within_sem c1 c2 e (adv_env 1 rc) j)
                       end
       | None => const_trace bot_trans
     end.


(* Semantics of contracts. *)

Reserved Notation "'C[|' e '|]'" (at level 9).

Fixpoint Csem (c : contract) : env -> trace :=
  fun rho => 
    match c with
      | Zero => empty_trace
      | TransfOne p1 p2 c => singleton_trace (singleton_trans p1 p2 c  1)
      | Scale e c' => scale_trace R[|e|](fst rho) (C[|c'|]rho) 
      | Transl d c' => (delay_trace d) (C[|c'|](adv_env (Z.of_nat d) rho))
      | Both c1 c2 => add_trace (C[|c1|]rho) (C[|c2|]rho)
      | IfWithin e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).

(********** Monotonicity of the semantics **********)

Lemma Rsem_monotone e rho1 rho2 : rho1 ⊆ rho2 -> R[| e |]rho1 ⊆ R[| e |]rho2.
Proof.
  intro S; induction e; simpl; intros; auto.
  - destruct (R[|e1|]rho1); destruct (R[|e2|]rho1); tryfalse.
    apply lep_some in IHe1. apply lep_some in IHe2. 
    rewrite <- IHe1. rewrite <- IHe2. simpl in *. auto.
  - destruct (R[|e|]rho1); tryfalse. apply lep_some in IHe. rewrite <- IHe. auto. 
Qed.

Lemma Bsem_monotone e rho1 rho2 : rho1 ⊆ rho2 -> B[| e |]rho1 ⊆ B[| e |]rho2.
Proof.
  intro S; induction e; simpl; intros; auto.
  - destruct S. auto.
  - destruct S as [S1 S2]. 
    remember (R[|r|](fst rho1)) as X1. remember (R[|r0|](fst rho1)) as X2.
    pose (Rsem_monotone r _ _ S1) as R1. pose (Rsem_monotone r0 _ _ S1) as R2.
    destruct X1; tryfalse. destruct X2; tryfalse. 
    rewrite <- HeqX1 in R1. rewrite <- HeqX2 in R2.
    simpl in *. erewrite R1 by auto. erewrite R2 by auto.
    auto.
  - destruct (B[|e|]rho1); tryfalse. erewrite IHe by auto. assumption.
  - destruct (B[|e1|]rho1); tryfalse. destruct (B[|e2|]rho1); tryfalse.
    erewrite IHe1 by auto. erewrite IHe2 by auto.  assumption.
Qed.



Lemma adv_inp_monotone A (in1 in2 : inp A) n : in1 ⊆ in2 -> adv_inp n in1 ⊆ adv_inp n in2.
Proof. 
  unfold lep, adv_inp. simpl. intros. remember (in1 (n + i)%Z j) as X.
  destruct X;tryfalse. apply H. rewrite <- H0. auto. 
Qed.

Lemma adv_env_monotone rho1 rho2 n : rho1 ⊆ rho2 -> adv_env n rho1 ⊆ adv_env n rho2.
Proof. 
  intros. destruct rho1. destruct rho2. destruct H. split; apply adv_inp_monotone;
  auto.
Qed.


Theorem Csem_monotone c rho1 rho2 : rho1 ⊆ rho2 -> C[| c |]rho1 ⊆ C[| c |]rho2.
Proof.
  generalize dependent rho1. generalize dependent rho2. 
  induction c; intros rho2 rho1 S; simpl; intros; auto.
  - pose S as S'. destruct S' as [S1 S2]. 
    remember (R[|r|] (fst rho1)) as Y. destruct Y; tryfalse.
    pose (Rsem_monotone r (fst rho1) (fst rho2) S1). 
    unfold scale_trace in *. unfold compose in *.
    rewrite <- HeqY in *. apply lep_some in l. rewrite <- l.
    remember (C[|c|] rho1 i) as X.
    pose (IHc _ _ S i) as IHi. 
    destruct X; tryfalse. rewrite <- HeqX in * by auto. erewrite IHi by auto.
    auto.
  - simpl. apply adv_env_monotone with (n := Z.of_nat n) in S. apply IHc in S.
    simpl in S. unfold delay_trace in *. destruct (leb n i); auto.
  - unfold add_trace, add_trans in *. 
    remember (C[|c1|] rho1 i) as X1. remember (C[|c2|] rho1 i) as X2.
    pose (IHc1 _ _ S i) as IHi1. pose (IHc2 _ _ S i) as IHi2. 
    destruct X1; tryfalse. destruct X2; tryfalse. 
    symmetry in HeqX1. apply IHi1 in HeqX1.
    symmetry in HeqX2. apply IHi2 in HeqX2. 
    auto. erewrite HeqX1. erewrite HeqX2. auto.
  - generalize dependent rho1.
    generalize dependent rho2.
    generalize dependent i.
    induction n; intros.
    * simpl. simpl in H.  remember (B[|b|]rho1) as B.
      pose (Bsem_monotone b (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct b0. eapply IHc1; eauto.
      eapply IHc2; eauto.
    * simpl. simpl in H. remember (B[|b|]rho1) as B.
      pose (Bsem_monotone b (rho1) (rho2) S) as HB. 
      destruct B; tryfalse. symmetry in HeqB. apply HB in HeqB.
      rewrite HeqB. destruct b0. eapply IHc1; eauto.
      unfold delay_trace in *. destruct (leb 1 i).
      + eapply IHn. apply adv_env_monotone. eassumption. assumption.
      + assumption.
Qed.

(********** Reduction semantics **********)

Fixpoint adv_rexp (d : Z) (e : rexp) : rexp :=
  match e with
    | RLit r => RLit r
    | RBin op e1 e2 => RBin op (adv_rexp d e1) (adv_rexp d e2)
    | RNeg e' => RNeg (adv_rexp d e')
    | Obs o i => Obs o (d + i)%Z
  end.

Fixpoint adv_bexp (d : Z) (e : bexp) : bexp :=
  match e with
    | BLit b => BLit b
    | BChoice c i => BChoice c (d + i)
    | BOp op e1 e2 => BOp op (adv_bexp d e1) (adv_bexp d e2)
    | RCmp op e1 e2 => RCmp op (adv_rexp d e1) (adv_rexp d e2)
    | BNot e' => BNot (adv_bexp d e')
  end.


Inductive Red : contract -> env -> contract -> trans -> Prop :=
| red_zero rho : Red Zero rho Zero empty_trans'
| red_transf c p1 p2 rho : Red (TransfOne c p1 p2) rho Zero (singleton_trans' c p1 p2 1)
| red_scale e rho c c' t v :  R[| e |] (fst rho) = Some v -> Red c rho c' t ->
               Red (Scale e c) rho (Scale (adv_rexp (-1) e) c') (scale_trans' v t)
| red_trans0 c rho c' t : Red c rho c' t -> Red (Transl 0 c) rho c' t
| red_transS c rho n : Red (Transl (S n) c) rho (Transl n c) empty_trans'
| red_both c1 c1' c2 c2' rho t1 t2 : Red c1 rho c1' t1 -> Red c2 rho c2' t2 -> 
                         Red (Both c1 c2) rho (Both c1' c2') (add_trans' t1 t2)
| red_if0_false rho c1 c2 c' b t : B[|b|] rho = Some false -> Red c2 rho c' t -> Red (IfWithin b 0 c1 c2) rho c' t
| red_ifS_false rho c1 c2 n b : B[|b|] rho = Some false -> Red (IfWithin b (S n) c1 c2) rho (IfWithin b n c1 c2) empty_trans'
| red_if_true rho c1 c2 c' n b t : B[|b|] rho = Some true -> Red c1 rho c' t -> Red (IfWithin b n c1 c2) rho c' t
.

Hint Constructors Red.

Theorem red_sound1 c c' rho t  : Red c rho c' t ->  C[|c|]rho 0 = Some t.
Proof.
  intro R. induction R; simpl. 
  - reflexivity.
  - reflexivity.
  - unfold scale_trace, compose. rewrite IHR. rewrite H. reflexivity.
  - unfold delay_trace. simpl. rewrite adv_env_0. 
    assumption.
  - unfold delay_trace. reflexivity.
  - unfold add_trace. rewrite IHR1. rewrite IHR2. reflexivity.
  - rewrite H. assumption.
  - rewrite H. unfold delay_trace. reflexivity.
  - destruct n; simpl; rewrite H; assumption.
Qed.


Lemma adv_rexp_obs d e rho : R[|adv_rexp d e|]rho = R[|e|](adv_inp d rho).
Proof.
  induction e; simpl; first [reflexivity | f_equal; assumption].
Qed.

Lemma adv_rexp_env d e rho : R[|adv_rexp d e|](fst rho) = R[|e|](fst (adv_env d rho)).
Proof.
  destruct rho. simpl. apply adv_rexp_obs.
Qed.

Theorem red_sound2 c c' i rho t  : Red c rho c' t ->  C[|c|]rho (S i) = C[|c'|](adv_env 1 rho) i.
Proof.
  intros R. induction R; simpl.
  - reflexivity.
  - reflexivity.
  - unfold scale_trace, compose. rewrite -> adv_rexp_env. rewrite adv_env_iter. simpl.
    rewrite adv_env_0. rewrite IHR.  reflexivity.
  - unfold delay_trace. rewrite adv_env_0. assumption.
  - unfold delay_trace. simpl. rewrite adv_env_iter. 
    assert (Z.pos (Pos.of_succ_nat n) = (1 + Z.of_nat n)%Z).
    assert (1%Z = Z.of_nat 1) by reflexivity. rewrite H.
    rewrite <- Nat2Z.inj_add. reflexivity.
    rewrite H. reflexivity.
  - unfold add_trace. rewrite IHR1. rewrite IHR2. reflexivity.
  - rewrite H. assumption.
  - unfold delay_trace. rewrite H. simpl. f_equal. omega.
  - destruct n; simpl; rewrite H; assumption.
Qed.

Theorem red_complete c rho t : C[|c|]rho 0 = Some t -> exists c', Red c rho c' t.
Proof.
  generalize dependent t. induction c; simpl; intros.
  - inversion H. eauto.
  - inversion H. eauto.
  - unfold scale_trace, compose in *.
    remember (R[|r|](fst rho)) as R. destruct R; tryfalse.
    remember (C[|c|] rho 0) as C. destruct C;tryfalse. inversion H. 
    assert (exists c', Red c rho c' t0) as R by auto.
    destruct R as [c'].
    eexists. apply red_scale; auto. apply H0.
  - unfold delay_trace in *. destruct n; simpl in *. 
    + rewrite adv_env_0 in *. apply IHc in H. destruct H as [c'].
      eexists. constructor. apply H.
    + inversion H. eexists. constructor.
  -  unfold add_trace in *.
     destruct (C[|c1|] rho 0);tryfalse. destruct (C[|c2|] rho 0);tryfalse.
     pose (IHc1 _ eq_refl) as IH1.  pose (IHc2 _ eq_refl) as IH2.
     destruct IH1. destruct IH2. inversion H. 
     eexists. constructor; eassumption.
  - remember (B[|b|]rho) as B. destruct B as [b'| ]. 
    + destruct b'.
      * destruct n; simpl in *; rewrite <- HeqB in *;apply IHc1 in H;
        destruct H; eexists; apply red_if_true; eauto. 
      * destruct n; simpl in *;rewrite <- HeqB in *.
        apply IHc2 in H. destruct H. eexists. apply red_if0_false; eauto.
        unfold delay_trace in H. simpl in *. inversion H. eexists. constructor; auto.
    + destruct n; simpl in *; rewrite <- HeqB in *; inversion H.
Qed.
      

(********** Equivalence of contracts **********)

(* Full equivalence. *)

Definition equiv (c1 c2 : contract) : Prop := 
  forall rho : env, C[|c1|]rho = C[|c2|]rho.
Infix "≡" := equiv (at level 40).

(* [c1 ⊑ c2] iff the semantics of [c1] and [c2] coincidese "in all
places" that [c1]'s semantics is defined. *)

Definition lequiv (c1 c2 : contract) : Prop := 
  forall rho : env, C[|c1|]rho ⊆ C[|c2|]rho.

Infix "⊑" := lequiv (at level 40).

Definition total (t : trace) : Prop :=
  forall i, t i <> None.

(* Partial equivalence: equivalence on the total fragment of the
semantics. *)

Definition wequiv (c1 c2 : contract) : Prop := 
  forall rho : env, total (C[|c1|]rho) \/ total (C[|c2|]rho) -> 
                    C[|c1|]rho = C[|c2|]rho.


Infix "≃" := wequiv (at level 40).

(* We prove some equivalences. *)

(* First some lemmas and auxiliary definitions. *)

Lemma lequiv_total c1 c2 r : c1 ⊑ c2 -> total (C[|c1|]r) -> C[|c1|]r = C[|c2|]r.
Proof.
  unfold lequiv, total, lep. intros.   apply functional_extensionality. intro.
  remember (C[|c1|] r x) as C1. destruct C1. erewrite H. reflexivity. auto.
  symmetry in HeqC1. apply H0 in HeqC1. contradiction.
Qed.


Lemma adv_env_ch d rho : snd (adv_env d rho) = adv_inp d (snd rho).
Proof.
  unfold adv_env. destruct rho. reflexivity.
Qed.

Lemma adv_env_obs d rho : fst (adv_env d rho) = adv_inp d (fst rho).
Proof.
  unfold adv_env. destruct rho. reflexivity.
Qed.


Lemma adv_bexp_env d e rho : B[|adv_bexp d e|]rho = B[|e|](adv_env d rho).
Proof.
  induction e; simpl; try first [reflexivity | f_equal; assumption].
  rewrite adv_env_ch. reflexivity.
  repeat rewrite adv_rexp_obs. rewrite adv_env_obs. reflexivity.
Qed.


Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Theorem transl_ifwithin e d t c1 c2 : 
  IfWithin (adv_bexp (Z.of_nat d) e) t (Transl d c1) (Transl d c2) ⊑
  Transl d (IfWithin e t c1 c2).
Proof.
  unfold lequiv, lep. simpl. induction t; intros.
  simpl in *. rewrite adv_bexp_env in *. remember (B[|e|](adv_env (Z.of_nat d) rho)) as b.
  destruct b. destruct b;  assumption. 
  unfold const_trace, bot_trans in H. inversion H.

  simpl in *.  rewrite adv_bexp_env in *. 
  remember (B[|e|](adv_env (Z.of_nat d) rho)) as b. repeat destruct b. assumption. 
  rewrite adv_env_swap. rewrite delay_trace_swap. 
  unfold delay_trace at 1.
  unfold delay_trace at 1 in H. 
  remember (leb 1 i) as L. destruct L.
  apply IHt. apply H. assumption.

  unfold const_trace, bot_trans in H. inversion H.
Qed.

Lemma total_delay t d : total t <-> total (delay_trace d t).
Proof.
  split; unfold total, delay_trace; intros.
  
  remember (leb d i) as L. destruct L. apply H. unfold not. intro. tryfalse.

  pose (H (i + d)) as H'.
  assert (leb d (i + d) = true) as L by (apply leb_correct; omega).
  rewrite L in H'. assert (i + d - d = i) as E by omega. rewrite E in *. assumption.
  
Qed.

  
Lemma bot_trans_delay_at d : delay_trace d (const_trace bot_trans) d = None.
Proof.
  rewrite delay_trace_at. reflexivity.
Qed.

Lemma bot_trans_delay_total d : ~ total (delay_trace d (const_trace bot_trans)).
Proof.
  unfold not, total. intros.
  contradiction (H d (bot_trans_delay_at d)). 
Qed.


Theorem transl_ifwithin_wequiv e d t c1 c2 : 
  IfWithin (adv_bexp (Z.of_nat d) e) t (Transl d c1) (Transl d c2) ≃
  Transl d (IfWithin e t c1 c2). 
Proof.
  unfold wequiv. intros. destruct H. apply lequiv_total. apply transl_ifwithin. assumption.
  
  
  unfold lequiv, lep. simpl. generalize dependent rho. induction t; intros.
  simpl in *. rewrite adv_bexp_env in *. remember (B[|e|](adv_env (Z.of_nat d) rho)) as b.
  destruct b. destruct b; reflexivity.
  unfold total in H. 
  contradiction (H d (bot_trans_delay_at d)). 

  simpl in *.  rewrite adv_bexp_env in *. 
  remember (B[|e|](adv_env (Z.of_nat d) rho)) as b. repeat destruct b. reflexivity.
  rewrite adv_env_swap. rewrite delay_trace_swap. 
  rewrite IHt. reflexivity. rewrite delay_trace_swap in H. rewrite adv_env_swap.
  apply total_delay in H. assumption. apply bot_trans_delay_total in H. contradiction.
Qed.

  

(********** Causality **********)

(* [obs_until d r1 r2] iff [r1] [r2] coincide at [d] and earlier. *)

Definition inp_until {A} (d : Z) (r1 r2 : inp A) : Prop :=
  forall z, Z.le z d -> r1 z = r2 z.

Definition env_until (d : Z) (e1 e2 : env) : Prop :=
  inp_until d (fst e1) (fst e2) /\ inp_until d (snd e1) (snd e2).


(* Semantic causality *)

Definition causal (c : contract) : Prop :=
  forall d r1 r2,  env_until (Z.of_nat d) r1 r2 -> (C[|c|]r1) d = (C[|c|]r2) d.

(* Provable causality *)

Reserved Notation "'R|-' c" (at level 20).

Inductive rpc : rexp -> Prop:=
| rpc_obs : forall o i, Z.le i 0 -> R|- Obs o i
| rpc_lit : forall q, R|- (RLit q)
| rpc_bin : forall op e1 e2, R|- e1 -> R|- e2 -> R|- RBin op e1 e2
| rpc_neg : forall e, R|- e -> R|- RNeg e
                                         where "'R|-' e" := (rpc e). 

Reserved Notation "'B|-' c" (at level 20).

Inductive bpc : bexp -> Prop:=
| bpc_lit : forall b, B|- (BLit b)
| rpc_ch : forall ch i, Z.le i 0 -> B|- BChoice ch i
| bpc_cmp : forall cmp e1 e2, R|- e1 -> R|- e2 -> B|- RCmp cmp e1 e2
| bpc_op : forall op e1 e2, B|- e1 -> B|- e2 -> B|- BOp op e1 e2
| bpc_not : forall e, B|- e -> B|- BNot e
                                         where "'B|-' e" := (bpc e). 

Reserved Notation "'|-' c" (at level 20).

Inductive pc : contract -> Prop :=
| pc_transl : forall d c, |- c -> |- Transl d c
| pc_transf : forall cur p1 p2, |- TransfOne cur p1 p2
| pc_scale : forall e c, R|- e -> |- c -> |- Scale e c
| pc_both : forall c1 c2, |- c1 -> |- c2 -> |- Both c1 c2
| pc_zero : |- Zero
| pc_if : forall c1 c2 b l, B|- b -> |- c1 -> |- c2 -> |- IfWithin b l c1 c2
                                            where "'|-' c" := (pc c). 

(* Below follows the proof that provable causality is sound (i.e. it
implies semantic causality). *)

Lemma inp_until_adv {A} d t (r1 r2 : inp A): 
  inp_until d (adv_inp t r1) (adv_inp t r2) <-> inp_until (t + d) r1 r2.
Proof.
  split.
  unfold inp_until in *. intros.
  pose (H (z - t)%Z) as H'.
  unfold adv_inp in H'. 
  assert (t + (z - t) = z)%Z as E by omega.
  rewrite E in H'. apply H'. omega.

  unfold inp_until in *. intros.
  unfold adv_inp. 

  pose (H (t + z)%Z) as H'.  apply H'. omega.

Qed.

Lemma env_until_adv d t e1 e2: 
    env_until d (adv_env t e1) (adv_env t e2) <-> env_until (t + d) e1 e2.
Proof.
  unfold env_until. repeat rewrite adv_env_obs. repeat rewrite adv_env_ch.
  repeat rewrite inp_until_adv. reflexivity.
Qed.

Lemma rpc_inp_until e d r1 r2 : R|-e -> inp_until (Z.of_nat d) r1 r2 -> R[|e|]r1 = R[|e|]r2.
Proof.
  intros R O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in O. rewrite O. reflexivity. 
  eapply Z.le_trans. apply H. apply Nat2Z.is_nonneg.
Qed.

Lemma bpc_env_until e d r1 r2 : B|-e -> env_until (Z.of_nat d) r1 r2 -> B[|e|]r1 = B[|e|]r2.
Proof.
  intros R O. destruct O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in *. rewrite H0. reflexivity.
  eapply Z.le_trans. apply H1. apply Nat2Z.is_nonneg.

  f_equal; eapply rpc_inp_until; eassumption.
Qed.

Lemma env_until_adv_1 d r1 r2 : (1 <= d -> env_until d r1 r2 ->
                        env_until (d - 1) (adv_env 1 r1) (adv_env 1 r2))%Z.
Proof.
  intros.
  assert (1 + (d - 1) = d)%Z by omega.
  rewrite env_until_adv. rewrite H1. assumption.
Qed.


Theorem pc_causal c : |- c -> causal c.
Proof.
  intros. induction H; unfold causal in *; intros; simpl.

  unfold delay_trace.
  remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    apply IHpc. rewrite env_until_adv. assert (Z.of_nat d + Z.of_nat(d0 - d) = Z.of_nat d0)%Z as D.
    rewrite <- Nat2Z.inj_add. f_equal. omega.
    rewrite D. assumption.
    
    reflexivity.

  reflexivity.

  unfold scale_trace, compose. erewrite IHpc by apply H1.
  unfold scale_trans. destruct H1. rewrite rpc_inp_until with (r2:=fst r2) (d:=d) by assumption. 
reflexivity. 

  unfold add_trace. f_equal; auto.

  reflexivity.

  generalize dependent d. generalize dependent r1. generalize dependent r2. 
  induction l; intros; simpl.
  
  erewrite bpc_env_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0. eapply IHpc1; eassumption. 
  eapply IHpc2; eassumption. reflexivity. 

  erewrite bpc_env_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0.  eapply IHpc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L.  apply IHl. 
  rewrite Nat2Z.inj_sub.
  apply env_until_adv_1. symmetry in HeqL. apply leb_complete in HeqL. apply inj_le in HeqL. auto.
  auto.
  apply leb_complete. auto. auto. reflexivity. 
Qed.


(* Stronger provable causality *)

Reserved Notation "d 'R||-' c" (at level 20).

Inductive rppc : nat -> rexp -> Prop:=
| rppc_obs : forall o i, Z.to_nat i R||- Obs o i
| rppc_lit : forall q, 0 R||- (RLit q)
| rppc_bin : forall op e1 e2 d1 d2, d1 R||- e1 -> d2 R||- e2 -> max d1 d2 R||- RBin op e1 e2
| rppc_neg : forall e d, d R||- e -> d R||- RNeg e
                                         where "d 'R||-' e" := (rppc d e). 

Reserved Notation "d 'B||-' c" (at level 20).

Inductive bppc : nat -> bexp -> Prop:=
| bppc_lit : forall b, 0 B||- (BLit b)
| rppc_ch : forall ch i, Z.to_nat i B||- BChoice ch i
| bppc_cmp : forall cmp e1 e2 d1 d2, d1 R||- e1 -> d2 R||- e2 -> max d1 d2 B||- RCmp cmp e1 e2
| bppc_op : forall op e1 e2 d1 d2, d1 B||- e1 -> d2 B||- e2 -> max d1 d2 B||- BOp op e1 e2
| bppc_not : forall e d, d B||- e -> d B||- BNot e
                                         where "d 'B||-' e" := (bppc d e). 


Definition oplus (n : nat) : option nat -> option nat := option_map (plus n).
Lemma oplus_0 d : oplus 0 d = d.
Proof.
  destruct d; reflexivity.
Qed.
Definition omin (m n : option nat) : option nat := 
  match m with
      | Some m' => match n with
                     | Some n' => Some (min m' n')
                     | None => m
                   end
      | None => n
  end.
                     
Definition ole (m : nat) (n : option nat) : Prop := 
  match n with
     | Some n' => m <= n'
     | _ => True
  end.

Definition olt (m : nat) (n : option nat) : Prop := 
  match n with
     | Some n' => m < n'
     | _ => True
  end.

Reserved Notation "d '||-' c" (at level 20).

Inductive ppc : option nat -> contract -> Prop :=
| ppc_transl : forall d c b, b ||- c -> oplus d b ||- Transl d c
| ppc_transf : forall cur p1 p2, Some 0 ||- TransfOne cur p1 p2
| ppc_scale : forall e c b d, ole d b ->  d R||- e -> b ||- c -> b ||- Scale e c
| ppc_both : forall c1 c2 d1 d2, d1 ||- c1 -> d2 ||- c2 -> omin d1 d2 ||- Both c1 c2
| ppc_zero : None ||- Zero
| ppc_if : forall c1 c2 b l d1 d2, 0 B||- b -> d1 ||- c1 -> d2 ||- c2 
                                     -> omin d1 (oplus l d2) ||-  IfWithin b l c1 c2
                                            where "d '||-' c" := (ppc d c). 

Lemma inp_until_le {A} d1 d2 (r1 r2 : inp A) : Z.le d2 d1 -> inp_until d1 r1 r2 -> inp_until d2 r1 r2.
Proof. 
  unfold inp_until. intros. apply H0. omega.
Qed.

Ltac inp_until_max := eauto using inp_until_le, Z.le_max_l, Z.le_max_r.

Lemma env_until_le d1 d2 r1 r2 : Z.le d2 d1 -> env_until d1 r1 r2 -> env_until d2 r1 r2.
Proof. 
  unfold env_until. intros. destruct H0. split; eapply inp_until_le; eassumption.
Qed.

Ltac env_until_max := eauto using env_until_le, Z.le_max_l, Z.le_max_r.

Lemma rppc_inp_until e d r1 r2 : d R||-e  -> inp_until (Z.of_nat d) r1 r2 -> R[|e|]r1 = R[|e|]r2.
Proof.
  intros R O. induction R; simpl; try solve [f_equal; auto].

  unfold inp_until in O. rewrite O. reflexivity. pose (Z_le_dec i 0%Z) as Z.
  destruct Z. eapply Z.le_trans. apply l. apply Zle_0_nat. rewrite Z2Nat.id; omega.
  rewrite Nat2Z.inj_max in *.

  f_equal; first [apply IHR1|apply IHR2]; inp_until_max.
Qed.

Lemma bppc_env_until e d r1 r2 : d B||-e -> env_until (Z.of_nat d) r1 r2 -> B[|e|]r1 = B[|e|]r2.
Proof.
  intros R O. induction R; simpl; try solve [f_equal; auto].

  destruct O. unfold inp_until in *. rewrite H0. reflexivity.
  remember (0 <=? i)%Z as L. symmetry in HeqL. destruct L.
  rewrite <- Zle_is_le_bool in HeqL. rewrite Z2Nat.id; omega.
  rewrite Z.leb_gt in HeqL. pose (Zle_0_nat (Z.to_nat i)). omega.
  rewrite Nat2Z.inj_max in *.
  destruct O. f_equal; eapply rppc_inp_until; inp_until_max.
  rewrite Nat2Z.inj_max in *.
  f_equal; first [apply IHR1|apply IHR2]; env_until_max.
Qed.

Lemma delay_trace_empty d : delay_trace d (const_trace empty_trans) = const_trace empty_trans.
Proof.
  apply functional_extensionality. intros. unfold delay_trace, const_trace.
  remember (leb d x) as L. destruct L; reflexivity.
Qed.

Lemma scale_trans_empty s : scale_trans (Some s) empty_trans = empty_trans.
Proof.
  reflexivity. 
Qed.


Definition wcausal (c : contract) : Prop :=
  forall d r1 r2,  env_until (Z.of_nat d) r1 r2 -> 
                   (C[|c|]r1) d = None \/ (C[|c|]r2) d = None \/ (C[|c|]r1) d = (C[|c|]r2) d.

Lemma rppc_indep' c r d N : N = None -> 
                            N ||- c -> (C[|c|]r) d = None \/ (C[|c|]r) d = empty_trans.
Proof.
  assert (@None nat = None) as NeN by auto.
  intros NN H. generalize dependent r. generalize dependent d. induction H; intros.
  
  destruct b. inversion NN. 
  simpl. unfold delay_trace. remember (leb d d0) as L.
  destruct L. 
  pose (IHppc NeN (d0 - d) (adv_env (Z.of_nat d) r)) as IH. destruct IH; auto.
  auto.

  inversion NN.

  simpl. pose (IHppc NN d0 r) as IH. destruct IH. left.
  destruct (R[|e|](fst r)); simpl. rewrite H2. reflexivity. reflexivity.
  destruct (R[|e|](fst r)); simpl. rewrite H2. simpl. auto. auto.

  simpl. destruct d1; destruct d2; try inversion NN.
  
  pose (IHppc1 NeN d r) as IH1. pose (IHppc2 NeN d r) as IH2. unfold add_trace.
  destruct IH1. left. rewrite H1. reflexivity.
  destruct IH2. left. rewrite H2. destruct (C[|c1|] r d); reflexivity.
  right.  rewrite H1. rewrite H2. reflexivity.

  right. reflexivity.

  simpl. destruct d1; destruct d2; try inversion NN.

  pose (IHppc1 NeN d r) as IH1. pose (IHppc2 NeN d r) as IH2. 
  generalize dependent r. generalize dependent d.
  induction l; intros; simpl; remember (B[|b|]r) as bl; destruct bl.
  destruct b0. destruct IH1; auto. destruct IH2; auto.
  left. reflexivity. destruct b0. destruct IH1; auto. unfold delay_trace.
  remember (leb 1 d) as L. destruct L. apply IHl. reflexivity. auto. auto.
Qed.
  
Lemma olt_omin d d1 d2 : olt d (omin d1 d2) -> olt d d1 /\ olt d d2.
Proof.
  intros. destruct d1; destruct d2; simpl in *; try auto.
  rewrite Nat.min_glb_lt_iff in H. omega.
Qed.

Lemma olt_minus d b : olt d b -> olt (d-1) b.
Proof.
  intros. destruct b; simpl in *. omega. auto.
Qed.



Lemma rppc_indep c r d B :  B ||- c -> olt d B -> (C[|c|]r) d = None \/ (C[|c|]r) d = empty_trans.
Proof.
  intros H. generalize dependent r. generalize dependent d.
  induction H; intros; simpl in *.
  
  unfold delay_trace. remember (leb d d0) as L. destruct L.
  simpl. apply IHppc. destruct b; simpl in *. symmetry in HeqL. 
  apply leb_complete in HeqL. omega. auto. 

  auto.

  unfold singleton_trace. inversion H.

  unfold scale_trace, scale_trans, compose. 
  pose (IHppc d0 r H2) as IH.
  destruct IH as [IH|IH]. left. rewrite IH. apply option_map2_none.
  rewrite IH. remember (R[|e|](fst r)) as R. destruct R. simpl. auto.
  left. reflexivity.

  apply olt_omin in H1. destruct H1. eapply IHppc1 in H1.
  eapply IHppc2 in H2. unfold add_trace. destruct H1.
  left. erewrite H1. reflexivity. destruct H2.
  left. erewrite H2. apply option_map2_none.
  right. rewrite H1. rewrite H2. reflexivity.

  auto.

  apply olt_omin in H2. destruct H2.
  pose (IHppc1 d r H2) as IH1. 
  generalize dependent r. generalize dependent d.
  induction l; intros; simpl; remember (B[|b|]r) as bl; destruct bl.
  destruct b0. destruct IH1; auto. 
  rewrite oplus_0 in H3. apply IHppc2. assumption.
  auto. destruct b0. destruct IH1; auto. unfold delay_trace.
  remember (leb 1 d) as L. destruct L. pose (olt_minus _ _ H2) as H2'.
  apply IHl with (H2:=H2'). destruct d2; simpl in *. destruct d. tryfalse. 
  omega. auto. auto. auto.
Qed.

Lemma ole_olt d b : ole d b -> olt d b \/ b = Some d.
Proof.
  intros. destruct b; simpl in *. apply le_lt_or_eq in H. destruct H; auto. auto.
Qed.

Lemma ole_lt a b c : a < b -> ole b c -> olt a c.
Proof.
  intros. destruct c; simpl in *. omega. auto.
Qed.

Lemma le_dle a b c : a <= b -> ole b c -> ole a c.
Proof.
  intros. destruct c; simpl in *. omega. auto.
Qed.


Theorem ppc_causal d c : d ||- c -> wcausal c.
Proof.
  intros. induction H; unfold wcausal in *; intros; simpl.

  unfold delay_trace.
  remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    apply IHppc. rewrite env_until_adv. assert (Z.of_nat d + Z.of_nat (d0 - d) = Z.of_nat d0)%Z as D.
    rewrite <- Nat2Z.inj_add. f_equal. omega.
    rewrite D. assumption. auto.
    
    auto.
    
  unfold scale_trace, scale_trans, compose. 
  remember (R[|e|](fst r1)) as R1; remember (R[|e|](fst r2)) as R2; 
  destruct R1; destruct R2; try auto. 
  remember (leb d d0) as D. symmetry in HeqD. destruct D. rewrite leb_iff in HeqD.
  inversion H2 as [H2' H2'']. apply inj_le in HeqD.
  pose (inp_until_le _ _ _ _ HeqD H2') as O.
  pose (IHppc _ _ _ H2) as IH. destruct IH. left.
  rewrite H3. reflexivity. destruct H3. right. left. rewrite H3.
  reflexivity. right. right. rewrite H3. simpl. 
  remember (C[|c|] r2 d0) as C. destruct C; try reflexivity. 
  pose (rppc_inp_until e _ (fst r1) (fst r2) H0 O) as RE. rewrite RE in HeqR1. rewrite <- HeqR1 in HeqR2.
  inversion_clear HeqR2. reflexivity.
  
  rewrite leb_iff_conv in HeqD.
  eapply ole_lt in H; try apply HeqD. pose (rppc_indep c r2 d0 _ H1 H) as P. destruct P.
  right. left. rewrite H3. apply option_map2_none. pose (rppc_indep c r1 d0 _ H1 H) as P.
  destruct P. left. rewrite H4. apply option_map2_none. right. right.
  rewrite H3. rewrite H4. reflexivity.

  unfold add_trace, add_trans. 
  pose (IHppc1 d r1 r2 H1) as IH1. pose (IHppc2 d r1 r2 H1) as IH2.
  destruct IH1; first [rewrite H2| destruct H2; rewrite H2; auto]; auto.
  destruct IH2. rewrite H3. left. apply option_map2_none. destruct H3.
  rewrite H3. right. left. apply option_map2_none. right. right. rewrite H3.
  reflexivity.

  auto.

  assert (env_until 0 r1 r2). apply env_until_le with (d1:= Z.of_nat d). omega. assumption.
  generalize dependent d. generalize dependent r1. generalize dependent r2. 
  induction l; intros; simpl.
  
 
  erewrite bppc_env_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0. eapply IHppc1; eassumption. 
  eapply IHppc2; eassumption. auto.

  rewrite bppc_env_until with (r2:=r2) (d:=0) by assumption.
  remember (B[|b|]r2) as bl. destruct bl. destruct b0.  eapply IHppc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L. 
  symmetry in HeqL. rewrite leb_iff in HeqL. apply IHl. apply env_until_adv. simpl.  
  apply inj_le in HeqL. eapply env_until_le; eassumption. rewrite Nat2Z.inj_sub. apply env_until_adv_1.
  apply inj_le in HeqL. assumption. auto. auto. auto. auto.
Qed.

