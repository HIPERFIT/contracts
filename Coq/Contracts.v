Require Import QArith.
Require Import String.
Require Import FunctionalExtensionality.
Require Import Basics.
Require Import ZArith.
Require Import LibTactics.
Import Compare_dec.

Infix "∘" := compose (at level 40, left associativity).


(********** Syntax **********)

Definition observable := string.
Definition currency := string.
Definition party := string.

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

Inductive rexp : Set :=
| RLit : Q -> rexp
| RBin : BinOp -> rexp -> rexp -> rexp 
| RNeg : rexp -> rexp
| Obs : observable -> Z -> rexp.

Inductive bexp : Set :=
| BLit : bool -> bexp
(* | ICmp : Cmp -> iexp -> iexp -> bexp *)
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

Definition obs := Z -> observable -> option Q.

Definition plusZnat (n : nat) (z : Z) : Z := (Z_of_nat n + z)%Z.

Infix "+#" := plusZnat (at level 60, right associativity).

Lemma plusZnat_assoc z n m : n +# m +# z = (n + m +# z). 
Proof.
  unfold "+#". rewrite -> Z.add_assoc. rewrite <- Nat2Z.inj_add. reflexivity.
Qed.

(* Move observations into the future. *)

Definition adv_obs (d : nat) (e : obs) : obs 
  := fun x => e (d +# x).

Lemma adv_obs_0 e : adv_obs 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_obs. unfold "+#". rewrite Nat2Z.inj_0. reflexivity.
Qed.

Lemma adv_obs_iter d d' e : adv_obs d (adv_obs d' e) = adv_obs (d' + d) e.
Proof.
  apply functional_extensionality. induction d'; intros.
  simpl. rewrite adv_obs_0. reflexivity.
  simpl. unfold adv_obs in *.  rewrite plusZnat_assoc. reflexivity.
Qed.


Lemma adv_obs_swap d d' e : 
  adv_obs d (adv_obs d' e) = adv_obs d' (adv_obs d e).
Proof.
  repeat rewrite adv_obs_iter. rewrite plus_comm. reflexivity.
Qed.

(* Semantics of (real) binary operations. *)

Definition RBinOp (op : BinOp) : Q -> Q -> Q :=
  match op with
    | Add => Qplus
    | Subt => Qminus
    | Mult => Qmult
    | Min => fun x y => if Qle_bool x y then x else y
    | Max => fun x y => if Qle_bool x y then y else x
  end.

(* Lifts binary functions into [option] types. *)

Definition option_map2 {A B C :Type} (f:A->B->C) o1 o2 :=
  match o1,o2 with
    | Some a, Some b => Some (f a b)
    | _,_ => None
  end.

(* Semantics of real expressions. *)

Reserved Notation "'R[|' e '|]' r" (at level 9).

Fixpoint Rsem (e : rexp) : obs -> option Q :=
  fun rho => 
    match e with
      | RLit r => Some r
      | RBin op e1 e2 => option_map2 (RBinOp op) R[|e1|]rho R[|e1|]rho
      | RNeg e => option_map (Qminus 0) R[|e|]rho
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

Definition RCompare (cmp : Cmp) : Q -> Q -> bool :=
  match cmp with
    | EQ => Qeq_bool
    | LTE => Qle_bool
    | LT => fun x y => negb (Qle_bool y x)
  end.

(* Semantics of Boolean expressions *)

Reserved Notation "'B[|' e '|]' r" (at level 9).

Fixpoint Bsem (e : bexp) : obs -> option bool :=
  fun rho => 
    match e with
      | BLit r => Some r
      | BOp op e1 e2 => option_map2 (BBinOp op) B[|e1|]rho B[|e2|]rho
      | BNot e => option_map negb B[|e|]rho
      | RCmp cmp e1 e2 => option_map2 (RCompare cmp) R[|e1|]rho R[|e2|]rho
    end
      where "'B[|' e '|]' r" := (Bsem e r). 

(* Semantic structures for contracts. *)

(* An elemtn of type [transfers] represents a set of transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of transfers is undefined (read:
 "bottom"). *)

Definition transfers := option (party -> party -> currency -> Q).



Definition empty_trans : transfers := Some (fun p1 p2 c => 0%Q).
Definition bot_trans : transfers := None.
Definition singleton_trans p1 p2 c r : transfers 
  := Some (fun p1' p2' c' => if andb (eq_str p1 p1') (andb (eq_str p2 p2') (eq_str c c')) then r else 0%Q).
Definition add_trans : transfers -> transfers -> transfers
  := option_map2 (fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c)%Q).
Definition scale_trans : option Q -> transfers -> transfers 
  := option_map2 (fun s t p1 p2 c => (t p1 p2 c * s)%Q).

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
Definition scale_trace (s : option Q) (t : trace) : trace
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

Fixpoint within_sem (c1 c2 : obs -> trace) (e : bexp) (r : obs) (i : nat) : trace 
  := match B[|e|]r with
       | Some true => c1 r
       | Some false => match i with
                         | O => c2 r
                         | S j => delay_trace 1 (within_sem c1 c2 e (adv_obs 1 r) j)
                       end
       | None => const_trace bot_trans
     end.


(* Semantics of contracts. *)

Reserved Notation "'C[|' e '|]'" (at level 9).

Fixpoint Csem (c : contract) : obs -> trace :=
  fun rho => 
    match c with
      | Zero => empty_trace
      | TransfOne p1 p2 c => singleton_trace (singleton_trans p1 p2 c  1)
      | Scale e c' => scale_trace (R[|e|]rho) (C[|c'|]rho) 
      | Transl d c' => (delay_trace d) (C[|c'|](adv_obs d rho))
      | Both c1 c2 => add_trace (C[|c1|]rho) (C[|c2|]rho)
      | IfWithin e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).

(********** Equivalence of contracts **********)

(* [t1 ⊆ t2] iff [t1] and [t2] coincide in all points that [t1] is
defined. *)

Definition letrace (t1 t2 : trace) : Prop :=
  forall i z , t1 i = Some z -> t2 i = Some z.

Infix "⊆" := letrace (at level 40).

(* Full equivalence. *)

Definition equiv (c1 c2 : contract) : Prop := 
  forall rho : obs, C[|c1|]rho = C[|c2|]rho.
Infix "≡" := equiv (at level 40).

(* [c1 ⊑ c2] iff the semantics of [c1] and [c2] coincidese "in all
places" that [c1]'s semantics is defined. *)

Definition lequiv (c1 c2 : contract) : Prop := 
  forall rho : obs, C[|c1|]rho ⊆ C[|c2|]rho.

Infix "⊑" := lequiv (at level 40).

Definition total (t : trace) : Prop :=
  forall i, t i <> None.

(* Partial equivalence: equivalence on the total fragment of the
semantics. *)

Definition wequiv (c1 c2 : contract) : Prop := 
  forall rho : obs, total (C[|c1|]rho) \/ total (C[|c2|]rho) -> 
                    C[|c1|]rho = C[|c2|]rho.


Infix "≃" := wequiv (at level 40).

(* We prove some equivalences. *)

(* First some lemmas and auxiliary definitions. *)

Lemma lequiv_total c1 c2 r : c1 ⊑ c2 -> total (C[|c1|]r) -> C[|c1|]r = C[|c2|]r.
Proof.
  unfold lequiv, total, letrace. intros.   apply functional_extensionality. intro.
  remember (C[|c1|] r x) as C1. destruct C1. erewrite H. reflexivity. auto.
  symmetry in HeqC1. apply H0 in HeqC1. contradiction.
Qed.


Fixpoint adv_rexp (d : nat) (e : rexp) : rexp :=
  match e with
    | RLit r => RLit r
    | RBin op e1 e2 => RBin op (adv_rexp d e1) (adv_rexp d e2)
    | RNeg e' => RNeg (adv_rexp d e')
    | Obs o i => Obs o (d +# i)
  end.

Fixpoint adv_bexp (d : nat) (e : bexp) : bexp :=
  match e with
    | BLit b => BLit b
    | BOp op e1 e2 => BOp op (adv_bexp d e1) (adv_bexp d e2)
    | RCmp op e1 e2 => RCmp op (adv_rexp d e1) (adv_rexp d e2)
    | BNot e' => BNot (adv_bexp d e')
  end.

Lemma adv_rexp_obs d e rho : R[|adv_rexp d e|]rho = R[|e|](adv_obs d rho).
Proof.
  induction e; simpl; first [reflexivity | f_equal; assumption].
Qed.

Lemma adv_bexp_obs d e rho : B[|adv_bexp d e|]rho = B[|e|](adv_obs d rho).
Proof.
  induction e; simpl; try first [reflexivity | f_equal; assumption].
  repeat rewrite adv_rexp_obs. reflexivity.
Qed.


Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Theorem transl_ifwithin e d t c1 c2 : 
  IfWithin (adv_bexp d e) t (Transl d c1) (Transl d c2) ⊑
  Transl d (IfWithin e t c1 c2).
Proof.
  unfold lequiv, letrace. simpl. induction t; intros.
  simpl in *. rewrite adv_bexp_obs in *. remember (B[|e|](adv_obs d rho)) as b.
  destruct b. destruct b;  assumption. 
  unfold const_trace, bot_trans in H. inversion H.

  simpl in *.  rewrite adv_bexp_obs in *. 
  remember (B[|e|](adv_obs d rho)) as b. repeat destruct b. assumption. 
  rewrite adv_obs_swap. rewrite delay_trace_swap. 
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
  IfWithin (adv_bexp d e) t (Transl d c1) (Transl d c2) ≃
  Transl d (IfWithin e t c1 c2). 
Proof.
  unfold wequiv. intros. destruct H. apply lequiv_total. apply transl_ifwithin. assumption.
  
  
  unfold lequiv, letrace. simpl. generalize dependent rho. induction t; intros.
  simpl in *. rewrite adv_bexp_obs in *. remember (B[|e|](adv_obs d rho)) as b.
  destruct b. destruct b; reflexivity.
  unfold total in H. 
  contradiction (H d (bot_trans_delay_at d)). 

  simpl in *.  rewrite adv_bexp_obs in *. 
  remember (B[|e|](adv_obs d rho)) as b. repeat destruct b. reflexivity.
  rewrite adv_obs_swap. rewrite delay_trace_swap. 
  rewrite IHt. reflexivity. rewrite delay_trace_swap in H. rewrite adv_obs_swap.
  apply total_delay in H. assumption. apply bot_trans_delay_total in H. contradiction.
Qed.

  

(********** Causality **********)

(* [obs_until d r1 r2] iff [r1] [r2] coincide at [d] and earlier. *)

Definition obs_until (d : nat) (r1 r2 : obs) : Prop :=
  forall z, Z.le z (Z.of_nat d) -> r1 z = r2 z.

(* Semantic causality *)

Definition causal (c : contract) : Prop :=
  forall d r1 r2,  obs_until d r1 r2 -> (C[|c|]r1) d = (C[|c|]r2) d.

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

Lemma obs_until_adv d t r1 r2: 
  obs_until d (adv_obs t r1) (adv_obs t r2) <-> obs_until (t + d) r1 r2.
Proof.
  split.
  unfold obs_until in *. intros.
  pose (H (z - Z.of_nat t)%Z) as H'.
  unfold adv_obs in H'. unfold "+#" in H'.
  assert (Z.of_nat t + (z - Z.of_nat t) = z)%Z as E by omega.
  rewrite E in H'. apply H'.
  rewrite Nat2Z.inj_add in H0. omega.

  unfold obs_until in *. intros.
  unfold adv_obs. unfold "+#".

  pose (H (Z.of_nat t + z)%Z) as H'.  apply H'. rewrite Nat2Z.inj_add. omega.

Qed.


Lemma rpc_obs_until e d r1 r2 : R|-e -> obs_until d r1 r2 -> R[|e|]r1 = R[|e|]r2.
Proof.
  intros R O. induction R; simpl; try (f_equal; assumption).

  unfold obs_until in O. rewrite O. reflexivity. 
  eapply Z.le_trans. apply H. apply Nat2Z.is_nonneg.
Qed.

Lemma bpc_obs_until e d r1 r2 : B|-e -> obs_until d r1 r2 -> B[|e|]r1 = B[|e|]r2.
Proof.
  intros R O. induction R; simpl; try (f_equal; assumption).

  f_equal; eapply rpc_obs_until; eassumption.
Qed.
  

Theorem pc_causal c : |- c -> causal c.
Proof.
  intros. induction H; unfold causal in *; intros; simpl.

  unfold delay_trace.
  remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    apply IHpc. rewrite obs_until_adv. assert (d + (d0 - d) = d0) as D by omega.
    rewrite D. assumption.
    
    reflexivity.

  reflexivity.

  unfold scale_trace, compose. erewrite IHpc by apply H1.
  unfold scale_trans. rewrite rpc_obs_until with (r2:=r2) (d:=d) by assumption. reflexivity. 

  unfold add_trace. f_equal; auto.

  reflexivity.

  generalize dependent d. generalize dependent r1. generalize dependent r2. 
  induction l; intros; simpl.
  
  erewrite bpc_obs_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0. eapply IHpc1; eassumption. 
  eapply IHpc2; eassumption. reflexivity. 

  erewrite bpc_obs_until with (r2:=r2) by eassumption. 
  remember (B[|b|]r2) as bl. destruct bl. destruct b0.  eapply IHpc1; eassumption. 
  unfold delay_trace. remember (leb 1 d) as L. destruct L.  apply IHl.
  unfold obs_until, adv_obs. intros. unfold "+#". unfold obs_until in H2. apply H2.
  rewrite Nat2Z.inj_sub in H3. omega. apply leb_complete. auto. reflexivity. reflexivity.
Qed.

