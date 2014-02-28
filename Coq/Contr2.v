Set Implicit Arguments.
Require Import Bool Arith String List CpdtTactics.
Require Import Basics ZArith.
Require Import FunctionalExtensionality.
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

Inductive type := 
| IntT: type
| RealT: type 
| BoolT: type
| PairT: type -> type -> type.

Definition isNum (t: type) : Prop :=
  match t with
    | IntT => True
    | RealT => True
    | _ => False
  end.

Definition isBase (t: type) : Prop :=
  match t with
    | IntT => True
    | RealT => True
    | BoolT => True
    | _ => False
  end.

Inductive binop : type -> type -> type -> Set := 
| Add: forall t, isNum t -> binop t t t
| Sub: forall t, isNum t -> binop t t t
| Mul: forall t, isNum t -> binop t t t
| Lt : forall t, isNum t -> binop t t BoolT
| Lte: forall t, isNum t -> binop t t BoolT
| Min: forall t, isNum t -> binop t t t
| Max: forall t, isNum t -> binop t t t
| Eq : forall t, isBase t -> binop t t BoolT
| And : binop BoolT BoolT BoolT
| Or : binop BoolT BoolT BoolT.

Inductive unop : type -> type -> Set :=
| NegI: unop IntT IntT
| NotB: unop BoolT BoolT.

Inductive val : type -> Set :=
| ILitV : Z -> val IntT
| RLitV : Z -> val RealT
| BLitV : bool -> val BoolT
| PairV : forall t1 t2, val t1 -> val t2 -> val (PairT t1 t2).

Inductive exp : type -> Set :=
| ILit : Z -> exp IntT
| RLit : Z -> exp RealT
| BLit : bool -> exp BoolT
| Binop : forall t1 t2 tr, binop t1 t2 tr -> exp t1 -> exp t2 -> exp tr
| Unop : forall t1 tr, unop t1 tr -> exp t1 -> exp tr
| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (PairT t1 t2)
| Fst : forall t1 t2, exp (PairT t1 t2) -> exp t1
| Snd : forall t1 t2, exp (PairT t1 t2) -> exp t2
| Obs : observable -> Z -> exp RealT
| Choice : choice -> Z -> exp BoolT.

(********** Semantics **********)

(* Observations: mapping observables to values *)

Definition inp (A : Set) := Z -> observable -> option A.
Definition obs := inp Z.

Definition choices := inp bool.

Definition plusZnat (n : nat) (z : Z) : Z := (Z_of_nat n + z)%Z.

Infix "+#" := plusZnat (at level 60, right associativity).

Lemma plusZnat_assoc z n m : n +# m +# z = (n + m +# z). 
Proof.
  unfold "+#". rewrite -> Z.add_assoc. rewrite <- Nat2Z.inj_add. reflexivity.
Qed.


(* Move observations into the future. *)

Definition adv_inp {A} (d : nat) (e : inp A) : inp A
  := fun x => e (d +# x).

Lemma adv_inp_0 A (e : inp A) : adv_inp 0 e = e.
Proof.
  apply functional_extensionality.
  unfold adv_inp. unfold "+#". rewrite Nat2Z.inj_0. reflexivity.
Qed.

Lemma adv_inp_iter {A} d d' (e : inp A) : adv_inp d (adv_inp d' e) = adv_inp (d' + d) e.
Proof.
  apply functional_extensionality. induction d'; intros.
  simpl. rewrite adv_inp_0. reflexivity.
  simpl. unfold adv_inp in *.  rewrite plusZnat_assoc. reflexivity.
Qed.

Lemma adv_inp_swap {A} d d' (e : inp A) : 
  adv_inp d (adv_inp d' e) = adv_inp d' (adv_inp d e).
Proof.
  repeat rewrite adv_inp_iter. rewrite plus_comm. reflexivity.
Qed.


(* Environments *)

Definition env := (obs * choices)%type.

Definition adv_env (d : nat) (rho : env) : env :=
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


(* Semantics of expressions *)

Fixpoint typeDen (typ:type) : Set :=
  match typ with
    | IntT => Z
    | RealT => Z
    | BoolT => bool
    | PairT t1 t2 => typeDen t1 * typeDen t2
  end%type.

Definition doUnop (t1:type) (t2:type) (op:unop t1 t2) : typeDen t1 -> typeDen t2 :=
  match op in unop t1 t2 return typeDen t1 -> typeDen t2 with
    | NegI => Zminus 0
    | NotB => negb
  end.

Definition doCmpop typ (opI:Z->Z->bool) (opR:Z->Z->bool) 
: typeDen typ -> typeDen typ -> bool :=
  match typ with
    | IntT => opI
    | RealT => opR
    | _ => fun _ _ => false
  end.

Fixpoint doEq typ : typeDen typ -> typeDen typ -> bool :=
  match typ with
    | IntT => fun n1 n2 => if Z.eqb n1 n2 then true else false
    | RealT => fun n1 n2 => if Z.eqb n1 n2 then true else false
    | BoolT => bool_eq
    | _ => fun _ _ => false
  end.

Definition doNumop typ (opI:Z->Z->Z) (opR:Z->Z->Z) 
: typeDen typ -> typeDen typ -> typeDen typ :=
  match typ with
      | IntT => opI
      | RealT => opR
      | _ => fun x y => x
  end.

Definition doBinop (t1:type) (t2:type) (tr:type) (op:binop t1 t2 tr) 
: typeDen t1 -> typeDen t2 -> typeDen tr :=
  match op in binop t1 t2 tr return typeDen t1 -> typeDen t2 -> typeDen tr with
    | Add t1 _ => doNumop t1 Zplus Zplus
    | Sub t1 _ => doNumop t1 Zminus Zminus
    | Mul t1 _ => doNumop t1 Zmult Zmult
    | Min t1 _ => doNumop t1 (fun x y => if Z.leb x y then x else y)
                          (fun x y => if Z.leb x y then x else y)
    | Max t1 _ => doNumop t1 (fun x y => if Z.leb x y then y else x)
                          (fun x y => if Z.leb x y then y else x)
    | Lt t1 _ => doCmpop t1 Z.ltb Z.ltb
    | Lte t1 _ => doCmpop t1 Z.leb Z.leb
    | Eq t1 _ => doEq t1
    | And => andb
    | Or => orb
  end.

Definition omap {A B :Type} (f:A->B) o :=
  match o with
    | Some x => Some(f x)
    | None => None
  end.

Definition omap2 {A B C :Type} (f:A->B->C) o1 o2 :=
  match o1,o2 with
    | Some a, Some b => Some (f a b)
    | _,_ => None
  end.

Fixpoint Esem (t:type) (e:exp t) (r:env) : option (typeDen t) :=
  match e in exp t return option (typeDen t) with
    | Obs ob x => fst r x ob
    | Choice ch x => snd r x ch
    | ILit v => Some v
    | RLit v => Some v
    | BLit v => Some v
    | Pair _ _ e1 e2 => omap2 (fun v1 v2 => (v1,v2)) (Esem e1 r) (Esem e2 r)
    | Fst _ _ e => omap (fun v => fst v) (Esem e r)
    | Snd _ _ e => omap (fun v => snd v) (Esem e r)
    | Binop _ _ _ op e1 e2 => omap2 (doBinop op) (Esem e1 r) (Esem e2 r)
    | Unop _ _ op e1 => omap (doUnop op) (Esem e1 r)
  end.

Extraction Language Haskell.
Extraction "Esem.hs" Esem.

Inductive contract : Set :=
 | Zero : contract
 | TransfOne : currency -> party -> party -> contract
 | Scale : exp RealT -> contract -> contract
 | Transl : nat -> contract -> contract
 | Both : contract -> contract -> contract
 | IfWithin : exp BoolT -> nat -> contract -> contract -> contract.

(* Semantic structures for contracts. *)

(* An element of type [transfers] represents a set of transfers that a
 contract specifies at a particular point in time. It can also be
 [None], which indicates that the set of transfers is undefined (read:
 "bottom"). *)

Definition transfers := option (party -> party -> currency -> Z).

Definition empty_trans : transfers := Some (fun p1 p2 c => 0%Z).
Definition bot_trans : transfers := None.
Definition singleton_trans p1 p2 c r : transfers 
  := Some (fun p1' p2' c' => if andb (eq_str p1 p1') (andb (eq_str p2 p2') (eq_str c c')) then r else 0%Z).
Definition add_trans : transfers -> transfers -> transfers
  := omap2 (fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c)%Z).
Definition scale_trans : option Z -> transfers -> transfers 
  := omap2 (fun s t p1 p2 c => (t p1 p2 c * s)%Z).

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
         (e : exp BoolT) (rc : env) (i : nat) : trace 
  := match Esem e rc with
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
      | TransfOne p1 p2 c => singleton_trace (singleton_trans p1 p2 c 1)
      | Scale e c' => scale_trace (Esem e rho) (C[|c'|]rho) 
      | Transl d c' => (delay_trace d) (C[|c'|](adv_env d rho))
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
  unfold lequiv, total, letrace. intros.   apply functional_extensionality. intro.
  remember (C[|c1|] r x) as C1. destruct C1. erewrite H. reflexivity. auto.
  symmetry in HeqC1. apply H0 in HeqC1. contradiction.
Qed.


Fixpoint adv_exp (t:type) (d : nat) (e : exp t) : exp t :=
  match e with
    | ILit x => ILit x
    | RLit x => RLit x
    | BLit x => BLit x
    | Binop t1 t2 tr op e1 e2 =>
      Binop op (adv_exp d e1) (adv_exp d e2)
    | Unop t1 tr op e1 => Unop op (adv_exp d e1)
    | Pair t1 t2 e1 e2 => Pair (adv_exp d e1) (adv_exp d e2)
    | Fst t1 t2 e1 => Fst (adv_exp d e1)
    | Snd t1 t2 e1 => Snd (adv_exp d e1)
    | Obs o i => Obs o (d +# i)
    | Choice c i => Choice c (d +# i)
  end.

Lemma adv_exp_obs t d (e:exp t) rho : Esem (adv_exp d e) rho = Esem e (adv_env d rho).
Proof.
  induction e; destruct rho; crush.
Qed.

Lemma adv_env_ch d rho : snd (adv_env d rho) = adv_inp d (snd rho).
Proof.
  unfold adv_env. destruct rho. reflexivity.
Qed.

Lemma adv_env_obs d rho : fst (adv_env d rho) = adv_inp d (fst rho).
Proof.
  unfold adv_env. destruct rho. reflexivity.
Qed.

(*
Lemma adv_bexp_env d e rho : B[|adv_bexp d e|]rho = B[|e|](adv_env d rho).
Proof.
  induction e; simpl; try first [reflexivity | f_equal; assumption].
  rewrite adv_env_ch. reflexivity.
  repeat rewrite adv_rexp_obs. rewrite adv_env_obs. reflexivity.
Qed.
*)

Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Theorem transl_ifwithin e d t c1 c2 : 
  IfWithin (adv_exp d e) t (Transl d c1) (Transl d c2) ⊑
  Transl d (IfWithin e t c1 c2).
Proof.
  unfold lequiv, letrace. simpl. induction t; intros.
  simpl in *. rewrite adv_exp_obs in *. 
  destruct (Esem e (adv_env d rho)). destruct t;  assumption. 
  unfold const_trace, bot_trans in H. inversion H.

  simpl in *.  rewrite adv_exp_obs in *.
  destruct (Esem e (adv_env d rho)). destruct t0. assumption.
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
  
  remember (leb d i) as L. destruct L. apply H. unfold not. intro. 
  unfold empty_trans in H0. inversion H0.

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
  IfWithin (adv_exp d e) t (Transl d c1) (Transl d c2) ≃
  Transl d (IfWithin e t c1 c2). 
Proof.
  unfold wequiv. intros. destruct H. apply lequiv_total. apply transl_ifwithin. assumption.
    
  unfold lequiv, letrace. simpl. generalize dependent rho. induction t; intros.
  simpl in *. rewrite adv_exp_obs in *. destruct (Esem e (adv_env d rho)).
  destruct t; reflexivity.
  unfold total in H.
  contradiction (H d (bot_trans_delay_at d)).

  simpl in *.  rewrite adv_exp_obs in *.
  destruct (Esem e (adv_env d rho)). destruct t0. reflexivity.
  rewrite adv_env_swap. rewrite delay_trace_swap.
  rewrite IHt. reflexivity. rewrite delay_trace_swap in H. rewrite adv_env_swap.
  apply total_delay in H. assumption. apply bot_trans_delay_total in H. contradiction.
Qed.


(********** Causality **********)

(* [obs_until d r1 r2] iff [r1] [r2] coincide at [d] and earlier. *)

Definition inp_until {A} (d : nat) (r1 r2 : inp A) : Prop :=
  forall z, Z.le z (Z.of_nat d) -> r1 z = r2 z.

Definition env_until (d : nat) (e1 e2 : env) : Prop :=
  inp_until d (fst e1) (fst e2) /\ inp_until d (snd e1) (snd e2).


(* Semantic causality *)

Definition causal (c : contract) : Prop :=
  forall d r1 r2,  env_until d r1 r2 -> (C[|c|]r1) d = (C[|c|]r2) d.

(* Provable causality *)

Reserved Notation "'E|-' c" (at level 20).

(*
Inductive epc : forall (t :type), exp t -> Prop:=
| epc_obs : forall o i, Z.le i 0 -> E|- Obs o i
| epc_ilit : forall q, E|- (ILit q)
| epc_rlit : forall q, E|- (RLit q)
| epc_blit : forall q, E|- (BLit q)
| epc_binop : forall (t1 t2 tr:type) op e1 e2, E|- e1 -> E|- e2 -> E|- Binop op e1 e2

                                         where "'E|-' e" := (epc e).

| epc_neg : forall e, R|- e -> E|- RNeg e
                                         where "'E|-' e" := (epc e). 

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
  pose (H (z - Z.of_nat t)%Z) as H'.
  unfold adv_inp in H'. unfold "+#" in H'.
  assert (Z.of_nat t + (z - Z.of_nat t) = z)%Z as E by omega.
  rewrite E in H'. apply H'.
  rewrite Nat2Z.inj_add in H0. omega.

  unfold inp_until in *. intros.
  unfold adv_inp. unfold "+#".

  pose (H (Z.of_nat t + z)%Z) as H'.  apply H'. rewrite Nat2Z.inj_add. omega.

Qed.

Lemma env_until_adv d t e1 e2: 
    env_until d (adv_env t e1) (adv_env t e2) <-> env_until (t + d) e1 e2.
Proof.
  unfold env_until. repeat rewrite adv_env_obs. repeat rewrite adv_env_ch.
  repeat rewrite inp_until_adv. reflexivity.
Qed.

Lemma rpc_inp_until e d r1 r2 : R|-e -> inp_until d r1 r2 -> R[|e|]r1 = R[|e|]r2.
Proof.
  intros R O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in O. rewrite O. reflexivity. 
  eapply Z.le_trans. apply H. apply Nat2Z.is_nonneg.
Qed.

Lemma bpc_env_until e d r1 r2 : B|-e -> env_until d r1 r2 -> B[|e|]r1 = B[|e|]r2.
Proof.
  intros R O. destruct O. induction R; simpl; try (f_equal; assumption).

  unfold inp_until in *. rewrite H0. reflexivity.
  eapply Z.le_trans. apply H1. apply Nat2Z.is_nonneg.

  f_equal; eapply rpc_inp_until; eassumption.
Qed.

Lemma env_until_adv_1 d r1 r2 : 1 <= d -> env_until d r1 r2 ->
                        env_until (d - 1) (adv_env 1 r1) (adv_env 1 r2).
Proof.
  intros.
  assert (1 + (d - 1) = d) by omega.
  rewrite env_until_adv. rewrite H1. assumption.
Qed.


Theorem pc_causal c : |- c -> causal c.
Proof.
  intros. induction H; unfold causal in *; intros; simpl.

  unfold delay_trace.
  remember (leb d d0) as C. destruct C.
    symmetry in HeqC. apply leb_complete in HeqC.
    apply IHpc. rewrite env_until_adv. assert (d + (d0 - d) = d0) as D by omega.
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
  apply env_until_adv_1. apply leb_complete. auto. auto. reflexivity. reflexivity.
Qed.

*)