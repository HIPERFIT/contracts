Require Import ZArith.
Require Import QArith.
Require Import String.
Require Import FunctionalExtensionality.
Require Import Basics.

Infix "∘" := compose (at level 40, left associativity).

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

Definition env := Z -> observable -> option Q.

Definition plusZnat (n : nat) (z : Z) : Z := Zplus (Z_of_nat n) z.

Lemma plusZnat_assoc z n m : plusZnat n (plusZnat m z) = plusZnat (plus n m) z. 
Proof.
  unfold plusZnat. rewrite -> Z.add_assoc. rewrite <- Nat2Z.inj_add. reflexivity.
Qed.

Definition advance_env (d : nat) (e : env) : env 
  := fun x => e (plusZnat d x).

Lemma advance_env_0 e : advance_env 0 e = e.
Proof.
  apply functional_extensionality.
  unfold advance_env. unfold plusZnat. rewrite Nat2Z.inj_0. reflexivity.
Qed.

Lemma advance_env_iter d d' e : advance_env d (advance_env d' e) = advance_env (plus d' d) e.
Proof.
  apply functional_extensionality. induction d'; intros.
  simpl. rewrite advance_env_0. reflexivity.
  simpl. unfold advance_env in *.  rewrite plusZnat_assoc. reflexivity.
Qed.


Lemma advance_env_swap d d' e : 
  advance_env d (advance_env d' e) = advance_env d' (advance_env d e).
Proof.
  repeat rewrite advance_env_iter. rewrite plus_comm. reflexivity.
Qed.


Definition RBinOp (op : BinOp) : Q -> Q -> Q :=
  match op with
    | Add => Qplus
    | Subt => Qminus
    | Mult => Qmult
    | Min => fun x y => if Qle_bool x y then x else y
    | Max => fun x y => if Qle_bool x y then y else x
  end.

Definition option_map2 {A B C :Type} (f:A->B->C) o1 o2 :=
  match o1,o2 with
    | Some a, Some b => Some (f a b)
    | _,_ => None
  end.

Reserved Notation "'R[|' e '|]' r" (at level 9).

Fixpoint Rsem (e : rexp) : env -> option Q :=
  fun rho => 
    match e with
      | RLit r => Some r
      | RBin op e1 e2 => option_map2 (RBinOp op) R[|e1|]rho R[|e1|]rho
      | RNeg e => option_map (Qminus 0) R[|e|]rho
      | Obs obs t => rho t obs
    end
      where "'R[|' e '|]' r" := (Rsem e r). 

Definition BBinOp (op : BoolOp) : bool -> bool -> bool :=
  match op with
    | And => andb
    | Or => orb
  end.

Definition RCompare (cmp : Cmp) : Q -> Q -> bool :=
  match cmp with
    | EQ => Qeq_bool
    | LTE => Qle_bool
    | LT => fun x y => negb (Qle_bool y x)
  end.


Reserved Notation "'B[|' e '|]' r" (at level 9).

Fixpoint Bsem (e : bexp) : env -> option bool :=
  fun rho => 
    match e with
      | BLit r => Some r
      | BOp op e1 e2 => option_map2 (BBinOp op) B[|e1|]rho B[|e2|]rho
      | BNot e => option_map negb B[|e|]rho
      | RCmp cmp e1 e2 => option_map2 (RCompare cmp) R[|e1|]rho R[|e2|]rho
    end
      where "'B[|' e '|]' r" := (Bsem e r). 


Definition transfers := party -> party -> currency -> Q.

Definition empty_trans : transfers := fun p1 p2 c => 0.
Definition singleton_trans p1 p2 c r : transfers 
  := fun p1' p2' c' => if andb (eq_str p1 p1') (andb (eq_str p2 p2') (eq_str c c')) then r else 0.
Definition add_trans (t1 t2 : transfers) : transfers
  := fun p1 p2 c => t1 p1 p2 c + t2 p1 p2 c.
Definition scale_trans (s : Q) (t : transfers) : transfers 
  := fun p1 p2 c => t p1 p2 c * s.

Definition trace := nat -> transfers.

Definition const_trace (t : transfers) : trace := fun x => t.
Definition empty_trace : trace := const_trace empty_trans.
Definition singleton_trace (t : transfers) : trace
  := fun x => match x with 
                | O => t
                | _ => empty_trans
              end.
Definition scale_trace (s : Q) (t : trace) : trace
  := scale_trans s ∘ t.

Definition delay_trace (d : nat) (t : trace) : trace :=
  fun x => match nat_compare x d with
               | Lt => empty_trans
               | _ => t (minus x d)
           end.

Definition add_trace (t1 t2 : trace) : trace 
  := fun x => add_trans (t1 x) (t2 x).


Fixpoint within_sem (c1 c2 : env -> option trace) (e : bexp) (r : env) (i : nat) : option trace 
            := match B[|e|]r with
                 | Some true => c1 r
                 | Some false => match i with
                                   | O => c2 r
                                   | S j => within_sem c1 c2 e (advance_env 1 r) j
                                 end
                 | None => None
               end.

Reserved Notation "'C[|' e '|]'" (at level 9).

Fixpoint Csem (c : contract) : env -> option trace :=
  fun rho => 
    match c with
      | Zero => Some empty_trace
      | TransfOne p1 p2 c => Some (singleton_trace (singleton_trans p1 p2 c 1))
      | Scale e c' => option_map2 scale_trace (R[|e|]rho) (C[|c'|]rho) 
      | Transl d c' => option_map (delay_trace d) (C[|c'|](advance_env d rho))
      | Both c1 c2 => option_map2 add_trace (C[|c1|]rho) (C[|c2|]rho)
      | IfWithin e d c1 c2 => within_sem C[|c1|] C[|c2|] e rho d
    end
      where "'C[|' e '|]'" := (Csem e).


Definition equiv (c1 c2 : contract) : Prop := 
  forall rho : env, C[|c1|]rho = C[|c2|]rho.

Infix "≡" := equiv (at level 40).

Fixpoint advance_rexp (d : nat) (e : rexp) : rexp :=
  match e with
    | RLit r => RLit r
    | RBin op e1 e2 => RBin op (advance_rexp d e1) (advance_rexp d e2)
    | RNeg e' => RNeg (advance_rexp d e')
    | Obs o i => Obs o (plusZnat d i)
  end.

Fixpoint advance_bexp (d : nat) (e : bexp) : bexp :=
  match e with
    | BLit b => BLit b
    | BOp op e1 e2 => BOp op (advance_bexp d e1) (advance_bexp d e2)
    | RCmp op e1 e2 => RCmp op (advance_rexp d e1) (advance_rexp d e2)
    | BNot e' => BNot (advance_bexp d e')
  end.

Lemma advance_rexp_env d e rho : R[|advance_rexp d e|]rho = R[|e|](advance_env d rho).
Proof.
  induction e; simpl; first [reflexivity | f_equal; assumption].
Qed.

Lemma advance_bexp_env d e rho : B[|advance_bexp d e|]rho = B[|e|](advance_env d rho).
Proof.
  induction e; simpl; try first [reflexivity | f_equal; assumption].
  repeat rewrite advance_rexp_env. reflexivity.
Qed.


Theorem transl_ifwithin e d t c1 c2 : 
  Transl d (IfWithin e t c1 c2) ≡
  IfWithin (advance_bexp d e) t (Transl d c1) (Transl d c2).
Proof.
  unfold equiv. simpl. intros. generalize dependent rho. induction t; intros.
  simpl. rewrite advance_bexp_env. remember (B[|e|](advance_env d rho)) as b.
  destruct b. destruct b; reflexivity. reflexivity.

  simpl. 
  rewrite advance_bexp_env. 
  remember (B[|e|](advance_env d rho)) as b. repeat destruct b. reflexivity. 
  rewrite advance_env_swap. apply IHt. reflexivity.
Qed.