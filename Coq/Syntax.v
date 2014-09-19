Require Import String.
Require Import ZArith.
Require Export Vector.

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

Inductive rexp' : nat -> Type :=
| RLit n : Z -> rexp' n
| RBin n : BinOp -> rexp' n -> rexp' n -> rexp' n
| RNeg  n : rexp' n -> rexp' n
| Obs n : observable -> Z -> rexp' n
| RVar n : fin n -> rexp' n
| RAcc n : rexp' (S n) -> nat -> rexp' n -> rexp' n. 

Implicit Arguments RLit [[n]].
Implicit Arguments RBin [[n]].
Implicit Arguments RNeg [[n]].
Implicit Arguments Obs [[n]].
Implicit Arguments RVar [[n]].
Implicit Arguments RAcc [[n]].

Definition rexp := rexp' 0.

Inductive bexp : Type :=
| BLit : bool -> bexp
| BChoice : choice -> Z -> bexp
| RCmp : Cmp -> rexp -> rexp -> bexp
| BNot : bexp -> bexp
| BOp : BoolOp -> bexp -> bexp -> bexp.

Inductive contract : Type :=
 | Zero : contract
 | TransfOne : currency -> party -> party -> contract
 | Scale : rexp -> contract -> contract
 | Transl : nat -> contract -> contract
 | Both : contract -> contract -> contract
 | IfWithin : bexp -> nat -> contract -> contract -> contract.
