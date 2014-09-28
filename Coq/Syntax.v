Require Export String.
Require Export ZArith.
Require Export Scope.

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

Inductive rexp' : Type -> Type :=
| RLit V : Z -> rexp' V
| RBin V : BinOp -> rexp' V -> rexp' V -> rexp' V
| RNeg  V : rexp' V -> rexp' V
| Obs V : observable -> Z -> rexp' V
| RVar V : V -> rexp' V
| RAcc V : Scope rexp' V -> nat -> rexp' V -> rexp' V. 

Implicit Arguments RLit [[V]].
Implicit Arguments RBin [[V]].
Implicit Arguments RNeg [[V]].
Implicit Arguments Obs [[V]].
Implicit Arguments RVar [[V]].
Implicit Arguments RAcc [[V]].

Definition rexp := rexp' ZeroT.

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


Definition transl (l : nat) : contract -> contract := 
  match l with
    | O => id
    | _ => Transl l
  end.