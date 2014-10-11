Require Export Reals.
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
| Div : BinOp
| Min : BinOp
| Max : BinOp.

Inductive Cmp : Set :=
| EQ : Cmp
| LT : Cmp
| LTE : Cmp.

Inductive BoolOp : Set :=
| And : BoolOp
| Or : BoolOp.

Inductive rexp' : Type -> Type :=
| RLit V : R -> rexp' V
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

Inductive bexp' : Type -> Type :=
| BLit V: bool -> bexp' V
| BChoice V  : choice -> Z -> bexp' V
| RCmp V : Cmp -> rexp -> rexp -> bexp' V
| BNot V : bexp' V -> bexp' V
| BOp V : BoolOp -> bexp' V -> bexp' V -> bexp' V
| BVar V : V -> bexp' V
| BAcc V : Scope bexp' V -> nat -> bexp' V -> bexp' V. 


Implicit Arguments BLit [[V]].
Implicit Arguments BChoice [[V]].
Implicit Arguments RCmp [[V]].
Implicit Arguments BNot [[V]].
Implicit Arguments BOp [[V]].
Implicit Arguments BVar [[V]].
Implicit Arguments BAcc [[V]].

Definition bexp := bexp' ZeroT.


Inductive contract : Type :=
 | Zero : contract
 | TransfOne : currency -> party -> party -> contract
 | Scale : rexp -> contract -> contract
 | Transl : nat -> contract -> contract
 | Both : contract -> contract -> contract
 | IfWithin : bexp -> nat -> contract -> contract -> contract.


Definition transl (l : nat) : contract -> contract := 
  match l with
    | O => (fun x => x)
    | _ => Transl l
  end.