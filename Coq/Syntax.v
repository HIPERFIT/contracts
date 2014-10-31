Require Export Reals.
Require Export String.
Require Export ZArith.
Require Export List.

Definition currency := string.
Definition party := string.

Inductive Ty := RTy | BTy.

Inductive Var : list Ty -> Ty -> Set := 
| V1 {l} i : Var (i :: l) i
| VS {l i j} : Var l i -> Var (j :: l) i
.


Inductive Env (ty : Ty -> Type) : list Ty -> Type := 
  | EnvNil : Env ty nil
  | EnvCons {i l} : ty i -> Env ty l -> Env ty (i :: l).

Implicit Arguments EnvCons [[ty][i][l]].

Require Import JMeq.

Program Fixpoint lookupEnv  {ty l} {t : Ty} (v : Var l t) : Env ty l -> ty t :=
  match v in Var l t return Env ty l -> ty t with
    | V1 _ _ => fun e => match e with
                       | EnvCons _ _ r _ => r
                       | EnvNil => _
                     end
    | VS l' i j v' => fun e => match e with
                                 | EnvCons _ l' _ e' =>  @lookupEnv ty l' i v' e'
                                 | EnvNil => _
                        end
  end.




Definition TySem (t : Ty) : Set :=
  match t with
    | RTy => R
    | BTy => bool
  end.

Notation "'[|' t '|]'" := (TySem t) (at level 9).

Inductive ObsLabel : Ty -> Set :=
  | obsLabel ty : string -> ObsLabel ty.

Inductive BinOp : Ty -> Ty -> Type :=
| Add : BinOp RTy RTy
| Sub : BinOp RTy RTy
| Mult : BinOp RTy RTy
| And : BinOp BTy BTy
| Or : BinOp BTy BTy
| Less : BinOp RTy BTy
| Equal : BinOp RTy BTy.

Inductive UnOp : Ty -> Ty -> Type :=
| Not : UnOp BTy BTy
| Neg : UnOp RTy RTy.

Inductive exp' V t : Set :=
| Lit : [|t|] -> exp' V t
| BinOpE {s} : BinOp s t -> exp' V s -> exp' V s -> exp' V t
| UnOpE {s} : UnOp s t -> exp' V s -> exp' V t
| IfE : exp' V BTy -> exp' V t -> exp' V t -> exp' V t
| Obs :  ObsLabel t -> Z -> exp' V t
| VarE : Var V t -> exp' V t
| Acc : exp' (t :: V) t -> nat -> exp' V t -> exp' V t. 


Implicit Arguments Lit [[V][t]].
Implicit Arguments BinOpE [[V][t][s]].
Implicit Arguments UnOpE [[V][t][s]].
Implicit Arguments IfE [[V][t]].
Implicit Arguments Obs [[V][t]].
Implicit Arguments VarE [[V][t]].
Implicit Arguments Acc [[V][t]].


Definition exp t := exp' nil t .

Inductive contract : Set :=
 | Zero : contract
 | TransfOne : party -> party -> currency -> contract
 | Scale : exp RTy -> contract -> contract
 | Transl : nat -> contract -> contract
 | Both : contract -> contract -> contract
 | IfWithin : exp BTy -> nat -> contract -> contract -> contract.


Definition transl (l : nat) : contract -> contract := 
  match l with
    | O => (fun x => x)
    | _ => Transl l
  end.