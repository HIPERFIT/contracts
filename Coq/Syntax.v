Require Export Reals.
Require Export String.
Require Export ZArith.
Require Export List.

Definition observable := string.
Definition currency := string.
Definition party := string.
Definition choice := string.

Definition eq_str (s1 s2 : string) : bool :=
  match string_dec s1 s2 with
      | left  _ => true
      | right _ => false
  end.

Inductive Var {I} : list I -> I -> Type := 
| V1 {l} i : Var (i :: l) i
| VS {l i j} : Var l i -> Var (j :: l) i
.


Inductive Env {I} (ty : I -> Type) : list I -> Type := 
  | EnvNil : Env ty nil
  | EnvCons {i l} : ty i -> Env ty l -> Env ty (i :: l).


Implicit Arguments EnvCons [[I][ty][i][l]].


Require Import JMeq.

Program Fixpoint lookupEnv  {I ty l} {t : I} (v : Var l t) : Env ty l -> ty t :=
  match v in Var l t return Env ty l -> ty t with
    | V1 _ _ => fun e => match e with
                       | EnvCons _ _ r _ => r
                       | EnvNil => _
                     end
    | VS l' i j v' => fun e => match e with
                                 | EnvCons _ l' _ e' =>  @lookupEnv I ty l' i v' e'
                                 | EnvNil => _
                        end
  end.



Inductive Ty := RTy | BTy.

Definition TySem (t : Ty) : Type :=
  match t with
    | RTy => R
    | BTy => bool
  end.

Notation "'[|' t '|]'" := (TySem t) (at level 9).

Inductive exp' : list Ty -> Ty -> Type :=
| Lit {t V} : [|t|] -> exp' V t
| BinOpE {t s V} : ([|s|] -> [|s|] -> [|t|]) -> exp' V s -> exp' V s -> exp' V t
| UnOpE {t s V} : ([|s|] -> [|t|]) -> exp' V s -> exp' V t
| IfE {t V} : exp' V BTy -> exp' V t -> exp' V t -> exp' V t
| Obs t {V} :  observable -> Z -> exp' V t
| VarE {V t} : Var V t -> exp' V t
| Acc {V t} : exp' (t :: V) t -> nat -> exp' V t -> exp' V t. 

Definition exp t := exp' nil t .

Inductive contract : Type :=
 | Zero : contract
 | TransfOne : currency -> party -> party -> contract
 | Scale : exp RTy -> contract -> contract
 | Transl : nat -> contract -> contract
 | Both : contract -> contract -> contract
 | IfWithin : exp BTy -> nat -> contract -> contract -> contract.


Definition transl (l : nat) : contract -> contract := 
  match l with
    | O => (fun x => x)
    | _ => Transl l
  end.