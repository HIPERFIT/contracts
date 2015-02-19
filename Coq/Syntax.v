(********** Syntax of the contract language **********)

Require Export Reals.
Require Export Utils.
Require Export Equalities.


(* The types of assets and parties are kept abstract. They should at
least be decicable, though. *)

Parameter Asset : Set.
Parameter Party : Set.

Module Asset.
  Parameter eqb : Asset -> Asset -> bool.
  Axiom eqb_eq : forall x y, eqb x y = true <-> x = y.

  Lemma eqb_refl p:  eqb p p = true.
  Proof.
    assert (p = p) as E by reflexivity. rewrite <- eqb_eq in E. auto.
  Qed.
    
End Asset.

Module Party.
  Parameter eqb : Party -> Party -> bool.
  Axiom eqb_eq : forall x y, eqb x y = true <-> x = y.
  Lemma eqb_refl p:  eqb p p = true.
  Proof.
    assert (p = p) as E by reflexivity. rewrite <- eqb_eq in E. auto.
  Qed.
    
End Party.

(* We also keep the types for Boolean and real observable labels
abstract. *)

Parameter BoolObs : Set.
Parameter RealObs : Set.


(* The type of variables. *)

Inductive Var : Set := V1 | VS (v:Var).

(* The type of labels that describe external observables. *)

Inductive ObsLabel : Set := LabR (l:RealObs) | LabB (l:BoolObs).

(* The type of operations that may be used in expressions. *)

Inductive Op : Set := Add | Sub | Mult | Div | And | Or | Less | Leq | Equal |
                      Not | Neg |
                      BLit (b : bool) | RLit (r:R) |
                      Cond.

(* The type of expressions. *)

Inductive Exp : Set := OpE (op : Op) (args : list Exp)
                     | Obs (l:ObsLabel) (i: Z)
                     | VarE (v:Var)
                     | Acc (f : Exp) (d : nat) (e : Exp).


(* We need to define a custom induction principle for expressions. The
automatically generated induction principle is too weak. *)

Definition Exp_ind'   : forall P : Exp -> Prop,
       (forall (op : Op) (args : list Exp), all P args -> P (OpE op args)) ->
       (forall (l : ObsLabel) (i : Z), P (Obs l i)) ->
       (forall v : Var, P (VarE v)) ->
       (forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) ->
       forall e : Exp, P e := 
fun (P : Exp -> Prop)
  (f : forall (op : Op) (args : list Exp), all P args -> P (OpE op args))
  (f0 : forall (l : ObsLabel) (i : Z), P (Obs l i))
  (f1 : forall v : Var, P (VarE v))
  (f2 : forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) =>
fix F (e : Exp) : P e :=
  match e as e0 return (P e0) with
  | OpE op args => let fix step es : all P es := 
                       match es with
                           | nil => forall_nil P
                           | e' :: es' => forall_cons P (F e') (step es')
                       end
                   in  f op args (step args)
  | Obs l i => f0 l i
  | VarE v => f1 v
  | Acc f3 d e0 => f2 f3 (F f3) d e0 (F e0)
  end.

(* This type defines the syntax of the contract language *)

Inductive Contr : Type :=
 | Zero : Contr
 | VarC : Var -> Contr
 | Let : Exp -> Contr -> Contr
 | Transfer : Party -> Party -> Asset -> Contr
 | Scale : Exp -> Contr -> Contr
 | Translate : nat -> Contr -> Contr
 | Both : Contr -> Contr -> Contr
 | If : Exp -> nat -> Contr -> Contr -> Contr
 | Iter (f : Contr) (d : nat) (e : Contr).
