Require Export Reals.
Require Export String.
Require Export ZArith.
Require Export List.

Definition currency := string.
Definition party := string.

Inductive Ty := REAL | BOOL.

Inductive Var : Set := V1 | VS (v:Var).

Inductive ObsLabel : Set := LabR (l:string) | LabB (l:string).

Inductive Val : Set := BVal : bool -> Val | RVal : R -> Val.

Inductive Op : Set := Add | Sub | Mult | Div | And | Or | Less | Leq | Equal |
                      Not | Neg |
                      BLit (b : bool) | RLit (r:R) |
                      Cond.



Inductive Exp : Set := OpE (op : Op) (args : list Exp)
                     | Obs (l:ObsLabel) (i: Z)
                     | VarE (v:Var)
                     | Acc (f : Exp) (d : nat) (e : Exp).

Inductive forall_list {A} (P : A -> Prop) : list A -> Prop :=
| forall_nil : forall_list P nil
| forall_cons {x xs} : P x -> forall_list P xs -> forall_list P (x :: xs).

Hint Constructors forall_list.

Definition Exp_ind'   : forall P : Exp -> Prop,
       (forall (op : Op) (args : list Exp), forall_list P args -> P (OpE op args)) ->
       (forall (l : ObsLabel) (i : Z), P (Obs l i)) ->
       (forall v : Var, P (VarE v)) ->
       (forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) ->
       forall e : Exp, P e := 
fun (P : Exp -> Prop)
  (f : forall (op : Op) (args : list Exp), forall_list P args -> P (OpE op args))
  (f0 : forall (l : ObsLabel) (i : Z), P (Obs l i))
  (f1 : forall v : Var, P (VarE v))
  (f2 : forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) =>
fix F (e : Exp) : P e :=
  match e as e0 return (P e0) with
  | OpE op args => let fix step es : forall_list P es := 
                       match es with
                           | nil => forall_nil P
                           | e' :: es' => forall_cons P (F e') (step es')
                       end
                   in  f op args (step args)
  | Obs l i => f0 l i
  | VarE v => f1 v
  | Acc f3 d e0 => f2 f3 (F f3) d e0 (F e0)
  end.


Inductive Contr : Set :=
 | Zero : Contr
 | Transfer : party -> party -> currency -> Contr
 | Scale : Exp -> Contr -> Contr
 | Translate : nat -> Contr -> Contr
 | Both : Contr -> Contr -> Contr
 | If : Exp -> nat -> Contr -> Contr -> Contr.


Definition translate (l : nat) : Contr -> Contr := 
  match l with
    | O => (fun x => x)
    | _ => Translate l
  end.

Reserved Notation "'|-V' e '∶' t" (at level 20).

Inductive TypeVal : Val -> Ty -> Prop := 
| type_bool b : |-V BVal b ∶ BOOL
| type_real b : |-V RVal b ∶ REAL
        where "'|-V' v '∶' t" := (TypeVal v t).

Reserved Notation "'|-Op' e '∶' t '=>' r" (at level 20).

Import ListNotations.

Inductive TypeOp : Op -> list Ty -> Ty -> Prop := 
| type_blit b : |-Op (BLit b) ∶ [] => BOOL
| type_rlit r : |-Op (RLit r) ∶ [] => REAL
| type_neg : |-Op Neg ∶ [REAL] => REAL
| type_not : |-Op Not ∶ [BOOL] => BOOL
| type_cond t : |-Op Cond ∶ [BOOL;t;t] => t
| type_add : |-Op Add ∶ [REAL;REAL] => REAL
| type_sub : |-Op Sub ∶ [REAL;REAL] => REAL
| type_mult : |-Op Mult ∶ [REAL;REAL] => REAL
| type_div : |-Op Div ∶ [REAL;REAL] => REAL
| type_and : |-Op And ∶ [BOOL;BOOL] => BOOL
| type_or : |-Op Or ∶ [BOOL;BOOL] => BOOL
| type_less : |-Op Less ∶ [REAL;REAL] => BOOL
| type_leq : |-Op Leq ∶ [REAL;REAL] => BOOL
| type_equal : |-Op Equal ∶ [REAL;REAL] => BOOL
        where "'|-Op' v '∶' t '=>' r" := (TypeOp v t r).

Reserved Notation "'|-O' e '∶' t" (at level 20).

Inductive TypeObs : ObsLabel -> Ty -> Prop := 
| type_obs_bool b : |-O LabB b ∶ BOOL
| type_obs_real b : |-O LabR b ∶ REAL
        where "'|-O' v '∶' t" := (TypeObs v t).

Reserved Notation "g '|-X' v '∶' t" (at level 20).

Definition TyEnv := list Ty.

Inductive TypeVar : TyEnv -> Var -> Ty -> Prop :=
| type_var_1 t g  : (t :: g) |-X V1 ∶ t
| type_var_S g v t : g |-X v ∶ t -> (t :: g) |-X VS v ∶ t
        where "g '|-X' v '∶' t" := (TypeVar g v t).


Inductive forall_zip {A B} (R : A -> B -> Prop) : list A -> list B -> Prop :=
| forall_zip_nil : forall_zip R [] []
| forall_zip_cons {x y xs ys} : R x y -> forall_zip R xs ys -> forall_zip R (x::xs) (y::ys).

Hint Constructors forall_zip.


Lemma forall_zip_impl {A B} (R1 R2 : A -> B -> Prop) xs ys : 
  (forall x y, R1 x y -> R2 x y) -> forall_zip R1 xs ys -> forall_zip R2 xs ys.
Proof.
  intros f l. induction l; auto. 
Qed.


Lemma forall_zip_apply {A B} (R : A -> B -> Prop) (P : Prop) xs ys : 
  forall_zip (fun x y => P -> R x y) xs ys -> P -> forall_zip R xs ys.
Proof.
  intros F p. induction F; auto.
Qed.

Lemma forall_zip_apply_dep {A B} (P : Type) (p : P) (R : A -> B -> P -> Prop) xs ys : 
  forall_zip (fun x y => forall (p:P), R x y p) xs ys -> forall_zip (fun x y => R x y p) xs ys.
Proof.
  intros F. induction F; auto.
Qed.


Lemma forall_zip_and {A B} (R1 R2 : A -> B -> Prop) xs ys : 
  forall_zip R1 xs ys -> forall_zip R2 xs ys -> forall_zip (fun x y => R1 x y /\ R2 x y) xs ys.
Proof.
  intros A1 A2. induction A1; inversion A2; auto.
Qed.


Reserved Notation "g '|-E' e '∶' t" (at level 20).

Inductive TypeExp : TyEnv -> Exp -> Ty -> Prop :=
| type_op g op es ts t : |-Op op ∶ ts => t -> forall_zip (TypeExp g) es ts -> g |-E OpE op es ∶ t
| type_obs t g o z : |-O o ∶ t -> g |-E Obs o z ∶ t
| type_var t g v : g |-X v ∶ t -> g |-E VarE v ∶ t
| type_acc n t g e1 e2 : (t :: g) |-E e1 ∶ t -> g |-E e2 ∶ t -> g |-E Acc e1 n e2 ∶ t
        where "g '|-E' e '∶' t" := (TypeExp g e t).

(* The induction principle generated by Coq is not strong enough. We
need to roll our own. *)

Definition TypeExp_ind' : forall P : TyEnv -> Exp -> Ty -> Prop,
       (forall (g : TyEnv) (op : Op) (es : list Exp) (ts : list Ty) (t : Ty),
        |-Op op ∶ ts => t ->
        forall_zip (TypeExp g) es ts -> forall_zip (P g) es ts -> P g (OpE op es) t) ->
       (forall (t : Ty) (g : TyEnv) (o : ObsLabel) (z : Z),
        |-O o ∶ t -> P g (Obs o z) t) ->
       (forall (t : Ty) (g : TyEnv) (v : Var), g |-X v ∶ t -> P g (VarE v) t) ->
       (forall (n : nat) (t : Ty) (g : list Ty) (e1 e2 : Exp),
        (t :: g) |-E e1 ∶ t ->
        P (t :: g) e1 t -> g |-E e2 ∶ t -> P g e2 t -> P g (Acc e1 n e2) t) ->
       forall (t : TyEnv) (e : Exp) (t0 : Ty), t |-E e ∶ t0 -> P t e t0 :=
  fun (P : TyEnv -> Exp -> Ty -> Prop)
  (f : forall (g : TyEnv) (op : Op) (es : list Exp) (ts : list Ty) (t : Ty),
       |-Op op ∶ ts => t -> forall_zip (TypeExp g) es ts -> forall_zip (P g) es ts -> P g (OpE op es) t)
  (f0 : forall (t : Ty) (g : TyEnv) (o : ObsLabel) (z : Z),
        |-O o ∶ t -> P g (Obs o z) t)
  (f1 : forall (t : Ty) (g : TyEnv) (v : Var), g |-X v ∶ t -> P g (VarE v) t)
  (f2 : forall (n : nat) (t : Ty) (g : list Ty) (e1 e2 : Exp),
        (t :: g) |-E e1 ∶ t ->
        P (t :: g) e1 t -> g |-E e2 ∶ t -> P g e2 t -> P g (Acc e1 n e2) t) =>
fix F (t : TyEnv) (e : Exp) (t0 : Ty) (t1 : t |-E e ∶ t0) {struct t1} :
  P t e t0 :=
  match t1 in (t2 |-E e0 ∶ t3) return (P t2 e0 t3) with
  | type_op g op es ts t2 t3 f3 =>
    let fix step es ts (args: forall_zip (TypeExp g) es ts) :=
        match args with
          | forall_zip_nil => forall_zip_nil (P g)
          | forall_zip_cons e t0 es ts ty tys => forall_zip_cons (P g) (F g e t0 ty) (step es ts tys)
        end
          in f g op es ts t2 t3 f3 (step es ts f3)
  | type_obs t2 g o z t3 => f0 t2 g o z t3
  | type_var t2 g v t3 => f1 t2 g v t3
  | type_acc n t2 g e1 e2 t3 t4 =>
      f2 n t2 g e1 e2 t3 (F (t2 :: g) e1 t2 t3) t4 (F g e2 t2 t4)
  end.


Reserved Notation "'|-C' e" (at level 20).

Inductive TypeContr : Contr -> Prop :=
| type_zero : |-C Zero
| type_transfer p1 p2 c : |-C Transfer p1 p2 c
| type_scale e c : nil |-E e ∶ REAL -> |-C c -> |-C Scale e c
| type_translate d c : |-C c -> |-C Translate d c
| type_both c1 c2 : |-C c1 ->  |-C c2 -> |-C Both c1 c2
| type_if e d c1 c2 : nil |-E e ∶ BOOL -> |-C c1 ->  |-C c2 -> |-C If e d c1 c2
  where "'|-C' c" := (TypeContr c).


Hint Constructors TypeVal TypeOp TypeObs TypeExp TypeVar TypeContr.