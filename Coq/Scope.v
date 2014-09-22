Require Import FunctionalExtensionality.

Inductive Vars A V : Type :=
| Old : A -> Vars A V
| New : V -> Vars A V.

Implicit Arguments Old [[A][V]].
Implicit Arguments New [[A][V]].


Infix ":>" := (@Vars) (at level 60, right associativity).

Definition Succ (a : Type) : Type := a :> unit.

Inductive ZeroT : Type := .

Definition zero (A : Type) (z : ZeroT) : A :=
  match z with
  end.

Lemma zero_unique {A} (f : ZeroT -> A) : f = zero A.
Proof.
  apply functional_extensionality. destruct x.
Qed.

Definition Scope (m : Type -> Type)  (A : Type) : Type := m (Succ A).

Set Implicit Arguments.


Inductive Env A : Type -> Type :=
  | Empty : forall I, (I -> A) -> Env A I
  | Extend : forall I, A -> Env A I -> Env A (Succ I).


(* partial environment *)

Inductive PEnv A : Type -> Type -> Type :=
  | PEmpty : forall I, (I -> A) -> PEnv A I I
  | PExtend : forall I J, A -> PEnv A I J -> PEnv A (Succ I) J
  | PSkip : forall I J, PEnv A I J -> PEnv A (Succ I) (Succ J).

Unset Implicit Arguments.

Fixpoint emap {I A B} (f : A -> B) (e : Env A I) : Env B I :=
  match e with
    | Empty _ f' => Empty (fun x => f (f' x))
    | Extend _ b r  => Extend (f b) (emap f r)
  end.

Fixpoint lookupEnv {A I} (e : Env A I) : I -> A :=
  match e with
      | Empty _ f => f
      | Extend _ b r => fun v => match v with
                     | Old v' => lookupEnv r v'
                     | New tt => b
                   end
  end.

Definition shiftIndex {A I} (x : A + I) : A + (Succ I) :=
  match x with
    | inl a => inl a
    | inr i => inr (Old i)
  end.

Fixpoint lookupPEnv {A I J} (e : PEnv A I J) : I -> A + J :=
  match e with
      | PEmpty _ f => fun i => inl (f i)
      | PExtend _ _ b r => fun v => match v with
                     | Old v' => lookupPEnv r v'
                     | New tt => inl b
                   end
      | PSkip _ _ r => fun v => match v with
                     | Old v' => shiftIndex (lookupPEnv r v')
                     | New tt => inr (New tt)
                   end 
  end.


Lemma emap_lookup {I A B} {e : Env A I} {i : I} {f : A -> B} : lookupEnv (emap f e) i = f (lookupEnv e i).
Proof.
  induction e.
  reflexivity.
  simpl. destruct i. auto. destruct u. reflexivity.
Qed.