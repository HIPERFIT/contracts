Require Export List.
Require Export Basics.
Require Export String.
Require Import Tactics.

Infix "∘" := compose (at level 40, left associativity).

Import ListNotations.


Inductive forall_list {A} (P : A -> Prop) : list A -> Prop :=
| forall_nil : forall_list P nil
| forall_cons {x xs} : P x -> forall_list P xs -> forall_list P (x :: xs).

Hint Constructors forall_list.

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


Definition eq_str (s1 s2 : string) : bool :=
  match string_dec s1 s2 with
      | left  _ => true
      | right _ => false
  end.

Lemma eq_str_iff s1 s2 : eq_str s1 s2 = true <-> s1 = s2.
Proof.
  split.
  + unfold eq_str. destruct (string_dec s1 s2). auto. intro H. inversion H.
  + intro H. rewrite H. unfold eq_str. destruct (string_dec s2 s2). reflexivity. 
    tryfalse.
Qed.
  

Class Partial t := {
  lep : t -> t -> Prop
                  }. 

Infix "⊆" := lep (at level 40).

Instance none_Partial A : Partial (option A) := {
  lep t1 t2  := forall z , t1 = Some z -> t2 = Some z
  }.
