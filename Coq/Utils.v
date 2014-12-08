Require Export List.
Require Export Basics.
Require Import Tactics.

Infix "∘" := compose (at level 40, left associativity).

Import ListNotations.


Inductive all {A} (P : A -> Prop) : list A -> Prop :=
| forall_nil : all P nil
| forall_cons {x xs} : P x -> all P xs -> all P (x :: xs).

Hint Constructors all.

Inductive all2 {A B} (R : A -> B -> Prop) : list A -> list B -> Prop :=
| all2_nil : all2 R [] []
| all2_cons {x y xs ys} : R x y -> all2 R xs ys -> all2 R (x::xs) (y::ys).

Hint Constructors all2.

Inductive all3 {A B C} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| all3_nil : all3 R [] [] []
| all3_cons {x y z xs ys zs} : R x y z -> all3 R xs ys zs -> all3 R (x::xs) (y::ys) (z::zs).

Hint Constructors all3.


Lemma all2_impl {A B} (R1 R2 : A -> B -> Prop) xs ys : 
  (forall x y, R1 x y -> R2 x y) -> all2 R1 xs ys -> all2 R2 xs ys.
Proof.
  intros f l. induction l; auto. 
Qed.


Lemma all2_apply {A B} (P : Type) (p : P) (R : A -> B -> P -> Prop) xs ys : 
  all2 (fun x y => forall (p:P), R x y p) xs ys -> all2 (fun x y => R x y p) xs ys.
Proof.
  intros F. induction F; auto.
Qed.


Lemma all2_and {A B} (R1 R2 : A -> B -> Prop) xs ys : 
  all2 R1 xs ys -> all2 R2 xs ys -> all2 (fun x y => R1 x y /\ R2 x y) xs ys.
Proof.
  intros A1 A2. induction A1; inversion A2; auto.
Qed.


Lemma all2_map {A} (P : A -> A -> Prop) (f g : A -> A) xs ys :
  (forall x y, P x y -> P (f x) (g y)) ->
  all2 P xs ys -> all2 P (map f xs) (map g ys).
Proof.
  intros I Z. induction Z;constructor; auto.
Qed.


  

Class Partial t := {
  lep : t -> t -> Prop
                  }. 

Infix "⊆" := lep (at level 60).

Instance none_Partial A : Partial (option A) := {
  lep t1 t2  := forall z , t1 = Some z -> t2 = Some z
  }.


(* Lifts binary functions into [option] types. *)


Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
    | None => None
    | Some x' => f x'
  end.

Definition pure {A} : A -> option A := fun x => Some x.

Hint Unfold pure compose.

Infix ">>=" := bind (at level 54, left associativity).

Definition liftM {A B} (f : A -> B) (x : option A) : option B :=
 x >>= (pure ∘ f).

Definition liftM2 {A B C} (f : A -> B -> C) (x : option A) (y : option B) : option C :=
 x >>= (fun x' => y >>= pure ∘ f x').

Fixpoint mapM {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
    | nil => Some nil
    | x :: xs => liftM2 (fun x' xs' => x' :: xs') (f x) (mapM f xs)
  end.


Lemma liftM2_none {A B C :Type} (f:A->B->C) o : liftM2 f o None = None.
Proof.
  destruct o; reflexivity.
Qed.

Fixpoint sequence {A} (l : list (option A)) : option (list A) :=
  match l with
    | nil => Some nil
    | x :: xs => liftM2 (fun x' xs' => x' :: xs') x (sequence xs)
  end.


Lemma sequence_mapM {A} (l : list (option A)) :  sequence l = mapM id l.
Proof.
  induction l. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma sequence_map {A B} (f : A -> option B) l : sequence (map f l) = mapM f l.
Proof.
  induction l. reflexivity. simpl. rewrite <- IHl. reflexivity.
Qed.


Lemma mapM_map {A B C} (f : B -> option C) (g : A -> B) l : mapM f (map g l) = mapM (f ∘ g) l.
Proof.
  induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma mapM_rewrite {A B} (f g : A -> option B) l : all (fun x => f x = g x) l -> mapM f l = mapM g l.
Proof.
  intros. induction l. reflexivity.
  inversion H. subst. simpl. rewrite IHl by auto. rewrite H2. reflexivity.
Qed.


Lemma mapM_monotone {A B} (f g : A -> option B) l : all (fun x => f x ⊆ g x) l -> mapM f l ⊆ mapM g l.
Proof.
  intros. unfold "⊆" in *. simpl in *. induction l; intros.
  + auto.
  + simpl in *. unfold liftM2, bind, pure, compose in *. 

    remember (f a) as fa. remember (mapM f l) as fl. destruct fa; destruct fl; tryfalse.
    inversion H0. subst. inversion H. subst. erewrite H3 by eauto. erewrite IHl by eauto. reflexivity.

Qed.

Instance list_Partial {A} : Partial (list (option A)) := {
  lep t1 t2  := all2 lep t1 t2
  }.


Lemma sequence_monotone {A} (l l' : list (option A)) : l ⊆ l' -> sequence l ⊆ sequence l'.
Proof.
  intro H. induction H. simpl. auto.
  simpl. destruct (sequence xs). erewrite IHall2 by reflexivity. destruct x. erewrite H by reflexivity. auto.
  intros. simpl in *. tryfalse.
  intros. rewrite liftM2_none in H1. tryfalse.
Qed.


Lemma sequence_map_monotone {A B} (f g : A -> option B) l : all (fun x => f x ⊆ g x) l ->
                                                            sequence (map f l) ⊆ sequence (map g l).
Proof.
  repeat rewrite sequence_map. apply mapM_monotone.
Qed.

Lemma bind_monotone' {A B} x y (f : A -> option B) : x ⊆ y -> x >>= f ⊆ y >>= f.
Proof.
  destruct x.
  simpl. intros. erewrite H by eauto. simpl. eauto.
  simpl. intros. tryfalse.
Qed.


Lemma bind_monotone {A B} x y (f : A -> option B) v : x ⊆ y -> x >>= f = Some v ->  y >>= f = Some v.
Proof.
  destruct x.
  simpl. intros. erewrite H by eauto. simpl. eauto.
  simpl. intros. tryfalse.
Qed.

Lemma bind_monotone2 {A B} x y (f g : A -> option B) v : x ⊆ y -> (forall x, f x ⊆ g x)
                                                         -> x >>= f = Some v ->  y >>= g = Some v.
Proof.
  destruct x.
  simpl. intros. erewrite H by eauto. simpl. eauto.
  simpl. intros. tryfalse.
Qed.

Lemma bind_equals {A B} x y (f g : A -> option B) : x = y -> (forall i, f i = g i) -> x >>= f = y >>= g.
Proof.
  intros. destruct x; subst; simpl; auto.
Qed.

Lemma bind_some {A B} x v (f : A -> option B) : x >>= f = Some v -> exists x', x = Some x' /\ f x' = Some v.
Proof.
  destruct x; simpl; autounfold; intros; inversion H. eexists. split; reflexivity.
Qed.


Lemma liftM_some {A B} (f : A -> B) x y : liftM f x = Some y -> exists x', x = Some x' /\ y = f x'.
Proof.
  destruct x; simpl; autounfold; intros; inversion H. eexists. split; reflexivity.
Qed.

Lemma liftM2_some {A1 A2 B} (f : A1 -> A2 -> B) x1 x2 y : liftM2 f x1 x2 = Some y
                                           -> exists x1' x2', x1 = Some x1' /\ x2 = Some x2' /\ y = f x1' x2'.
Proof.
  destruct x1; destruct x2; simpl; autounfold; intros; inversion H. do 2 eexists. do 2 split; reflexivity.
Qed.


Ltac option_inv T := idtac;let H := fresh "H" in pose T as H; match goal with
                      | [T : liftM _ _ = Some _ |- _] => apply liftM_some in H
                      | [T : liftM2 _ _ _ = Some _ |- _] => apply liftM2_some in H
                      | [T : _ >>= _ = Some _ |- _] => apply bind_some in H
                     end; decompose [ex and] H; clear H.

Ltac option_inv' T := option_inv T; subst; clear T.

Ltac option_inv_auto := repeat (idtac; match goal with
                      | [T : liftM _ _ = Some _ |- _] => apply liftM_some in T; decompose [ex and] T; clear T
                      | [T : liftM2 _ _ _ = Some _ |- _] => apply liftM2_some in T; decompose [ex and] T; clear T
                      | [T : _ >>= _ = Some _ |- _] => apply bind_some in T; decompose [ex and] T; clear T
                     end;subst).


Lemma map_rewrite {A B} (f g : A -> option B) l : all (fun x => f x = g x) l -> map f l = map g l.
Proof.
  intros. induction l. reflexivity.
  inversion H. subst. simpl. rewrite IHl by auto. rewrite H2. reflexivity.
Qed.


Lemma all_apply {A} (P : Type) (p : P) (R : A -> P -> Prop) xs : 
  all (fun x => forall (p:P), R x p) xs -> all (fun x => R x p) xs.
Proof.
  intros F. induction F; auto.
Qed.


Lemma all_zip T T' (P : T -> T' -> Prop) l l' f :
  all (fun x => forall t, P x t -> P (f x) t) l -> all2 P l l' -> all2 P (map f l) l'.
Proof.
  generalize dependent l'. induction l; intros.
  + simpl. assumption.
  + simpl. inversion H. inversion H0. subst. constructor. auto. apply IHl; auto.
Qed.

Lemma all_apply' {A} (P Q : Type) (q : Q) (R : A -> P -> Q -> Prop) xs : 
  all (fun x => forall (p:P) (q:Q), R x p q) xs -> all (fun x => forall (p:P), R x p q) xs.
Proof.
  intros F. induction F; auto.
Qed.

Lemma liftM_liftM A B C (f : B -> C) (g : A -> B) x : liftM f (liftM g x) = liftM (f ∘ g) x.
Proof.
  unfold liftM, bind. destruct x. unfold compose, pure. reflexivity. reflexivity.
Qed.
Lemma liftM_extensionality A B (f g : A -> B) x : (forall x, f x = g x) -> liftM f x = liftM g x.
Proof.
  intros. unfold liftM, bind, pure, compose. destruct x. rewrite H. reflexivity. reflexivity.
Qed.


Lemma all_mp {A} (P Q : A -> Prop) xs : all P xs -> all (fun x => P x -> Q x) xs -> all Q xs.
Proof.
  intro All. induction All;constructor;inversion H0; auto.
Qed.
