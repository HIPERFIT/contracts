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

Lemma mapM_rewrite {A B} (f g : A -> option B) l : forall_list (fun x => f x = g x) l -> mapM f l = mapM g l.
Proof.
  intros. induction l. reflexivity.
  inversion H. subst. simpl. rewrite IHl by auto. rewrite H2. reflexivity.
Qed.


Lemma mapM_monotone {A B} (f g : A -> option B) l : forall_list (fun x => f x ⊆ g x) l -> mapM f l ⊆ mapM g l.
Proof.
  intros. unfold "⊆" in *. simpl in *. induction l; intros.
  + auto.
  + simpl in *. unfold liftM2, bind, pure, compose in *. 

    remember (f a) as fa. remember (mapM f l) as fl. destruct fa; destruct fl; tryfalse.
    inversion H0. subst. inversion H. subst. erewrite H3 by eauto. erewrite IHl by eauto. reflexivity.

Qed.

Instance list_Partial {A} : Partial (list (option A)) := {
  lep t1 t2  := forall_zip lep t1 t2
  }.


Lemma sequence_monotone {A} (l l' : list (option A)) : l ⊆ l' -> sequence l ⊆ sequence l'.
Proof.
  intro H. induction H. simpl. auto.
  simpl. destruct (sequence xs). erewrite IHforall_zip by reflexivity. destruct x. erewrite H by reflexivity. auto.
  intros. simpl in *. tryfalse.
  intros. rewrite liftM2_none in H1. tryfalse.
Qed.


Lemma sequence_map_monotone {A B} (f g : A -> option B) l : forall_list (fun x => f x ⊆ g x) l ->
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

Lemma bind_some {A B} x (f : A -> option B) : (exists v, x = Some v) ->
                                                  (forall i, exists v, f i = Some v) -> exists v, x >>= f = Some v.
Proof.
  intros. destruct H. pose (H0 x0) as E; subst; simpl; auto.
Qed.


Lemma liftM_some {A B} (f : A -> B) x y : liftM f x = Some y -> exists x', x = Some x' /\ y = f x'.
Proof.
  destruct x; simpl; autounfold; intros; inversion H. eexists. split; reflexivity.
Qed.
                                 
      





Lemma map_rewrite {A B} (f g : A -> option B) l : forall_list (fun x => f x = g x) l -> map f l = map g l.
Proof.
  intros. induction l. reflexivity.
  inversion H. subst. simpl. rewrite IHl by auto. rewrite H2. reflexivity.
Qed.


Lemma forall_list_apply_dep {A} (P : Type) (p : P) (R : A -> P -> Prop) xs : 
  forall_list (fun x => forall (p:P), R x p) xs -> forall_list (fun x => R x p) xs.
Proof.
  intros F. induction F; auto.
Qed.




Lemma forall_list_zip T T' (P : T -> T' -> Prop) l l' f :
  forall_list (fun x => forall t, P x t -> P (f x) t) l -> forall_zip P l l' -> forall_zip P (map f l) l'.
Proof.
  generalize dependent l'. induction l; intros.
  + simpl. assumption.
  + simpl. inversion H. inversion H0. subst. constructor. auto. apply IHl; auto.
Qed.

Lemma forall_list_apply_dep' {A} (P Q : Type) (q : Q) (R : A -> P -> Q -> Prop) xs : 
  forall_list (fun x => forall (p:P) (q:Q), R x p q) xs -> forall_list (fun x => forall (p:P), R x p q) xs.
Proof.
  intros F. induction F; auto.
Qed.
