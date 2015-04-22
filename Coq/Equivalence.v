Require Export Denotational.
Require Import TranslateExp.
Require Import FunctionalExtensionality.
Require Import Tactics.

Require Import DenotationalTyped.

(********** Equivalence of contracts **********)

(* Full equivalence. *)

Definition equiv (g : TyEnv) (c1 c2 : Contr) : Prop
  := g |-C c1 /\ g |-C c2 /\ 
    (forall (env : Env) (ext : ExtEnv), 
      TypeExt ext -> TypeEnv g env -> C[|c1|]env ext = C[|c2|]env ext).
Notation "c1 '≡[' g ']' c2" := (equiv g c1 c2) (at level 50).


Lemma equiv_typed g c1 c2 : g |-C c1 -> g |-C c2 -> (forall t1 t2 env ext, TypeExt ext -> TypeEnv g env -> C[|c1|]env ext = Some t1 -> C[|c2|]env ext = Some t2 -> t1 = t2) -> c1 ≡[g] c2.
Proof. 
  intros T1 T2 E. unfold equiv. repeat split;auto. intros. 
  eapply Csem_typed_total in T1;eauto. destruct T1 as [t1 T1].
  eapply Csem_typed_total in T2;eauto. destruct T2 as [t2 T2].
  rewrite T1. rewrite T2. f_equal. eauto.
Qed.

Lemma delay_trace_at d t : delay_trace d t d = t O.
Proof.
  unfold delay_trace. 
  assert (leb d d = true) as E by (apply leb_correct; auto).
  rewrite E. rewrite minus_diag. reflexivity.
Qed.

Hint Resolve translateExp_type.

Theorem transl_ifwithin g e d t c1 c2 : g |-C c1 -> g |-C c2 -> g |-E e ∶ BOOL ->
  If (translateExp (Z.of_nat d) e) t (Translate d c1) (Translate d c2) ≡[g]
  Translate d (If e t c1 c2).
Proof.
  unfold equiv. intros. repeat split; eauto. intros env ext R V.
  generalize dependent ext. induction t; intros. 
  - eapply Esem_typed_total with (ext:=(adv_ext (Z.of_nat d) ext)) in H1;eauto.
    decompose [ex and] H1. simpl in *. rewrite translateExp_ext, H3 in *. 
    destruct x; try destruct b; reflexivity.
  - pose H1 as H1'. eapply Esem_typed_total with (ext:=(adv_ext (Z.of_nat d) ext)) in H1';eauto.
    decompose [ex and] H1'. simpl in *. rewrite translateExp_ext, H3. destruct x; try reflexivity. destruct b. reflexivity.
    rewrite IHt;eauto. rewrite adv_ext_swap. repeat rewrite liftM_liftM. apply liftM_ext. 
    intros. unfold compose. apply delay_trace_swap. 
Qed.