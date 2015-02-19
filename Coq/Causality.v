(********** Causality **********)

(* This module defines the semantic notion of causality and gives some
lemmas helpful for proving causality. *)


Require Export Denotational.
Require Export TranslateExp.

Open Scope Z.


(** [ext_until d r1 r2] iff [r1] and [r2] coincide at [d] and earlier. *)

Definition ext_until {A} (d : Z) (r1 r2 : ExtEnv' A) : Prop :=
  forall l z, Z.le z d -> r1 l z = r2 l z.

(* Semantic causality of (closed) contracts *)

Definition causal (c : Contr) : Prop :=
  forall d r1 r2 t1 t2,  ext_until (Z.of_nat d) r1 r2 -> C[|c|] nil nil r1 = Some t1 -> C[|c|]nil nil r2 = Some t2
                        -> t1 d = t2 d.


Lemma ext_until_adv {A} d t (r1 r2 : ExtEnv' A): 
  ext_until d (adv_ext t r1) (adv_ext t r2) <-> ext_until (t + d) r1 r2.
Proof.
  unfold ext_until,adv_ext. split; intros.
  - pose (H l (z - t)%Z). 
    assert (t + (z - t) = z)%Z as E. omega. rewrite E in *. 
    apply e. omega.
  - apply H. omega.
Qed.


Lemma ext_until_adv_1 {A} d (r1 r2 : ExtEnv' A) : (1 <= d -> ext_until d r1 r2 ->
                        ext_until (d - 1) (adv_ext 1 r1) (adv_ext 1 r2))%Z.
Proof.
  intros.
  assert (1 + (d - 1) = d)%Z by omega.
  rewrite ext_until_adv. rewrite H1. assumption.
Qed.

Lemma ext_until_le {A} d1 d2 (r1 r2 : ExtEnv' A) : ext_until d1 r1 r2 ->  d2 <= d1 -> ext_until d2 r1 r2.
Proof. 
  unfold ext_until. intros. apply H. omega.
Qed.