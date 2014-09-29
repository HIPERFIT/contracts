Require Export Denotational.
Require Export Advance.

Open Scope Z.

(********** Causality **********)

(* [obs_until d r1 r2] iff [r1] [r2] coincide at [d] and earlier. *)

Definition inp_until {A} (d : Z) (r1 r2 : inp A) : Prop :=
  forall z, Z.le z d -> r1 z = r2 z.

Definition ext_until (d : Z) (e1 e2 : ext) : Prop :=
  inp_until d (fst e1) (fst e2) /\ inp_until d (snd e1) (snd e2).


(* Semantic causality *)

Definition causal (c : contract) : Prop :=
  forall d r1 r2,  ext_until (Z.of_nat d) r1 r2 -> (C[|c|]r1) d = (C[|c|]r2) d.


Lemma inp_until_adv {A} d t (r1 r2 : inp A): 
  inp_until d (adv_inp t r1) (adv_inp t r2) <-> inp_until (t + d) r1 r2.
Proof.
  unfold inp_until,adv_inp. split; intros.
  - pose (H (z - t)%Z). 
    assert (t + (z - t) = z)%Z as E. omega. rewrite E in *. 
    apply e. omega.
  - apply H. omega.

Qed.

Lemma ext_until_adv d t e1 e2: 
    ext_until d (adv_ext t e1) (adv_ext t e2) <-> ext_until (t + d) e1 e2.
Proof.
  unfold ext_until. repeat rewrite adv_ext_obs. repeat rewrite adv_ext_ch.
  repeat rewrite inp_until_adv. reflexivity.
Qed.

Lemma ext_until_adv_1 d r1 r2 : (1 <= d -> ext_until d r1 r2 ->
                        ext_until (d - 1) (adv_ext 1 r1) (adv_ext 1 r2))%Z.
Proof.
  intros.
  assert (1 + (d - 1) = d)%Z by omega.
  rewrite ext_until_adv. rewrite H1. assumption.
Qed.

Lemma inp_until_le {A} d1 d2 (r1 r2 : inp A) : inp_until d1 r1 r2 ->  d2 <= d1 -> inp_until d2 r1 r2.
Proof. 
  unfold inp_until. intros. apply H. omega.
Qed.
