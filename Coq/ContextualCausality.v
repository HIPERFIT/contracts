Require Import Causality.
Require Import Advance.
Require Import FunctionalExtensionality.
Require Import Tactics.
Require Import Utils.

(* Contextual syntactic causality. This syntactic notion of causality
is more permissive than plain syntactic causality. However, the
causality property that follows from this syntactic notion of
causality is slightly weaker. *)

Open Scope Z.


(* Definition of the inference rules for contextual causality. *)

Definition TimeEnv := list Z.


Inductive CausalV : TimeEnv -> Z -> Var -> Prop :=
| causal_V1 t t' g  : t <= t' -> CausalV (t :: g) t' V1
| causal_VS g v t t' : CausalV g t v -> CausalV (t' :: g) t (VS v).


Inductive CausalE : TimeEnv -> Z -> Exp -> Prop:= 
 | causal_op t ts op args : forall_list (CausalE ts t) args -> CausalE ts t (OpE op args)
 | causal_obs l t' t ts : t' <= t -> CausalE ts t (Obs l t')
 | causal_var t ts v : CausalV ts t v -> CausalE ts t (VarE v)
 | causal_acc t t' ts e1 e2 n : CausalE ts (t + Z.of_nat n) e2 -> CausalE (t' :: ts) t e1
                                -> CausalE ts t (Acc e1 n e2)
  .



Inductive CausalC : TimeEnv -> Z -> Contr -> Prop :=
| causal_zero ts t : CausalC ts t Zero
| causal_translate ts t d c : CausalC (map (fun x => x - Z.of_nat d) ts) (t - Z.of_nat d) c
                                     -> CausalC ts t (Translate d c)
| causal_let ts t t' e c : CausalE ts t' e -> CausalC (t' :: ts) t c -> CausalC ts t (Let e c)
| causal_scale ts t t' e c : t <= t' -> CausalE ts t' e -> CausalC ts t c -> CausalC ts t (Scale e c)
| causal_both ts t c1 c2 : CausalC ts t c1 -> CausalC ts t c1 -> CausalC ts t (Both c1 c2)
| causal_transfer t ts p1 p2 a : t <= 0 -> CausalC ts t (Transfer p1 p2 a)
| causal_if ts t d e c1 c2 : CausalE ts 0 e -> CausalC ts (t - Z.of_nat d) c1 -> CausalC ts t c2
                             -> CausalC ts t (If e d c1 c2)
.

(* Contextual causality is 'open': i.e. it is (anti-)monotone w.r.t. ordering on time. *)

Lemma CausalV_open t t' ts ts' (v : Var) : forall_zip Z.le ts' ts -> t <= t' -> CausalV ts t v -> CausalV ts' t' v.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'. generalize dependent ts. generalize dependent ts'.
  induction v; intros; inversion P; subst.
  - inversion Is. subst. constructor. omega.
  - inversion Is. subst. constructor. eauto.
Qed.

Lemma CausalE_open t t' ts ts' (e : Exp) : forall_zip Z.le ts' ts -> t <= t' -> CausalE ts t e -> CausalE ts' t' e.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'.
  generalize dependent ts. generalize dependent ts'.
  induction e using Exp_ind'; intros;inversion P;subst;econstructor.
  - induction args.
    * constructor.
    * inversion H3. inversion H. subst. constructor. eauto. apply IHargs. auto. constructor. auto. auto.
  - omega.
  - eapply CausalV_open; eauto. 
  - eapply IHe2; eauto. omega.
  - eapply IHe1 in H5.  apply H5; auto. constructor; auto. apply Z.le_refl. assumption.
Qed.


Lemma CausalC_open t t' ts ts' (c : Contr):
  forall_zip Z.le ts' ts -> t' <= t -> CausalC ts t c -> CausalC ts' t' c.
Proof.
  intros Is I P. generalize dependent t. generalize dependent t'.
  generalize dependent ts. generalize dependent ts'.
  induction c;intros;inversion P;subst.
  - constructor.
  - econstructor. eapply CausalE_open. eauto. apply Z.le_refl. eassumption.
    eapply IHc. constructor. apply Z.le_refl. eassumption. eassumption. eassumption.
  - econstructor. omega.
  - apply causal_scale with (t' := t'0). omega. eapply CausalE_open. eassumption.
    apply Z.le_refl. eassumption. eapply IHc; eassumption.
  - constructor. eapply IHc with (ts := map (fun x : Z => x - Z.of_nat n) ts) (t := t - Z.of_nat n).
    apply forall_zip_map; [intros; omega|assumption]. omega. assumption.
  - constructor;[eapply IHc1|eapply IHc1]; eauto.
  - constructor.
    + eapply CausalE_open;eauto. omega.
    + eapply IHc1 with (t:=t - Z.of_nat n). eassumption. omega. eassumption.
    + eapply IHc2 with (t:=t). eassumption. omega. eassumption.
Qed.
