Require Export Denotational.
Require Import Advance.
Require Import Tactics.

(********** Reduction semantics **********)



Inductive Red : contract -> env -> contract -> trans -> Prop :=
| red_zero rho : Red Zero rho Zero empty_trans'
| red_transf c p1 p2 rho : Red (TransfOne c p1 p2) rho Zero (singleton_trans' c p1 p2 1)
| red_scale e rho c c' t v :  R[| e |] (fst rho) = Some v -> Red c rho c' t ->
               Red (Scale e c) rho (Scale (adv_rexp (-1) e) c') (scale_trans' v t)
| red_trans0 c rho c' t : Red c rho c' t -> Red (Transl 0 c) rho c' t
| red_transS c rho n : Red (Transl (S n) c) rho (Transl n c) empty_trans'
| red_both c1 c1' c2 c2' rho t1 t2 : Red c1 rho c1' t1 -> Red c2 rho c2' t2 -> 
                         Red (Both c1 c2) rho (Both c1' c2') (add_trans' t1 t2)
| red_if0_false rho c1 c2 c' b t : B[|b|] rho = Some false -> Red c2 rho c' t -> Red (IfWithin b 0 c1 c2) rho c' t
| red_ifS_false rho c1 c2 n b : B[|b|] rho = Some false -> Red (IfWithin b (S n) c1 c2) rho (IfWithin b n c1 c2) empty_trans'
| red_if_true rho c1 c2 c' n b t : B[|b|] rho = Some true -> Red c1 rho c' t -> Red (IfWithin b n c1 c2) rho c' t
.

Hint Constructors Red.

Theorem red_sound1 c c' rho t  : Red c rho c' t ->  C[|c|]rho 0 = Some t.
Proof.
  intro R. induction R; simpl. 
  - reflexivity.
  - reflexivity.
  - unfold scale_trace, compose. rewrite IHR. rewrite H. reflexivity.
  - unfold delay_trace. simpl. rewrite adv_env_0. 
    assumption.
  - unfold delay_trace. reflexivity.
  - unfold add_trace. rewrite IHR1. rewrite IHR2. reflexivity.
  - rewrite H. assumption.
  - rewrite H. unfold delay_trace. reflexivity.
  - destruct n; simpl; rewrite H; assumption.
Qed.

Theorem red_sound2 c c' i rho t  : Red c rho c' t ->  C[|c|]rho (S i) = C[|c'|](adv_env 1 rho) i.
Proof.
  intros R. induction R; simpl.
  - reflexivity.
  - reflexivity.
  - unfold scale_trace, compose. rewrite -> adv_rexp_env. rewrite adv_env_iter. simpl.
    rewrite adv_env_0. rewrite IHR.  reflexivity.
  - unfold delay_trace. rewrite adv_env_0. assumption.
  - unfold delay_trace. simpl. rewrite adv_env_iter. 
    assert (Z.pos (Pos.of_succ_nat n) = (1 + Z.of_nat n)%Z).
    assert (1%Z = Z.of_nat 1) by reflexivity. rewrite H.
    rewrite <- Nat2Z.inj_add. reflexivity.
    rewrite H. reflexivity.
  - unfold add_trace. rewrite IHR1. rewrite IHR2. reflexivity.
  - rewrite H. assumption.
  - unfold delay_trace. rewrite H. simpl. f_equal. omega.
  - destruct n; simpl; rewrite H; assumption.
Qed.

Theorem red_complete c rho t : C[|c|]rho 0 = Some t -> exists c', Red c rho c' t.
Proof.
  generalize dependent t. induction c; simpl; intros.
  - inversion H. eauto.
  - inversion H. eauto.
  - unfold scale_trace, compose in *.
    remember (R[|r|](fst rho)) as R. destruct R; tryfalse.
    remember (C[|c|] rho 0) as C. destruct C;tryfalse. inversion H. 
    assert (exists c', Red c rho c' t0) as R by auto.
    destruct R as [c'].
    eexists. apply red_scale; auto. apply H0.
  - unfold delay_trace in *. destruct n; simpl in *. 
    + rewrite adv_env_0 in *. apply IHc in H. destruct H as [c'].
      eexists. constructor. apply H.
    + inversion H. eexists. constructor.
  -  unfold add_trace in *.
     destruct (C[|c1|] rho 0);tryfalse. destruct (C[|c2|] rho 0);tryfalse.
     pose (IHc1 _ eq_refl) as IH1.  pose (IHc2 _ eq_refl) as IH2.
     destruct IH1. destruct IH2. inversion H. 
     eexists. constructor; eassumption.
  - remember (B[|b|]rho) as B. destruct B as [b'| ]. 
    + destruct b'.
      * destruct n; simpl in *; rewrite <- HeqB in *;apply IHc1 in H;
        destruct H; eexists; apply red_if_true; eauto. 
      * destruct n; simpl in *;rewrite <- HeqB in *.
        apply IHc2 in H. destruct H. eexists. apply red_if0_false; eauto.
        unfold delay_trace in H. simpl in *. inversion H. eexists. constructor; auto.
    + destruct n; simpl in *; rewrite <- HeqB in *; inversion H.
Qed.
