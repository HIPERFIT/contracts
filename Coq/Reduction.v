Require Export Denotational.
Require Import Advance.
Require Import Tactics.

(********** Reduction semantics **********)



Inductive Red : Contr -> ExtEnv -> Contr -> trans' -> Prop :=
| red_zero rho : Red Zero rho Zero empty_trans'
| red_transf c p1 p2 rho : Red (Transfer c p1 p2) rho Zero (singleton_trans' c p1 p2 1)
| red_scale e rho c c' t v :  E[| e |] rho = Some (RVal v) -> Red c rho c' t ->
               Red (Scale e c) rho (Scale (adv_exp (-1) e) c') (scale_trans' v t)
| red_trans0 c rho c' t : Red c rho c' t -> Red (Translate 0 c) rho c' t
| red_transS c rho n : Red (Translate (S n) c) rho (Translate n c) empty_trans'
| red_both c1 c1' c2 c2' rho t1 t2 : Red c1 rho c1' t1 -> Red c2 rho c2' t2 -> 
                         Red (Both c1 c2) rho (Both c1' c2') (add_trans' t1 t2)
| red_if0_false rho c1 c2 c' b t : E[|b|] rho = Some (BVal false) -> Red c2 rho c' t -> Red (If b 0 c1 c2) rho c' t
| red_ifS_false rho c1 c2 n b : E[|b|] rho = Some (BVal false) -> Red (If b (S n) c1 c2) rho (If b n c1 c2) empty_trans'
| red_if_true rho c1 c2 c' n b t : E[|b|] rho = Some (BVal true) -> Red c1 rho c' t -> Red (If b n c1 c2) rho c' t
.

Hint Constructors Red.

Theorem red_sound1 c c' rho t  : Red c rho c' t ->  C[|c|]rho 0 = Some t.
Proof.
  intro R. induction R; simpl. 
  - reflexivity.
  - reflexivity.
  - unfold scale_trace, compose. rewrite IHR.  rewrite H. reflexivity.
  - unfold delay_trace. simpl. rewrite adv_ext_0. 
    assumption.
  - unfold delay_trace. reflexivity.
  - unfold add_trace. rewrite IHR1. rewrite IHR2. reflexivity.
  - rewrite H. assumption.
  - rewrite H. unfold delay_trace. reflexivity.
  - destruct n; simpl; rewrite H; assumption.
Qed.

Theorem red_sound2 c c' i rho t  : Red c rho c' t ->  C[|c|]rho (S i) = C[|c'|](adv_ext 1 rho) i.
Proof.
  intros R. induction R; simpl.
  - reflexivity.
  - reflexivity.
  - unfold scale_trace, compose. rewrite -> adv_exp_ext. rewrite adv_ext_iter. simpl.
    rewrite adv_ext_0. rewrite IHR.  reflexivity.
  - unfold delay_trace. rewrite adv_ext_0. assumption.
  - unfold delay_trace. simpl. rewrite adv_ext_iter. 
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
    remember (E[|e|]rho) as R. destruct R; tryfalse.
    destruct v; tryfalse. simpl in H.
    remember (C[|c|] rho 0) as C. destruct C;tryfalse. inversion H. 
    assert (exists c', Red c rho c' t0) as R by auto.
    destruct R as [c'].
    eexists. apply red_scale; auto. apply H0.
  - unfold delay_trace in *. destruct n; simpl in *. 
    + rewrite adv_ext_0 in *. apply IHc in H. destruct H as [c'].
      eexists. constructor. apply H.
    + inversion H. eexists. constructor.
  -  unfold add_trace in *.
     destruct (C[|c1|] rho 0);tryfalse. destruct (C[|c2|] rho 0);tryfalse.
     pose (IHc1 _ eq_refl) as IH1.  pose (IHc2 _ eq_refl) as IH2.
     destruct IH1. destruct IH2. inversion H. 
     eexists. constructor; eassumption.
  - remember (E[|e|]rho) as B. destruct B as [b'| ]. 
    + destruct b'. destruct b.
      * destruct n; simpl in *; rewrite <- HeqB in *; apply IHc1 in H;
        destruct H; eexists; apply red_if_true; eauto. 
      * destruct n; simpl in *;rewrite <- HeqB in *.
        apply IHc2 in H. destruct H. eexists. apply red_if0_false; eauto.
        unfold delay_trace in H. simpl in *. inversion H. eexists. constructor; auto.
      * destruct n; simpl in H; rewrite <- HeqB in *; tryfalse.
    + destruct n; simpl in *; rewrite <- HeqB in *; inversion H.
Qed.


Fixpoint RedFun (c : Contr) (rho : ExtEnv) : option (Contr * trans') :=
  match c with
    | Zero => Some (Zero, empty_trans')
    | Transfer c p1 p2 => Some (Zero, singleton_trans' c p1 p2 1)
    | Scale e c => match RedFun c rho, E[|e|]rho with
                       | Some (c', t), Some (RVal v) => Some (Scale (adv_exp (-1) e) c', scale_trans' v t)
                       | _, _ => None
                   end
    | Translate l c => match l with
                      | O => RedFun c rho
                      | S l' => Some (Translate l' c, empty_trans')
                    end
    | Both c1 c2 => match RedFun c1 rho, RedFun c2 rho with
                      | Some (c1', t1), Some (c2', t2) => Some (Both c1' c2', add_trans' t1 t2)
                      | _, _ => None
                    end
    | If b l c1 c2 => match E[|b|] rho with
                              | Some (BVal false) => match l with
                                                | O => RedFun c2 rho
                                                | S l' => Some (If b l' c1 c2, empty_trans')
                                              end
                              | Some (BVal true) => RedFun c1 rho
                              | _ => None
                            end
  end.

Lemma redfun_red c rho c' t : RedFun c rho = Some (c', t) -> Red c rho c' t.
Proof.
  generalize dependent c'. generalize dependent t.
  induction c; intros t c' R; simpl in R; try solve [inversion R;auto].
  - remember (RedFun c rho) as RF. destruct RF. destruct p.
    remember (E[|e|]rho) as RS. destruct RS. destruct v. inversion R.
    inversion R. auto. inversion R. inversion R.
  - destruct n. auto. inversion R. auto.
  - destruct (RedFun c1 rho) as [p1| ]. destruct (RedFun c2 rho) as [p2| ].
    destruct p1, p2. inversion R. auto. destruct p1. inversion R. inversion R.
  - remember (E[|e|]rho) as BS. destruct BS. destruct v. destruct b. constructor; auto.
    destruct n. constructor; auto. inversion R. constructor; auto. inversion R.
    inversion R.
Qed.


Lemma red_redfun c rho c' t : Red c rho c' t -> RedFun c rho = Some (c', t).
Proof.
  intros R. induction R; simpl; repeat rewr_assumption; auto.
Qed.

Theorem Red_function c rho c' t : RedFun c rho = Some (c', t) <-> Red c rho c' t.
Proof. split. apply redfun_red. apply red_redfun. Qed.