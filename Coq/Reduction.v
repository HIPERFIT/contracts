Require Export Denotational.
Require Import Advance.
Require Import Tactics.
Require Import FunctionalExtensionality.

(********** Reduction semantics **********)



Inductive Red : Contr -> Env -> ExtEnv -> Contr -> Trans -> Prop :=
| red_zero env ext : Red Zero env ext Zero empty_trans
| red_let e env ext c c' t v :  E[| e |] env ext = Some v -> Red c (v::env) ext c' t ->
               Red (Let e c) env ext (Let (adv_exp (-1) e) c') t
| red_transf c p1 p2 env ext : Red (Transfer c p1 p2) env ext Zero (singleton_trans c p1 p2 1)
| red_scale e env ext c c' t v :  E[| e |] env ext = Some (RVal v) -> Red c env ext c' t ->
               Red (Scale e c) env ext (Scale (adv_exp (-1) e) c') (scale_trans v t)
| red_trans0 c env ext c' t : Red c env ext c' t -> Red (Translate 0 c) env ext c' t
| red_transS c env ext n : Red (Translate (S n) c) env ext (Translate n c) empty_trans
| red_both c1 c1' c2 c2' env ext t1 t2 : Red c1 env ext c1' t1 -> Red c2 env ext c2' t2 -> 
                         Red (Both c1 c2) env ext (Both c1' c2') (add_trans t1 t2)
| red_if0_false env ext c1 c2 c' b t : E[|b|] env ext = Some (BVal false) -> 
                                        Red c2 env ext c' t -> Red (If b 0 c1 c2) env ext c' t
| red_ifS_false env ext c1 c2 n b : E[|b|] env ext = Some (BVal false) -> Red (If b (S n) c1 c2) env ext (If b n c1 c2) empty_trans
| red_if_true env ext c1 c2 c' n b t : E[|b|] env ext = Some (BVal true) -> Red c1 env ext c' t -> Red (If b n c1 c2) env ext c' t
.

Hint Constructors Red.

Open Scope nat.

Theorem red_sound1 c c' env ext tr t  : Red c env ext c' t ->  C[|c|] env ext = Some tr -> tr 0 = t.
Proof.
  intro R. generalize dependent tr. induction R; simpl; intros tr T. 
  - inversion T. reflexivity.
  - rewrite H in T. simpl in T. apply IHR. apply T.
  - inversion T. reflexivity.
  - rewrite H in T. option_inv' T. unfold scale_trace,compose.
    simpl in H1. inversion H1. apply IHR in H2. subst. reflexivity.
  - unfold delay_trace in T. simpl in T. rewrite adv_ext_0 in T.
    option_inv' T. apply IHR. assumption.
  - simpl in T. option_inv' T. reflexivity.
  - option_inv' T. unfold add_trace. rewrite IHR1 by assumption. rewrite IHR2 by assumption. reflexivity.
  - rewrite H in T. auto.
  - rewrite H in T. option_inv' T. reflexivity.
  - destruct n; simpl in *; rewrite H in T; auto.
Qed.

Theorem red_sound2 c c' i env ext t t1 t2 : 
  Red c env ext c' t -> C[|c|]env ext = Some t1 -> C[|c'|] env (adv_ext 1 ext) = Some t2
  -> t1 (S i) = t2 i.
Proof.
  intros R T1 T2. generalize dependent t1. generalize dependent t2. induction R; simpl;intros.
  - inversion T1. inversion T2. reflexivity.
  - rewrite adv_exp_ext in T2. rewrite adv_ext_iter in T2. simpl in T2. rewrite adv_ext_0 in T2.
    rewrite H in *. simpl in *. apply IHR; auto.
  - inversion T1. inversion T2. subst. reflexivity.
  - rewrite adv_exp_ext in T2. rewrite adv_ext_iter in T2. simpl in T2. rewrite adv_ext_0 in T2.
    rewrite H in *. simpl in *. option_inv' T1. option_inv' T2. unfold pure,compose in *.
    eapply IHR in H4;eauto. inversion H3. inversion H5. unfold scale_trace, compose in *. rewrite H4. 
    reflexivity.
  - unfold delay_trace in *. rewrite adv_ext_0 in T1. 
    option_inv' T1. simpl. apply IHR; auto. 
  - option_inv' T1. option_inv' T2.
    unfold delay_trace in *. simpl in *. rewrite adv_ext_iter in H2. 
    assert (Z.pos (Pos.of_succ_nat n) = (1 + Z.of_nat n)%Z).
    assert (1%Z = Z.of_nat 1) by reflexivity. rewrite H in *.
    rewrite <- Nat2Z.inj_add in *. reflexivity.
    rewrite H in *.  rewrite H1 in H2. inversion H2. reflexivity.
  - option_inv' T1. option_inv' T2. unfold add_trace. erewrite IHR1;eauto. erewrite IHR2;eauto.
  - rewrite H in *. auto.
  - unfold delay_trace in *. rewrite H in *. option_inv' T1. simpl in *. 
    rewrite T2 in H2. inversion H2. f_equal. omega.
  - destruct n; simpl in T1; rewrite H in T1; auto.
Qed.

Ltac eauto_destruct := repeat(match goal with [ H : exists _, _ |- _] => destruct H end); eauto.

Theorem red_complete c env ext t : C[|c|] env ext = Some t -> exists c', Red c env ext c' (t 0).
Proof.
  generalize dependent t. generalize dependent env. induction c; simpl; intros.
  - inversion H. eauto.
  - option_inv' H. apply IHc in H3. eauto_destruct.
  - inversion H. simpl. eauto.
  - option_inv' H. apply IHc in H2. destruct H2. 
    unfold scale_trace, compose in *. option_inv' H1. destruct x2; tryfalse. 
    simpl in *. inversion H4. subst. eauto.
  - unfold delay_trace in *. option_inv' H. destruct n; simpl in *.
    + rewrite adv_ext_0 in H2. apply IHc in H2. eauto_destruct.
    + eauto.
  -  unfold add_trace in *. option_inv' H. apply IHc1 in H1. apply IHc2 in H2.
     eauto_destruct.
  - remember (E[|e|]env ext) as B. destruct B as [b'| ]. 
    + destruct b'. destruct b.
      * destruct n; simpl in *; rewrite <- HeqB in *; apply IHc1 in H;
        eauto_destruct. 
      * destruct n; simpl in *;rewrite <- HeqB in *.
        apply IHc2 in H. eauto_destruct.
        unfold delay_trace in H. simpl in *. option_inv' H. eauto_destruct.
      * destruct n; simpl in H; rewrite <- HeqB in *; tryfalse.
    + destruct n; simpl in *; rewrite <- HeqB in *; inversion H.
Qed.


Fixpoint RedFun (c : Contr) (env : Env) (ext : ExtEnv) : option (Contr * Trans) :=
  match c with
    | Zero => Some (Zero, empty_trans)
    | Let e c => E[|e|]env ext >>= fun val => liftM (fun res : (Contr * Trans) => 
                                                        let (c', t) := res in (Let (adv_exp (-1) e) c', t)) 
                                                     (RedFun c (val::env) ext)
    | Transfer c p1 p2 => Some (Zero, singleton_trans c p1 p2 1)
    | Scale e c => match RedFun c env ext, E[|e|]env ext with
                       | Some (c', t), Some (RVal v) => Some (Scale (adv_exp (-1) e) c', scale_trans v t)
                       | _, _ => None
                   end
    | Translate l c => match l with
                      | O => RedFun c env ext
                      | S l' => Some (Translate l' c, empty_trans)
                    end
    | Both c1 c2 => match RedFun c1 env ext, RedFun c2 env ext with
                      | Some (c1', t1), Some (c2', t2) => Some (Both c1' c2', add_trans t1 t2)
                      | _, _ => None
                    end
    | If b l c1 c2 => match E[|b|] env ext with
                              | Some (BVal false) => match l with
                                                | O => RedFun c2 env ext
                                                | S l' => Some (If b l' c1 c2, empty_trans)
                                              end
                              | Some (BVal true) => RedFun c1 env ext
                              | _ => None
                            end
  end.

Lemma redfun_red c env ext c' t : RedFun c env ext = Some (c', t) -> Red c env ext c' t.
Proof.
  generalize dependent c'. generalize dependent t. generalize dependent env.
  induction c; intros env t c' R; simpl in R; try solve [inversion R;auto].
  - option_inv_auto. destruct x0. apply IHc in H2. inversion H3.
    eauto.
  - remember (RedFun c env ext) as RF. destruct RF. destruct p. 
    remember (E[|e|]env ext) as RS. destruct RS. destruct v. inversion R.
    inversion R. auto. inversion R. inversion R.
  - destruct n. auto. inversion R. auto.
  - specialize IHc1 with (env:=env). specialize IHc2 with (env:=env). 
    destruct (RedFun c1 env ext) as [p1| ]. destruct (RedFun c2 env ext) as [p2| ].
    destruct p1, p2. inversion R. auto. destruct p1. inversion R. inversion R.
  - remember (E[|e|] env ext) as BS. destruct BS. destruct v. destruct b. constructor; auto.
    destruct n. constructor; auto. inversion R. constructor; auto. inversion R.
    inversion R.
Qed.


Lemma red_redfun c env ext c' t : Red c env ext c' t -> RedFun c env ext = Some (c', t).
Proof.
  intros R. induction R; simpl; repeat (simpl;rewr_assumption); auto. 
Qed.

Theorem Red_function c env ext c' t : RedFun c env ext = Some (c', t) <-> Red c env ext c' t.
Proof. split. apply redfun_red. apply red_redfun. Qed.