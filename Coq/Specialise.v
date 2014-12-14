Require Import Denotational.
Require Import DenotationalTyped.
Require Import Tactics.


(* Specialisation (a.k.a. partial evaluation) of contracts. *)


Import ListNotations.

Definition ExtEnvP := ExtEnv' (option Val).

Definition EnvP := list (option Val).

Definition fromLit (e : Exp) : option Val :=
  match e with
    | OpE (RLit r) nil => Some (RVal r)
    | OpE (BLit b) nil => Some (BVal b)
    | _ => None
  end.



Definition toLit (e : Val) : Exp :=
  match e with
    | RVal r => OpE (RLit r) nil
    | BVal b => OpE (BLit b) nil
  end.

Lemma toLit_fromLit x v : fromLit x = Some v -> toLit v = x.
Proof.
  intros. destruct x; try solve [simpl in H; inversion H].
  destruct op; simpl in H; try solve [inversion H]; destruct args;
  inversion H; subst; reflexivity.
Qed.
 
Definition default {A} (d : A) (x : option A) : A :=
  match x with
    | Some y => y
    | None => d
  end.

Definition fromBLit (e : Exp) : option bool :=
  match e with
    | OpE (BLit b) nil => Some b
    | _ => None
  end.

Definition fromRLit (e : Exp) : option R :=
  match e with
    | OpE (RLit r) nil => Some r
    | _ => None
  end.

Definition specialiseOp (op : Op) (args : list Exp) : option Exp :=
  match op with
    | Cond => match args with
                | [e1; e2; e3] => match fromBLit e1 with
                                      | Some true => Some e2
                                      | Some false => Some e3
                                      | _ => None
                                  end
                | _ => None
              end
    | And => match args with
               | [e1;e2] => match fromBLit e1, fromBLit e2 with
                              | Some false, _ => Some e1
                              | _, Some false => Some e2
                              | Some true, _ => Some e2
                              | _, Some true => Some e1
                              | _, _ => None
                            end
               | _ => None
             end
    | Or => match args with
               | [e1;e2] => match fromBLit e1, fromBLit e2 with
                              | Some true, _ => Some e1
                              | _, Some true => Some e2
                              | Some false, _ => Some e2
                              | _, Some false => Some e1
                              | _, _ => None
                            end
               | _ => None
             end
    | _ =>  None
  end.

Ltac destruct_match := match goal with
                         | [ _ : context [match ?x with 
                                          | _ => _ 
                                        end] |- _ ] => is_var x; destruct x
                         | [ |- context [match ?x with 
                                          | _ => _ 
                                         end]] => is_var x; destruct x
                         | [_:context[sequence [?o]]|- _] => is_var o; destruct o
                      end.
  
Fixpoint lookupEnvP (v : Var) (rho : EnvP) : option Val :=
  match v, rho with
    | V1, x::_ => x
    | VS v, _::xs => lookupEnvP v xs
    | _,_ => None
  end.


Fixpoint specialiseExp (e : Exp) (rho : ExtEnvP) (vars : EnvP) : Exp :=
    match e with
      | OpE op args => let args' := map (fun e' => specialiseExp e' rho vars) args
                       in default (OpE op args') (specialiseOp op args')
      | Obs obs t => default e (liftM toLit (rho obs t))
      | VarE v => default e (liftM toLit (lookupEnvP v vars))
      | Acc f l z => let rho' := adv_ext (-Z.of_nat l) rho in
                     let ze := (specialiseExp z rho' vars) in
                     let fe := (specialiseExp z rho (None :: vars)) in
                     let z' := fromLit ze in
                     let f' l r := fromLit (specialiseExp f (adv_ext (Z.of_nat l) rho') (r :: vars))
                     in default (Acc f l ze) (liftM toLit (Acc_sem f' l z'))
    end.

(* Definition of instantiation of external and internal environments *)

Definition ext_inst (rhop : ExtEnvP) (rho : ExtEnv) : Prop := forall l t v, rhop l t = Some v -> rho l t = v.

Definition env_inst : EnvP -> Env -> Prop := all2 (fun p v => forall v', p = Some v' -> v' = v).

Lemma env_inst_lookup rp r v x : env_inst rp r -> lookupEnvP v rp = Some x -> lookupEnv v r = Some x.
Proof.
  intros I L. generalize dependent r. generalize dependent rp. induction v;intros;simpl in *.
  - destruct I;tryfalse. apply H in L. subst. reflexivity.
  - destruct I;tryfalse. eapply IHv; eauto.
Qed.

Lemma Esem_toLit v vars rho :  E[|toLit v|] vars rho = Some v.
Proof.
  destruct v; reflexivity.
Qed.


Lemma Esem_fromLit e vars rho : fromLit e ⊆ E[|e|] vars rho.
Proof.
  unfold "⊆". simpl. intros. destruct e;tryfalse.
  destruct op; simpl in H; tryfalse; destruct args; tryfalse; auto.
Qed.


Lemma mapM_partial {A B} (f g : A -> option B) P v xs : 
  all P xs -> (forall x, P x -> forall v, f x = Some v -> g x = Some v) -> mapM f xs = Some v -> mapM g xs = Some v.
Proof.
  admit.
Qed.


Lemma sequence_map_partial {A B} (f g : A -> option B) v xs P : 
  all P xs -> (forall x, P x -> forall v, f x = Some v -> g x = Some v) ->
  sequence (map f xs) = Some v -> sequence (map g xs) = Some v.
Proof.
  admit.
Qed.


Lemma liftM_none {A B} (f : A -> B)  x : liftM f x = None -> x = None.
Proof.
  intro. destruct x;tryfalse. reflexivity.
Qed.

Definition TypeExtP (rhop : ExtEnvP) := forall z l t, |-O l ∶ t -> |-V' (rhop l z)  ∶ t.
Definition TypeEnvP (g : TyEnv) (rhop : EnvP) : Prop := all2 TypeVal' rhop g.


Lemma ext_inst_typed rho rhop : ext_inst rhop rho -> TypeExt rho -> TypeExtP rhop.
Proof.
  unfold TypeExt, TypeExtP. intros I T z l t O. 
  remember (rhop l z) as R. symmetry in HeqR. destruct R;constructor.
  apply I in HeqR. rewrite <- HeqR. auto.
Qed.

Lemma env_inst_typed rho rhop G : env_inst rhop rho -> TypeEnv G rho -> TypeEnvP G rhop.
Proof.
  intros I T. generalize dependent G. induction I;intros; inversion T; econstructor.
  destruct x. assert (Some v = Some v) as V by reflexivity. apply H in V. rewrite V. 
  auto. auto.  unfold TypeEnvP in *. eauto.
Qed.

Lemma toLit_typed x t g : |-V x ∶ t -> g |-E toLit x ∶ t.
Proof.
  intros. destruct x; simpl; inversion H; eauto.
Qed.

Lemma fromLit_typed e t g : g |-E e ∶ t -> |-V' fromLit e ∶ t.
Proof.
  intros. destruct e;auto.
  inversion H. clear H. subst. destruct op; simpl; try constructor;
                               destruct args;try inversion H3; auto.
 Qed.


Lemma mapM_some {A B} (f : A -> option B) xs x : (mapM f xs) = Some x -> all (fun x => exists y, f x = Some y) xs.
Proof.
  intro M. generalize dependent x. induction xs;intros;constructor;simpl in *;option_inv_auto;eauto.
Qed.
 
Lemma specialiseOp_typed op es e G ts t : 
|-Op op ∶ ts => t -> all2 (TypeExp G) es ts -> specialiseOp op es = Some e
                -> G |-E e ∶ t.
Proof.
  Ltac inv := match goal with
                | [T : all2 (TypeExp _)  _ _ |- _] => inversion T; clear T;subst
                | [_: context[match ?x with _ => _ end]|- _] => destruct x
                | [T: Some _ = Some _|- _] => inversion T;clear T; subst
            end.

  intros O A S. inversion O;subst;clear O; simpl in *; tryfalse;
  repeat inv; tryfalse; auto.
Qed.

Lemma all2_map_all2 {A' A B B'} xs ys P (f : A -> A') (g : B -> B') : 
  all2 (fun x y => P (f x) (g y)) xs ys -> all2 P (map f xs) (map g ys).
Proof. 
  intro Ps. induction Ps;simpl;constructor;auto.
Qed.

Lemma lookupEnvP_typed G varsp v t : TypeEnvP G varsp -> G |-X v ∶ t -> |-V' lookupEnvP v varsp ∶ t.
Proof.
  intros E V. generalize dependent varsp. generalize dependent G. 
  induction v;intros.
  - simpl. destruct varsp. auto. inversion E. subst. inversion V. subst. assumption.
  - simpl. destruct varsp. constructor. inversion V. subst. inversion E. subst. eauto.
Qed.

Lemma adv_extp_type: forall (e : ExtEnvP) (d : Z), TypeExtP e -> TypeExtP (adv_ext d e).
Proof.
  unfold TypeExtP, adv_ext. intros. auto.
Qed.

  
Lemma constFoldAcc_typed rho f l z t : 
  TypeExtP rho
  -> (forall i x, |-V' x ∶ t -> |-V' f i x ∶ t)
  -> (|-V' z ∶ t)
  -> |-V' Acc_sem f l z ∶ t.
Proof.
  intros. induction l;intros; simpl; auto using adv_extp_type.
Qed.

Lemma TypeVal_Some v t : |-V' Some v ∶ t -> |-V v ∶ t.
Proof.
  intros H. inversion H. auto.
Qed.

Hint Resolve adv_extp_type.

Lemma specialiseExp_typed G e t rhop varsp : 
  G |-E e ∶ t -> TypeEnvP G varsp -> TypeExtP rhop
      -> G |-E specialiseExp e rhop varsp ∶ t.
Proof.
  intros E V R. generalize dependent varsp. generalize dependent rhop. 
  induction E using TypeExp_ind'; intros.
  - simpl. remember (specialiseOp op (map (fun e' : Exp => specialiseExp e' rhop varsp) es)) as S.
    symmetry in HeqS. 
    do 4 (eapply all2_apply in H1; try eassumption).
    apply all2_map_all2 in H1. rewrite map_id in H1.
    destruct S. 
    + simpl.  eapply specialiseOp_typed in HeqS; eassumption. 
    + simpl. econstructor; eassumption.
  - simpl. remember (rhop o z) as O. symmetry in HeqO. destruct O. 
    + simpl. apply toLit_typed. unfold TypeExtP in *. apply R with (z:=z) in H. rewrite HeqO in H.
      inversion H. assumption.
    + simpl. auto.
  - simpl. remember (lookupEnvP v varsp) as L. symmetry in HeqL. destruct L.
    + simpl. apply toLit_typed. eapply lookupEnvP_typed in H;eauto. rewrite HeqL in H. inversion H.
      assumption.
    + simpl. auto.
  - simpl. remember (Acc_sem
               (fun (l : nat) (r : option Val) =>
                fromLit
                  (specialiseExp e1
                     (adv_ext (Z.of_nat l) (adv_ext (- Z.of_nat n) rhop))
                     (r :: varsp))) n
               (fromLit
                  (specialiseExp e2 (adv_ext (- Z.of_nat n) rhop) varsp))) as S.
    symmetry in HeqS. destruct S. 
    + simpl. apply toLit_typed. apply TypeVal_Some. rewrite <- HeqS. eapply constFoldAcc_typed.
      * eassumption. 
      * intros. eapply fromLit_typed. apply IHE1; auto. constructor;auto.
      * intros. eapply fromLit_typed. apply IHE2; auto. 
    + simpl. auto.
Qed.

Lemma fromBLit_Some b x : Some b = fromBLit x -> x = OpE (BLit b) [].
Proof.
  intros. destruct x;tryfalse. simpl in *. destruct op;tryfalse. destruct args;tryfalse.
  inversion H. reflexivity.
Qed.

Lemma specialiseOp_sound (op : Op) es e vars rho G ts t:
|-Op op ∶ ts => t -> all2 (TypeExp G) es ts -> TypeEnv G vars -> TypeExt rho ->
  specialiseOp op es = Some e -> E[|OpE op es|] vars rho = E[|e|] vars rho.
Proof.
  Ltac inv' := match goal with
                | [T : all2 (TypeExp _)  _ _ |- _] => inversion T; clear T;subst
                | [_: context[match ?x with _ => _ end]|- _] => let y := fresh in remember x as y;
                                                                                 destruct y;tryfalse
                | [T : Some _ = fromBLit _ |- _] => apply fromBLit_Some in T
                | [T: Some _ = Some _|- _] => inversion T;clear T; subst
              end.
  Ltac tot := match goal with
                | [T : TypeExp _ _ _ |- _] => eapply Esem_typed_total in T; eauto; decompose [ex and] T; clear T
                | [T : _ = Some _ |- _ ] => rewrite T; simpl in *
                | [|-context [match ?x with _ => _ end]] => let y := fresh in remember x as y;
                                                                                 destruct y;tryfalse
                | [T : TypeVal _ _ |- _] => inversion T; clear T;subst
              end.

  intros O A E X R.
 inversion O;subst;clear O; simpl in *;tryfalse;
 repeat inv'; simpl; repeat tot; try reflexivity; destruct b; reflexivity.
Qed.


Lemma all2_all {A B} P (xs : list A) (ys : list B) : all2 (fun x y => P x) xs ys -> all P xs.
Proof.
  intros T. induction T;constructor;auto.
Qed.

Hint Resolve env_inst_typed ext_inst_typed specialiseExp_typed.


Lemma lookupEnvP_sound varsp vars v x : 
  env_inst varsp vars -> lookupEnvP v varsp = Some x -> lookupEnv v vars = Some x.
Proof.
  intros I L. generalize dependent x. generalize dependent varsp. generalize dependent vars. 
  induction v;intros; simpl in *; destruct varsp;tryfalse; inversion I; subst. 
  - erewrite <- H1; reflexivity.
  - eapply IHv;eauto.
Qed.

Theorem specialiseExp_sound G e t rhop rho varsp vars : 
  G |-E e ∶ t -> TypeExt rho -> TypeEnv G vars ->
      ext_inst rhop rho -> env_inst varsp vars -> 
      E[|specialiseExp e rhop varsp|] vars rho  = E[|e|] vars rho.
Proof.
  intros T R V I J. induction T using TypeExp_ind'.
  - simpl. 
    apply all2_all in H1. apply all_apply in H1;auto. apply map_rewrite in H1.
    remember (specialiseOp op (map (fun e' : Exp => specialiseExp e' rhop varsp) es)) as S.
    symmetry in HeqS. destruct S.
    + eapply specialiseOp_sound in HeqS;eauto. simpl in *. rewrite <- HeqS. 
      rewrite map_map. rewrite H1. reflexivity.
      rewrite <- map_id.  eapply all2_map; eauto.
    + simpl. rewrite map_map. rewrite H1. reflexivity.
  - simpl. remember (rhop o z) as O. symmetry in HeqO. destruct O; simpl. apply I in HeqO. rewrite HeqO.
    apply Esem_toLit. reflexivity.
  - simpl. remember (lookupEnvP v varsp) as L. symmetry in HeqL. destruct L. 
    + simpl. rewrite Esem_toLit. erewrite lookupEnvP_sound;eauto.
    + reflexivity.
  - (* case for accumulations still missing *)

Qed.



Theorem specializeExp e rhop rho varsp vars : ext_inst rhop rho -> env_inst varsp vars -> 
                                            E[|specialiseExp e rhop varsp|] vars rho  ⊆ E[|e|] vars rho.
Proof.
  intros R V. induction e using Exp_ind';intros e E.
  - simpl in *. rewrite map_map in *. option_inv_auto.
    remember (liftM toLit (OpSemLazy op
              (map (fun x : Exp => fromLit (specialiseExp x rhop varsp)) args))) as S.
    destruct S. 
    + option_inv_auto. destruct op; try solve[
        simpl in *; rewrite Esem_toLit in E; inversion E; subst; option_inv_auto;
        eapply sequence_map_partial in H2; [rewrite H2;simpl; assumption|apply H| simpl; intros;
          eapply Esem_fromLit in H1; apply H0 in H1; apply H1]].
      * simpl in *. rewrite Esem_toLit in E. inversion E. clear E. subst.
        destruct H;tryfalse. destruct H0;tryfalse. destruct H2;tryfalse.
        simpl in *. 
        remember (fromLit (specialiseExp x rhop varsp)) as A. symmetry in HeqA.
        remember (fromLit (specialiseExp x0 rhop varsp)) as B. symmetry in HeqB.
        destruct A. eapply Esem_fromLit in HeqA. erewrite H;eauto. 
        destruct B. eapply Esem_fromLit in HeqB. erewrite H0;eauto. simpl.
        destruct v; destruct v0; try destruct b;try destruct b0;inversion H1; try reflexivity.

 destruct v. destruct b. destruct B. destruct v. destruct b. 
      * admit.
      * admit.
    + clear HeqS. simpl in *. rewrite map_map in E. option_inv_auto. 
      eapply sequence_map_partial in H1. rewrite H1. simpl. assumption. apply H. simpl.
      intros. auto.
  - simpl in *. remember (rhop l i) as O. destruct O;try assumption. simpl in *.
    symmetry in HeqO. apply R in HeqO. rewrite HeqO.
    rewrite Esem_toLit in E. assumption.
  - simpl in *. remember (lookupEnvP v varsp) as S. destruct S;try assumption. simpl in *. symmetry in HeqS.
    eapply env_inst_lookup in HeqS;eauto. rewrite Esem_toLit in E. inversion E. subst. assumption.
  - 
Qed.



Ltac destruct_match' := match goal with
                         | [ _ : context [match ?x with 
                                          | _ => _ 
                                        end] |- _ ] => is_var x; destruct x
                         | [ |- context [match ?x with 
                                          | _ => _ 
                                         end]] => is_var x; destruct x
                      end.

Lemma OpSemLazy_monotone (op : Op) (args args' : list (option Val)) :
  args ⊆ args' -> OpSemLazy op args ⊆ OpSemLazy op args'.
Proof.
  unfold "⊆". simpl. intros F S. destruct op;
    try solve [simpl in *; apply bind_monotone; apply sequence_monotone; auto];

    destruct F; try destruct F; try destruct F;auto; destruct x; destruct x0;
    try erewrite H, H0 by reflexivity; auto; intros; simpl in *;
    repeat (destruct_match';try pose (H _ eq_refl) as C; try pose (H0 _ eq_refl) as C; tryfalse;auto;try inversion F).
Qed.

Lemma map_monotone {A B} (f : A -> option B) g l : (forall x, f x ⊆ g x) -> map f l ⊆ map g l.
Proof.
  unfold "⊆". simpl. intros. induction l; simpl; constructor; auto.
Qed.

Theorem specialiseExp_sound e rho vars rhop varsp:
                           ext_inst rhop rho -> env_inst varsp vars -> E[| e |] vars' rho' ⊆
                           E[| specialiseExp e rho vars |] vars' rho'.
Proof.
  generalize dependent rho. generalize dependent rho'.
  generalize dependent vars. 
  induction e using Exp_ind'; intros vars rho' rho R. 
  - unfold "⊆". simpl.  intros v E.
    do 4 (eapply all_apply_dep in H; eauto).
    remember (map (fun e' : Exp => specialiseExp e' rho vars) args) as args'. unfold default.
    remember (liftM toLit (OpSemLazy op (map fromLit args'))) as A. destruct A.

    + apply sequence_map_monotone in H. eapply bind_monotone' in H. apply H in E.
      apply OpSemLazy_sound in E.
      rewrite Heqargs' in HeqA. rewrite map_map in HeqA.
      symmetry in HeqA. apply liftM_some in HeqA. decompose [ex and] HeqA. clear HeqA. subst.
      rewrite Esem_toLit. eapply OpSemLazy_monotone  in H1. rewrite <- E. rewrite <- H1. reflexivity.
      apply map_monotone. intros. apply Esem_fromLit.

    + simpl. simpl in E. rewrite Heqargs'. rewrite map_map. 
      apply mapM_monotone in H. rewrite sequence_map. rewrite sequence_map in E.
      unfold "⊆" in H. simpl in H.
      remember (mapM (fun e : Exp => E'[|e|] vars rho') args) as M. destruct M.
      erewrite H by reflexivity. rewrite <- E. reflexivity.
      simpl in E. inversion E.
  - simpl. intros. unfold default. remember (rho l i) as L. destruct L. simpl.
    symmetry in HeqL. apply R in HeqL. rewrite HeqL in H.
    inversion H. subst. apply Esem_toLit. simpl. auto.
  - simpl. intros. unfold default. rewrite H. simpl.
    apply Esem_toLit.
  - admit.
     (* generalize dependent rho. generalize dependent rho'. *)
     (* generalize dependent vars. *)
     (* induction d. *)
     (* + simpl. intros. unfold default. apply IHe2; eauto. *)
     (* + simpl. unfold compose. intros. unfold default. simpl in IHe1. *)
     (*   eapply bind_monotone in IHe1. eapply IHe1 in H.      remember (constFoldAcc (adv_ext (-1) rho) *)
     (*          (fun (rho0 : ExtEnv) (r : option Val) => *)
     (*           specialiseExp e1 rho0 (r :: vars)) d *)
     (*          (fun rho0 : ExtEnv => specialiseExp e2 rho0 vars)) as E1. *)
     (*   destruct E1. simpl. apply IHe1; eauto. constructor; eauto. *)
     (*   symmetry in HeqE1. simpl in IHd. apply IHd in HeqE1.  *)
     (*   remember (specialiseExp (Acc e1 d e2) (adv_ext (-1) rho) vars) as FOO. *)
     (*   simpl in HeqFOO. unfold default in HeqFOO. *)
Qed.


Fixpoint traverseIfWithin (rho : ExtEnv) (e: Exp) (c1 c2 : ExtEnv -> Contr) (l : nat) : Contr + (Exp * nat) :=
  match specialiseExp e rho nil with
      | OpE (BLit true) nil => inl (c1 rho)
      | OpE (BLit false) nil => match l with
                        | O => inl (c2 rho)
                        | S l' => traverseIfWithin (adv_ext 1 rho) e c1 c2 l'
                        end
      | e' => inr (e', l)
  end.

Definition isZeroLit (e : Exp) : bool :=
  match e with
    | OpE (RLit r) nil => Reqb r 0
    | _ => false
end.

Fixpoint specialise (c : Contr) (rho : ExtEnv) : Contr :=
  match c with
    | Zero => c
    | Transfer _ _ _ => c
    | Scale e c' => let e' := specialiseExp e rho nil
                    in if isZeroLit e' then Zero
                       else match specialise c' rho with
                              | Zero => Zero 
                              | c'' => Scale e' c''
                            end
    | Translate l c' => match (specialise c' (adv_ext (Z.of_nat l) rho)) with
                           | Zero => Zero
                           | c'' => translate l c''
                        end
    | Both c1 c2 => match specialise c1 rho, specialise c2 rho with
                        | Zero, c' => c'
                        | c', Zero => c'
                        | c1', c2' => Both c1' c2'
                    end
    | If e l c1 c2 => match traverseIfWithin rho e (specialise c1) (specialise c2) l with
                              | inl c' => c'
                              | inr (e', l') => translate (l - l') (If e' l' c1 c2)
                            end
  end.
