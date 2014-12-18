Require Import Denotational.
Require Export DenotationalTyped.
Require Import Tactics.
Require Import Equivalence.


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


Definition isZeroLit (e : Exp) : bool :=
  match e with
    | OpE (RLit r) nil => Reqb r 0
    | _ => false
end.

Definition isOneLit (e : Exp) : bool :=
  match e with
    | OpE (RLit r) nil => Reqb r 1
    | _ => false
end.

Definition specialiseOpSimp (op : Op) (args : list Exp) : option Exp :=
  liftM toLit (mapM fromLit args >>= OpSem op).

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
    | Add => match args with
               | [e1;e2] => if isZeroLit e1 then Some e2
                            else if isZeroLit e2 then Some e1 
                                 else specialiseOpSimp op args
               | _ => None
             end
    | Mult => match args with
               | [e1;e2] => if isOneLit e1 then Some e2
                            else if isOneLit e2 then Some e1
                                 else if isZeroLit e1 || isZeroLit e2 
                                      then Some (OpE (RLit 0) []) 
                                      else specialiseOpSimp op args
               | _ => None
             end
    | _ =>  specialiseOpSimp op args
  end.




  
Fixpoint lookupEnvP (v : Var) (env : EnvP) : option Val :=
  match v, env with
    | V1, x::_ => x
    | VS v, _::xs => lookupEnvP v xs
    | _,_ => None
  end.

Definition specialiseFun f  (env : EnvP) (ext : ExtEnvP) := 
  fun l r => fromLit(f (r :: env) (adv_ext (Z.of_nat l) ext)).

Fixpoint specialiseExp (e : Exp) (env : EnvP) (ext : ExtEnvP)  : Exp :=
    match e with
      | OpE op args => let args' := map (fun e' => specialiseExp e' env ext) args
                       in default (OpE op args') (specialiseOp op args')
      | Obs obs t => default e (liftM toLit (ext obs t))
      | VarE v => default e (liftM toLit (lookupEnvP v env))
      | Acc f l z => let ext' := adv_ext (-Z.of_nat l) ext in
                     let ze := (specialiseExp z env ext') in
                     let fe := (specialiseExp z (None :: env) ext) in
                     let z' := fromLit ze in
                     let f' := specialiseFun (specialiseExp f) env ext'
                     in default (Acc f l ze) (liftM toLit (Acc_sem f' l z'))
    end.

(* Definition of instantiation of external and internal environments *)

Definition ext_inst (extp : ExtEnvP) (ext : ExtEnv) : Prop := forall l t v, extp l t = Some v -> ext l t = v.

Definition env_inst : EnvP -> Env -> Prop := all2 (fun p v => forall v', p = Some v' -> v' = v).

Hint Unfold env_inst.

Lemma env_inst_lookup rp r v x : env_inst rp r -> lookupEnvP v rp = Some x -> lookupEnv v r = Some x.
Proof.
  intros I L. generalize dependent r. generalize dependent rp. induction v;intros;simpl in *.
  - destruct I;tryfalse. apply H in L. subst. reflexivity.
  - destruct I;tryfalse. eapply IHv; eauto.
Qed.

Lemma Esem_toLit v env ext :  E[|toLit v|] env ext = Some v.
Proof.
  destruct v; reflexivity.
Qed.


Lemma Esem_fromLit e env ext v : fromLit e = Some v -> E[|e|] env ext = Some v.
Proof.
  simpl. intros. destruct e;tryfalse.
  destruct op; simpl in H; tryfalse; destruct args; tryfalse; auto.
Qed.


Definition TypeExtP (extp : ExtEnvP) := forall z l t, |-O l ∶ t -> |-V' (extp l z)  ∶ t.
Definition TypeEnvP (g : TyEnv) (envp : EnvP) : Prop := all2 TypeVal' envp g.

Hint Unfold TypeEnvP.

Lemma ext_inst_typed ext extp : ext_inst extp ext -> TypeExt ext -> TypeExtP extp.
Proof.
  unfold TypeExt, TypeExtP. intros I T z l t O. 
  cases (extp l z) as R;constructor.
  apply I in R. rewrite <- R. auto.
Qed.

Lemma env_inst_typed env envp G : env_inst envp env -> TypeEnv G env -> TypeEnvP G envp.
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

  Ltac inv := match goal with
                | [T : all2 (TypeExp _)  _ _ |- _] => inversion T; clear T;subst
                | [_: context[match ?x with _ => _ end]|- _] => destruct x
                | [T: Some _ = Some _|- _] => inversion T;clear T; subst
            end.

 
Lemma specialiseOpSimp_typed op es e G ts t : 
|-Op op ∶ ts => t -> all2 (TypeExp G) es ts -> specialiseOpSimp op es = Some e
                -> G |-E e ∶ t.
Proof.
  intros O A S. unfold specialiseOpSimp in *.
  eapply OpSem_typed_total in O. decompose [ex and] O. rewrite H0 in S.
  simpl in S. unfold compose, pure in *. inversion S. apply toLit_typed. assumption.
  clear O. option_inv_auto. clear H2. generalize dependent x0. induction A;constructor.
  simpl in H1. option_inv_auto. eexists. split. eassumption. apply fromLit_typed in H.
  rewrite H0 in H. inversion H. rewrite <- H1 in H0. inversion H0. subst. assumption.
  simpl in H1. option_inv_auto. eauto.
Qed.

Lemma specialiseOp_typed op es e G ts t : 
|-Op op ∶ ts => t -> all2 (TypeExp G) es ts -> specialiseOp op es = Some e
                -> G |-E e ∶ t.
Proof.

  intros O A S. inversion O;subst;clear O; simpl in *; tryfalse;
  repeat inv; tryfalse; eauto using specialiseOpSimp_typed.
Qed.

Lemma lookupEnvP_typed G envp v t : TypeEnvP G envp -> G |-X v ∶ t -> |-V' lookupEnvP v envp ∶ t.
Proof.
  intros E V. generalize dependent envp. generalize dependent G. 
  induction v;intros.
  - simpl. destruct envp. auto. inversion E. subst. inversion V. subst. assumption.
  - simpl. destruct envp. constructor. inversion V. subst. inversion E. subst. eauto.
Qed.

Lemma adv_extp_type: forall (e : ExtEnvP) (d : Z), TypeExtP e -> TypeExtP (adv_ext d e).
Proof.
  unfold TypeExtP, adv_ext. intros. auto.
Qed.

Hint Resolve adv_extp_type.
  
Lemma constFoldAcc_typed ext f l z t : 
  TypeExtP ext
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



Tactic Notation "destruct_toLit" ident (d') 
  := match goal with
       | [|- context[liftM toLit ?x]] => let d := fresh in 
                                         cases x as d'
     end.


Lemma specialiseExp_typed G e t extp envp : 
  G |-E e ∶ t -> TypeEnvP G envp -> TypeExtP extp
      -> G |-E specialiseExp e envp extp ∶ t.
Proof.
  intros E V R. generalize dependent envp. generalize dependent extp. 
  induction E using TypeExp_ind'; intros.
  - simpl. 
        do 4 (eapply all2_apply in H1; try eassumption).
    apply all2_map_all2 in H1. rewrite map_id in H1.
    cases (specialiseOp op (map (fun e' : Exp => specialiseExp e' envp extp) es)) as S.
    + simpl.  eapply specialiseOp_typed in S; eassumption. 
    + simpl. econstructor; eassumption.
  - simpl. cases (extp o z) as O.
    + simpl. apply toLit_typed. unfold TypeExtP in *. apply R with (z:=z) in H. rewrite O in H.
      inversion H. assumption.
    + simpl. auto.
  - simpl. cases (lookupEnvP v envp) as L.
    + simpl. apply toLit_typed. eapply lookupEnvP_typed in H;eauto. rewrite L in H. inversion H.
      assumption.
    + simpl. auto.
  - simpl. destruct_toLit S.
    + apply toLit_typed. apply TypeVal_Some. rewrite <- S. eapply constFoldAcc_typed.
      * eassumption. 
      * intros. eapply fromLit_typed. apply IHE1; auto.
      * intros. eapply fromLit_typed. apply IHE2; auto. 
    + simpl. auto.
Qed.

Lemma fromBLit_Some b x : fromBLit x = Some b -> x = OpE (BLit b) [].
Proof.
  intros. destruct x;tryfalse. simpl in *. destruct op;tryfalse. destruct args;tryfalse.
  inversion H. reflexivity.
Qed.


Lemma isZeroLit_true x : isZeroLit x = true -> x = OpE (RLit 0) [].
Proof.
  intros. destruct x;tryfalse. destruct args; destruct op;tryfalse. 
  simpl in H. apply Reqb_iff in H. subst. reflexivity.
Qed.

Lemma isOneLit_true x : isOneLit x = true -> x = OpE (RLit 1) [].
Proof.
  intros. destruct x;tryfalse. destruct args; destruct op;tryfalse. 
  simpl in H. apply Reqb_iff in H. subst. reflexivity.
Qed.




Lemma specialiseOpSimp_sound (op : Op) es e env ext G ts t:
|-Op op ∶ ts => t -> all2 (TypeExp G) es ts -> TypeEnv G env -> TypeExt ext ->
  specialiseOpSimp op es = Some e -> E[|OpE op es|] env ext = E[|e|] env ext.
Proof.
  intros O A E X R. unfold specialiseOpSimp in R. option_inv_auto. simpl.
  rewrite Esem_toLit. rewrite sequence_map. eapply mapM_monotone' in H1.
  rewrite H1. assumption.  simpl. intros. auto using Esem_fromLit.
Qed.

Lemma specialiseOp_sound (op : Op) es e env ext G ts t:
|-Op op ∶ ts => t -> all2 (TypeExp G) es ts -> TypeEnv G env -> TypeExt ext ->
  specialiseOp op es = Some e -> E[|OpE op es|] env ext = E[|e|] env ext.
Proof.
  Ltac inv' := match goal with
                | [T : all2 (TypeExp _)  _ _ |- _] => inversion T; clear T;subst
                | [_: context[match ?x with _ => _ end]|- _] => cases x;tryfalse
                | [T : fromBLit _ = Some _ |- _] => apply fromBLit_Some in T
                | [T : isZeroLit _ = true |- _] => apply isZeroLit_true in T
                | [T : isOneLit _ = true |- _] => apply isOneLit_true in T
                | [T : ?x || ?y = true |- _] => cases x;cases y;simpl in T; tryfalse
                | [T: Some _ = Some _|- _] => inversion T;clear T; subst
                | [T: specialiseOpSimp _ _ = Some _ |- _] => eapply specialiseOpSimp_sound in T;eauto
              end.
  Ltac tot := match goal with
                | [T : TypeExp _ _ _ |- _] => eapply Esem_typed_total in T; eauto; decompose [ex and] T; clear T
                | [T : _ = Some _ |- _ ] => rewrite T; simpl in *
                | [|-context [match ?x with _ => _ end]] => cases x;tryfalse
                | [T : TypeVal _ _ |- _] => inversion T; clear T;subst
              end.

  intros O A E X R.
 inversion O;subst;clear O; simpl in *;tryfalse;
 repeat inv'; simpl; repeat tot; try reflexivity; try destruct b; 
 try first [reflexivity|rewrite Rplus_0_l|rewrite Rplus_0_r|rewrite Rmult_1_l|rewrite Rmult_1_r|rewrite Rmult_0_l|rewrite Rmult_0_r]; try first [reflexivity|assumption].
Qed.


Lemma ext_inst_adv extp ext z : ext_inst extp ext -> ext_inst (adv_ext z extp) (adv_ext z ext).
Proof.
  unfold ext_inst, adv_ext. intros. auto.
Qed.

Hint Resolve env_inst_typed ext_inst_typed specialiseExp_typed ext_inst_adv.


Lemma lookupEnvP_sound envp env v x : 
  env_inst envp env -> lookupEnvP v envp = Some x -> lookupEnv v env = Some x.
Proof.
  intros I L. generalize dependent x. generalize dependent envp. generalize dependent env. 
  induction v;intros; simpl in *; destruct envp;tryfalse; inversion I; subst. 
  - erewrite <- H1; reflexivity.
  - eapply IHv;eauto.
Qed.

Theorem specialiseExp_sound G e t extp ext envp env : 
  G |-E e ∶ t -> TypeExt ext -> TypeEnv G env ->
      ext_inst extp ext -> env_inst envp env -> 
      E[|specialiseExp e envp extp|] env ext  = E[|e|] env ext.
Proof.
  intros T R V I J. generalize dependent ext. generalize dependent extp. 
  generalize dependent env. generalize dependent envp.
  induction T using TypeExp_ind';intros.
  - simpl. 
    apply all2_all in H1. do 8 (eapply all_apply in H1;eauto). apply map_rewrite in H1.
    cases (specialiseOp op (map (fun e' : Exp => specialiseExp e' envp extp) es)) as S.
    + eapply specialiseOp_sound in S;eauto. simpl in *. rewrite <- S. 
      rewrite map_map. rewrite H1. reflexivity.
      rewrite <- map_id.  eapply all2_map; eauto.
    + simpl. rewrite map_map. rewrite H1. reflexivity.
  - simpl. cases (extp o z) as O; simpl. apply I in O. rewrite O.
    apply Esem_toLit. reflexivity.
  - simpl. cases (lookupEnvP v envp) as L.
    + simpl. rewrite Esem_toLit. erewrite lookupEnvP_sound;eauto.
    + reflexivity.
  - generalize dependent ext. generalize dependent extp. 
    generalize dependent env. generalize dependent envp. induction n;intros.
    + simpl. destruct_toLit S.
      * eapply Esem_fromLit in S. rewrite IHT2 in S; eauto. 
        simpl. rewrite Esem_toLit. auto.
      * simpl. auto.
    + assert (g |-E Acc e1 n e2 ∶ t) as A by auto.
      eapply Esem_typed_total with (ext:= adv_ext (-1) ext) in A; eauto.
      assert (g |-E specialiseExp (Acc e1 n e2) envp (adv_ext (-1) extp) ∶ t) as As 
                                                                                 by (apply specialiseExp_typed;eauto).
      eapply Esem_typed_total with (ext := adv_ext (-1) ext) in As;eauto.
      simpl in *. destruct_toLit S.
      * simpl. rewrite Esem_toLit.         
        unfold Fsem at 1. simpl. simpl in IHn. repeat rewrite adv_ext_step'. 
        erewrite <- IHn with (extp:=adv_ext (-1) extp) (envp := envp); eauto.
        destruct_toLit S'.
        simpl. rewrite Esem_toLit. simpl. 
        eapply Esem_fromLit with (env := v0 :: env) in S. rewrite <- S. 
        eapply IHT1;eauto. constructor;eauto. 
        decompose [ex and] As.  simpl in H0. rewrite Esem_toLit in H0. inversion H0. assumption.
        constructor;auto.
        intros. rewrite <- adv_ext_step' in S'. rewrite S' in H. inversion H. reflexivity. 
        repeat rewrite adv_ext_iter. 
        assert (Z.neg (Pos.of_succ_nat n) + Z.of_nat (Datatypes.S n) = 
                (-1) + (- Z.of_nat n + Z.pos (Pos.of_succ_nat n)))%Z as E by
        (rewrite Zneg_of_succ_nat; rewrite Zpos_P_of_succ_nat; repeat rewrite Nat2Z.inj_succ; omega) .
        rewrite E. auto. 

        
        simpl. unfold specialiseFun in S. decompose [ex and] A. 
        eapply Esem_fromLit with (env := x :: env) (ext :=(adv_ext (Z.pos (Pos.of_succ_nat n))
        (adv_ext (- Z.of_nat n) (adv_ext (-1) ext)))) in S. 
        rewrite <- S. rewrite IHT1;eauto. rewrite IHT2;eauto. rewrite H0. 
        simpl. reflexivity. constructor;auto. 
        intros. unfold specialiseFun in S'. 
        rewrite <- adv_ext_step in S'. rewrite <- Zneg_of_succ_nat in S'.
        rewrite S' in H. inversion H. repeat rewrite adv_ext_iter.
        assert (Z.neg (Pos.of_succ_nat n) + Z.of_nat (Datatypes.S n) = 
                (-1) + (- Z.of_nat n + Z.pos (Pos.of_succ_nat n)))%Z as E by
        (rewrite Zneg_of_succ_nat; rewrite Zpos_P_of_succ_nat; repeat rewrite Nat2Z.inj_succ; omega) .
        rewrite E. auto. 
      * simpl. rewrite IHT2;auto.
Qed.

Fixpoint elimVarV (v1 v2 : Var) : option Var :=
  match v1, v2 with
    | V1,V1 => None
    | V1,VS v2' => Some v2'
    | VS v1', V1 => Some V1
    | VS v1', VS v2' => liftM VS (elimVarV v1' v2')
  end.

(* Checks whether the given variable occurs in the given expression. *)

Fixpoint elimVarE (v : Var) (e : Exp) : option Exp :=
  match e with
    | OpE op args => liftM (OpE op) (sequence (map (elimVarE v) args))
    | Obs _ _ => Some e
    | VarE v' => liftM VarE (elimVarV v v')
    | Acc e1 l e2 => liftM2 (fun e1' e2' => Acc e1' l e2') (elimVarE (VS v) e1) (elimVarE v e2)
  end.

(* Two internal environments are equivalent up to a variable. *)
Inductive elimVarEnv {A} : Var -> list A -> list A -> Prop :=
  | elimVarEnv_nil v : elimVarEnv v [] []
  | elimVarEnv_V1 r x : elimVarEnv V1 (x::r) r
  | elimVarEnv_VS r1 r2 x v : elimVarEnv v r1 r2 -> 
                                elimVarEnv (VS v) (x::r1) (x::r2).

Hint Constructors elimVarEnv.

Lemma Acc_sem_ext {A} l (e1 e2 : A) f1 f2 : 
  e1 = e2 -> (forall x y, f1 x y = f2 x y) ->  Acc_sem f1 l e1 = Acc_sem f2 l e2.
Proof.
  intros E F. induction l.
  - simpl. assumption.
  - simpl. rewrite IHl. apply F.
Qed.

Lemma elimVarE_sound v vs1 vs2 ext e e': elimVarE v e = Some e' -> elimVarEnv v vs1 vs2 -> 
                                       E[|e|]vs1 ext = E[|e'|]vs2 ext.
Proof.
  intros O U. generalize dependent ext. generalize dependent vs1. generalize dependent vs2.
  generalize dependent v. generalize dependent e'.
  induction e using Exp_ind';intros;simpl in *. 
  - option_inv_auto. simpl. apply bind_equals;auto.
    generalize dependent x. induction H;intros.
    + simpl in H1. inversion H1. reflexivity.
    + simpl in H1. option_inv_auto. simpl. f_equal;eauto.
  - inversion O. reflexivity.
  - option_inv_auto. simpl. generalize dependent v. generalize dependent x.
    induction U;intros.
    + destruct x;destruct v0;reflexivity.
    + destruct v;tryfalse. simpl in *. inversion H0. reflexivity.
    + destruct v0; simpl in *. inversion H0. reflexivity.
      option_inv_auto. simpl. apply IHU. assumption.
  - option_inv_auto. simpl. generalize dependent ext. 
    induction d;intros.
    + simpl in *. eapply IHe2;eauto.
    + rewrite adv_ext_step. simpl. erewrite IHd.
      unfold Fsem. apply bind_equals. apply Acc_sem_ext; auto.
      intros. erewrite IHe1;eauto.
Qed. 

Lemma elimVarE_typed v g1 g2 e e' t: elimVarE v e = Some e' -> elimVarEnv v g1 g2 -> 
                                         g1 |-E e ∶ t -> g2 |-E e' ∶ t.
Proof.
  intros O U T. generalize dependent g1. generalize dependent g2.
  generalize dependent t. generalize dependent e'. generalize dependent v.
  induction e using Exp_ind';intros;simpl in *;first[option_inv' O|inversion O];inversion T;clear T;subst.
  - econstructor;eauto. clear H4. generalize dependent x. induction H6;intros.
    + simpl in H2. inversion H2. constructor.
    + simpl in H2. option_inv' H2. inversion H. subst. constructor; eauto.
  - auto.
  - constructor. generalize dependent v. generalize dependent x. induction U;intros.
    + destruct v0;destruct v;tryfalse; simpl in *; inversion H1;inversion H2;auto.
    + destruct v;tryfalse. simpl in *. inversion H1. inversion H2. subst. assumption.
    + destruct v0; simpl in *. inversion H1. inversion H2. subst. auto.
      option_inv_auto. inversion H2. subst. eauto.
  - constructor;eauto.
Qed. 


Fixpoint elimVarC (v : Var) (c : Contr) : option Contr :=
  match c with
    | Zero => Some c
    | Transfer _ _ _ => Some c
    | Let e c' => liftM2 Let (elimVarE v e) (elimVarC (VS v) c')
    | Scale e c' => liftM2 Scale (elimVarE v e) (elimVarC v c')
    | Translate l c' => liftM (Translate l) (elimVarC v c')
    | Both c1 c2 => liftM2 Both (elimVarC v c1) (elimVarC v c2)
    | If e l c1 c2 => liftM3 (fun e' c1' c2' => If e' l c1' c2') (elimVarE v e) (elimVarC v c1) (elimVarC v c2)
  end.

Lemma elimVarC_sound v vs1 vs2 ext c c' : elimVarC v c = Some c' -> elimVarEnv v vs1 vs2 -> 
                                         C[|c|]vs1 ext = C[|c'|]vs2 ext.
Proof.
  intros O U. generalize dependent ext. generalize dependent vs1. generalize dependent vs2.
  generalize dependent v. generalize dependent c'.
  induction c;intros; simpl in *;try first [option_inv' O|inversion O];simpl;
  try solve [reflexivity|eauto using bind_equals, elimVarE_sound|f_equal;eauto using bind_equals, elimVarE_sound].
  
  generalize dependent ext. induction n;intros;simpl;erewrite elimVarE_sound;eauto;erewrite IHc1;eauto.
  - erewrite IHc2;eauto.
  - erewrite IHn;eauto.
Qed. 


Lemma elimVarC_typed v g1 g2 c c' : elimVarC v c = Some c' -> elimVarEnv v g1 g2 -> 
                                         g1 |-C c -> g2 |-C c'.
Proof.
  intros O U T. generalize dependent g1. generalize dependent g2.
  generalize dependent c'. generalize dependent v.
  induction c;intros;simpl in *;first[option_inv' O|inversion O];inversion T;clear T;subst;
  eauto using elimVarE_typed.
Qed. 



(* Smart contructor for let bindings. If the bound variable of the let
bindings occurs in the given contract, a let binding is constructed
otherwise the input contract is returned. *)

Definition smartLet (e : Exp) (c : Contr) : Contr := 
  match elimVarC V1 c with
    | None => Let e c
    | Some c' => c'
  end.

(* The smart let binding is equivalent to the ordinary let binding. *)

Lemma smartLet_sound e c vs ext t g : 
  g |-E e ∶ t -> TypeEnv g vs -> TypeExt ext -> C[|smartLet e c|]vs ext = C[|Let e c|]vs ext.
Proof.
  intros T G R. unfold smartLet. cases (elimVarC V1 c); try reflexivity.
  simpl.
  eapply Esem_typed_total in T;eauto. decompose [ex and] T.
  rewrite H0. simpl. erewrite <- elimVarC_sound;eauto.
Qed.

Lemma smartLet_typed e c g : 
  g |-C Let e c -> g |-C smartLet e c.
Proof.
  intros T. inversion T. unfold smartLet. cases (elimVarC V1 c); eauto using elimVarC_typed.
Qed.

Corollary smartLet_equiv e c g : 
  g |-C Let e c -> smartLet e c ≡[g] Let e c.
Proof.
  intros. unfold equiv. repeat split; auto. 
  - apply smartLet_typed. assumption.
  - intros. inversion H. eauto using smartLet_sound.
Qed.
   
(* Smart constructor for scaling *)

Definition smartScale e c : Contr :=
  if isZeroLit e then Zero
  else match c with
         | Zero => Zero 
         | c' => Scale e c'
       end.

Lemma smartScale_sound e c vs ext g: 
  g |-C Scale e c -> TypeEnv g vs -> TypeExt ext -> C[|smartScale e c|]vs ext = C[|Scale e c|]vs ext.
Proof.
  intros T G R. inversion T. subst.
  unfold smartScale. cases (isZeroLit e) as E. apply isZeroLit_true in E.
  subst. simpl. eapply Csem_typed_total in H3;eauto. destruct H3. rewrite H. simpl.
  unfold compose. rewrite scale_trace_0. reflexivity.
  destruct c; try reflexivity.
  simpl. eapply Esem_typed_total in H2;eauto. decompose [ex and] H2. rewrite H0.
  inversion H1. simpl. unfold compose. rewrite scale_empty_trace. reflexivity.
Qed.

Lemma smartScale_typed e c g : 
  g |-C Scale e c -> g |-C smartScale e c.
Proof.
  intros T. inversion T. unfold smartScale. cases (isZeroLit e); cases c; eauto.
Qed.


Corollary smartScale_equiv e c g : 
  g |-C Scale e c -> smartScale e c ≡[g] Scale e c.
Proof.
  intros. unfold equiv. repeat split; auto. 
  - apply smartScale_typed. assumption.
  - intros. inversion H. eauto using smartScale_sound.
Qed.
   


Definition smartBoth c1 c2 : Contr :=
  match c1, c2 with
    | Zero, c' => c'
    | c', Zero => c'
    | c1', c2' => Both c1' c2'
  end.


Lemma smartBoth_sound c1 c2 vs ext g: 
  g |-C Both c1 c2 -> TypeEnv g vs -> TypeExt ext -> C[|smartBoth c1 c2|]vs ext = C[|Both c1 c2|]vs ext.
Proof.
  intros T G R. inversion T. subst.
  eapply Csem_typed_total in H2;eauto. destruct H2 as [t1 C1].
  eapply Csem_typed_total in H3;eauto. destruct H3 as [t2 C2].
  destruct c1;destruct c2;unfold smartBoth; simpl in *; unfold compose;try reflexivity;
  try first[rewrite add_empty_trace_l|rewrite add_empty_trace_r]; try reflexivity;
  first[rewrite C1|rewrite C2]; simpl;unfold compose; 
  first[rewrite add_empty_trace_l|rewrite add_empty_trace_r]; try reflexivity.
Qed.

Lemma smartBoth_typed c1 c2 g : 
  g |-C Both c1 c2 -> g |-C smartBoth c1 c2.
Proof.
  intros T. inversion T. destruct c1;destruct c2; simpl; eauto.
Qed.


Corollary smartBoth_equiv c1 c2 g : 
  g |-C Both c1 c2 -> smartBoth c1 c2 ≡[g] Both c1 c2.
Proof.
  intros. unfold equiv. repeat split; auto. 
  - apply smartBoth_typed. assumption.
  - intros. inversion H. eauto using smartBoth_sound.
Qed.


Definition smartTranslate l c : Contr :=
  match l with
    | 0 => c
    | _ => match c with
             | Zero => Zero
             | _ => Translate l c
           end
end.

Lemma smartTranslate_sound l c vs ext: 
  C[|smartTranslate l c|]vs ext = C[|Translate l c|]vs ext.
Proof.
  destruct l.
  - simpl. erewrite liftM_ext. rewrite liftM_id. rewrite adv_ext_0. reflexivity.
    intros. simpl. apply delay_trace_0.
  - destruct c;try reflexivity. simpl. unfold compose. simpl.
    rewrite delay_empty_trace. reflexivity.
Qed.

Lemma smartTranslate_typed l c g : 
  g |-C Translate l c -> g |-C smartTranslate l c.
Proof.
  intros T. inversion T. destruct l;auto;destruct c; auto.
Qed.


Corollary smartTranslate_equiv l c g : 
  g |-C Translate l c -> smartTranslate l c ≡[g] Translate l c.
Proof.
  intros. unfold equiv. repeat split; auto. 
  - apply smartTranslate_typed. assumption.
  - intros. inversion H. eauto using smartTranslate_sound.
Qed.
   

Fixpoint traverseIf (env:EnvP) (ext : ExtEnvP) (e: Exp) (c1 c2 : ExtEnvP -> Contr) (d : nat) (l : nat) : option Contr :=
  match fromBLit (specialiseExp e env ext) with
      | Some true => Some (smartTranslate d (c1 ext))
      | Some false => match l with
                        | O => Some (smartTranslate d (c2 ext))
                        | S l' => traverseIf env (adv_ext 1 ext) e c1 c2 (S d) l'
                        end
      | _ => None
  end.



Fixpoint specialise (c : Contr) (env : EnvP) (ext : ExtEnvP) : Contr :=
  match c with
    | Zero => c
    | Transfer _ _ _ => c
    | Let e c' => let e' := specialiseExp e env ext in
                  smartLet e' (specialise c' (fromLit e' :: env) ext)
    | Scale e c' => smartScale (specialiseExp e env ext) (specialise c' env ext)
    | Translate l c' => smartTranslate l (specialise c' env (adv_ext (Z.of_nat l) ext))
    | Both c1 c2 => smartBoth (specialise c1 env ext) (specialise c2 env ext)
    | If e l c1 c2 => default c (traverseIf env ext e (specialise c1 env) (specialise c2 env) 0 l)
  end.

Hint Resolve smartTranslate_typed smartBoth_typed smartScale_typed 
     smartLet_typed specialiseExp_typed fromLit_typed : SmartTyped.



Theorem specialise_typed g env ext  c : 
  g |-C c -> TypeEnvP g env -> TypeExtP ext -> g |-C specialise c env ext.
Proof.
  intros T E R. generalize dependent env. generalize dependent ext. generalize dependent g. 
  induction c;intros; inversion T;subst;simpl; eauto 9 with SmartTyped.
  (* all cases except If are caught by eauto *)
  match goal with [|-context[default _ ?x]] => cases x as S end;try auto.
  generalize dependent c. generalize dependent ext. generalize 0.
  induction n;intros.
  - simpl in *. cases (fromBLit (specialiseExp e env ext)) as B;tryfalse. 
    destruct b; inversion S; auto with SmartTyped.
  - simpl in *. cases (fromBLit (specialiseExp e env ext)) as B;tryfalse.
    destruct b; inversion S; auto with SmartTyped. apply IHn in S;eauto.
Qed.


Hint Resolve  Esem_fromLit smartTranslate_typed smartBoth_typed smartScale_typed 
     smartLet_typed specialiseExp_typed specialise_typed fromLit_typed smartTranslate_sound 
     smartBoth_sound smartScale_sound  smartLet_sound specialiseExp_sound   : SmartSound.

Lemma Esem_fromBLit e r vs ext : fromBLit e = Some r -> E[|e|]vs ext = Some (BVal r).
Proof.
  intros. apply fromBLit_Some in H. subst. reflexivity.
Qed.

Definition pequiv g envp extp c1 c2 := forall env ext, 
                                        TypeEnv g env -> TypeExt ext -> 
                                        ext_inst extp ext ->
                                        env_inst envp env ->
                                        C[|c1|] env ext = C[|c2|] env ext.

Notation "c1 '≡[' g ',' envp ',' extp ']' c2" := (pequiv g envp extp c1 c2) (at level 50).

Theorem specialise_sound g envp extp  c : 
  g |-C c -> specialise c envp extp ≡[g,envp,extp] c.
Proof.
  unfold pequiv.
  intros T env ext E R I J. generalize dependent env. generalize dependent ext.
  generalize dependent envp. generalize dependent extp. generalize dependent g. 
  induction c;intros; inversion T;subst;simpl; eauto.
  - erewrite smartLet_sound by eauto 9 with SmartSound. simpl. 
    erewrite specialiseExp_sound by eauto. pose H2 as HT. eapply Esem_typed_total in HT;eauto.
    decompose [ex and] HT. rewrite H0. simpl.
    eapply IHc; eauto 9 with SmartSound. constructor. 
    intros. eapply Esem_fromLit in H. erewrite specialiseExp_sound in H; eauto.
    rewrite H0 in H. inversion H. reflexivity. auto.
  - erewrite smartScale_sound by eauto 9 with SmartSound. simpl. erewrite IHc by eauto.
    erewrite specialiseExp_sound by eauto.  reflexivity.
  - erewrite smartTranslate_sound by eauto. simpl. erewrite IHc by eauto. reflexivity.
  - erewrite smartBoth_sound by eauto 9 with SmartSound. simpl. erewrite IHc1 by eauto. 
    erewrite IHc2 by eauto. reflexivity.

  - match goal with [|-context[default _ ?x]] => cases x as S end;try auto.
    generalize dependent c. generalize dependent ext. generalize dependent extp. 
    assert (forall (n0 : nat) (extp : ExtEnvP) (ext : ExtEnv),
              TypeExt (adv_ext (Z.of_nat n0) ext) ->
              ext_inst extp (adv_ext (Z.of_nat n0) ext) ->
              forall c : Contr,
                traverseIf envp extp e (specialise c1 envp) (specialise c2 envp) n0 n =
                Some c ->
                C[|c|] env ext =
                liftM (delay_trace n0) (within_sem C[|c1|] C[|c2|] e n env (adv_ext (Z.of_nat n0) ext))) as G.
    
    induction n;intros;
    simpl in *; pose H3 as HT; eapply Esem_typed_total in HT;eauto;
    decompose [ex and] HT; inversion H7; subst; rewrite H4;
    cases (fromBLit (specialiseExp e envp extp)) as B;tryfalse;
    eapply Esem_fromBLit in B; erewrite specialiseExp_sound in B by eauto;
    rewrite B in H4; inversion H4; subst;
    destruct b; inversion H1; try rewrite smartTranslate_sound; simpl; f_equal; eauto.
    + rewrite liftM_liftM. erewrite liftM_ext.
      rewrite adv_ext_iter'.
      assert (1 + Z.of_nat n0 = Z.of_nat (1 + n0))%Z as Q.
      rewrite Nat2Z.inj_succ. omega. rewrite Q. eapply IHn; eauto. 
      rewrite <- Q. rewrite <- adv_ext_iter'. auto.
      rewrite <- Q. rewrite <- adv_ext_iter'. auto.
      intros. unfold compose. rewrite delay_trace_iter. reflexivity.
    + intros. simpl. erewrite G;eauto;rewrite adv_ext_0;auto. erewrite liftM_ext by (apply delay_trace_0).
      rewrite liftM_id. reflexivity. 
Qed.
