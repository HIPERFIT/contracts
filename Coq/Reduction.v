Require Import ZArith.
Require Export Specialise.
Require Import Denotational.
Require Import TranslateExp.
Require Import Tactics.
Require Import FunctionalExtensionality.
Require Export FinMap.
Require Import TimedTyping.


(********** reduction semantics **********)

(* This is the reduction relation *)


Inductive ScaleTrans : option R -> Trans -> Trans -> Prop :=
| scaleTrans_empty e : ScaleTrans e empty_trans empty_trans
| scaleTrans_scale v t : ScaleTrans (Some v) t (scale_trans v t)
.

Inductive Red : Contr -> EnvP -> ExtEnvP -> Contr -> Trans -> Prop :=
| red_zero env ext t c :t = empty_trans -> c = Zero -> Red Zero env ext c t
| red_let e e' env ext c c' c'' t : e' = specialiseExp e env ext ->
                                     Red c (fromLit e'::env) ext c' t ->
                                     c'' = (smartLet (translateExp (-1) e') c') ->
                                    Red (Let e c) env ext c'' t
| red_transf c c' t' p1 p2 env ext : c' = Zero -> t' = (singleton_trans c p1 p2 1) -> Red (Transfer c p1 p2) env ext c' t'
| red_scale e e' env ext c c' c'' t t' : e' = specialiseExp e env ext -> 
                                   ScaleTrans (fromRLit e') t t' -> Red c env ext c' t ->
                                   c'' = (smartScale (translateExp (-1) e') c') ->
                                   Red (Scale e c) env ext c'' t'
| red_trans0 c env ext c' t : Red c env ext c' t -> Red (Translate 0 c) env ext c' t
| red_transS c env ext n c' t' : t' = empty_trans -> c' = Translate n c -> Red (Translate (S n) c) env ext c' t'
| red_both c1 c1' c2 c2' env ext t1 t2 c t : Red c1 env ext c1' t1 -> Red c2 env ext c2' t2 -> 
                                             c = smartBoth c1' c2' -> t = add_trans t1 t2 ->
                                             Red (Both c1 c2) env ext c t
| red_if0_false env ext c1 c2 c' b t : fromBLit (specialiseExp b env ext) = Some false -> 
                                         Red c2 env ext c' t -> Red (If b 0 c1 c2) env ext c' t
| red_ifS_false env ext c1 c2 n b c t : fromBLit (specialiseExp b env ext) = Some false -> 
                                    c = If b n c1 c2 -> t = empty_trans -> 
                                       Red (If b (S n) c1 c2) env ext c t
| red_if_true env ext c1 c2 c' n b t : fromBLit (specialiseExp b env ext) = Some true -> 
                                         Red c1 env ext c' t -> Red (If b n c1 c2) env ext c' t
.

(* N.B. If rule red_ifS_false used (specialiseExp b env ext) for the
result contract, the rule would be unsound. *)

Hint Constructors Red.

Module Preservation.

  (* Proof of type preservation by Red *)

Lemma red_typed c c' envp extp t g:
  TypeEnvP g envp -> TypeExtP extp -> 
  g |-C c -> Red c envp extp c' t ->  g |-C c'.
Proof.
  intros T1 T2 T R. generalize dependent g.
  induction R;intros;inversion T;subst;
  eauto 10 using smartLet_typed, smartBoth_typed, smartScale_typed, translateExp_type,specialiseExp_typed, fromLit_typed.
Qed.

End Preservation.

Import Preservation.

Module Soundness.

  (* Proof of soundness of Red according to denotational semantics *)

Theorem red_sound1 c c' env ext envp extp tr t g: 
  g |-C c ->
      TypeEnv g env -> TypeExt ext -> 
  Red c envp extp c' t ->  
  ext_inst extp ext ->
  env_inst envp env ->
  C[|c|] env ext = Some tr -> tr O = t.
Proof.

  Ltac spec := repeat match goal with 
                  | [T: fromRLit _ = Some _ |- _ ] => apply fromRLit_fromLit in T
                  | [T: fromBLit _ = Some _ |- _ ] => apply fromBLit_fromLit in T
                  | [T: fromLit _ = Some _ |- _ ] => eapply specialise_fromLit in T;eauto; try rewrite T in *
               end.
  intros T E X R I J S. 
  generalize dependent env. generalize dependent ext. generalize dependent g. generalize dependent tr.
  induction R;intros; simpl in S; try option_inv' S; try solve [inversion S;auto|auto];inversion T;clear T;subst.
  - eapply IHR;eauto. eauto using Esem_typed  . constructor. intros.
    spec. inversion H3. reflexivity. assumption.
  - unfold scale_trace,compose. option_inv_auto. erewrite IHR;eauto. inversion H0. 
    * apply scale_empty_trans.
    * symmetry in H3. spec. inversion H1. subst. simpl in H2. inversion H2. reflexivity.
  - erewrite <- IHR;eauto. rewrite adv_ext_0 in H1. rewrite delay_trace_0. assumption.
  - unfold add_trace. erewrite <- IHR1;eauto. erewrite <- IHR2;eauto.
  - spec. eapply IHR;eauto. 
  - spec. option_inv_auto. reflexivity.
  - spec. eapply IHR;eauto. destruct n; simpl in S; rewrite H in S;assumption.
Qed.


Theorem red_sound2 c c' env ext envp extp t t1 t2 i g: 
  g |-C c ->
      TypeEnv g env -> TypeExt ext -> 
  Red c envp extp c' t ->  
  ext_inst extp ext ->
  env_inst envp env ->
  C[|c|]env ext = Some t1 -> C[|c'|] env (adv_ext 1 ext) = Some t2
  -> t1 (S i) = t2 i.
Proof.
  intros T E X R I J S1 S2. generalize dependent t1. generalize dependent t2. generalize dependent env. 
  generalize dependent ext. generalize dependent g.
  induction R; simpl in *;intros;inversion T;clear T;subst;try solve [inversion S1;inversion S2;eauto].
  - option_inv_auto. eapply IHR;eauto. 
    eauto using Esem_typed.  
    constructor. intros. spec. inversion H0. reflexivity. auto. 
    erewrite smartLet_sound in S2;eauto. simpl in S2. option_inv_auto.
    rewrite translateExp_ext_opp in H2 by reflexivity.
    erewrite specialiseExp_sound in H2;eauto. rewrite H2 in H0. inversion H0. subst. auto.
  - option_inv_auto. spec. erewrite smartScale_sound in S2 by eauto 10 using red_typed.
    simpl in S2. option_inv_auto. rewrite translateExp_ext_opp in H8 by reflexivity.
    erewrite specialiseExp_sound in H8;eauto. 
    unfold scale_trace, compose. erewrite IHR by eauto. f_equal. 
    rewrite H8 in H3. inversion H3. subst. rewrite H9 in H4. inversion H4. reflexivity.
  - option_inv_auto. rewrite delay_trace_0. eapply IHR;eauto.
  - option_inv_auto. simpl in S2. option_inv_auto. rewrite delay_trace_S. f_equal.  rewrite adv_ext_iter in H1.
    rewrite Zpos_P_of_succ_nat in H0. rewrite Z.add_1_l in H1. rewrite H0 in H1. inversion H1. reflexivity.
  - option_inv_auto. erewrite smartBoth_sound in S2;eauto.
    * simpl in S2. option_inv_auto. unfold add_trace,compose. f_equal;eauto.
    * eauto 10 using red_typed.
  - spec. eapply IHR;eauto.
  - spec. option_inv_auto. rewrite delay_trace_S. rewrite delay_trace_0. simpl in S2.
    rewrite H1 in S2. inversion S2. reflexivity.
  - spec. eapply IHR;eauto. destruct n; simpl in S1; rewrite H in S1; assumption.
    Qed.

End Soundness.
Import Soundness.

Module Progress.

  (* Proof of progress of Red *)

Open Scope time.

Definition ext_def_until (ext : ExtEnvP) t := 
  forall l i, Time i <= t -> exists v, ext l i = Some v.

Definition env_def_until (env : EnvP) ts t := 
  all2 (fun v t' => time t' <= t -> exists v', v = Some v' /\ TypeVal v' (type t')) env ts.


Lemma fromLit_toLit v : fromLit (toLit v) = Some v.
Proof.
  destruct v;reflexivity.
Qed.

Lemma lookupEnvP_complete env tis ti v t:  
  time ti <= t -> env_def_until env tis t -> TiTyV tis ti v
  -> exists v', lookupEnvP v env = Some v' /\ TypeVal v' (type ti).
Proof.
  intros M E T. generalize dependent env. 
  induction T;intros;
  inversion E; subst; simpl; try rewr_assumption; eauto.
Qed.


Lemma add_time_0 t : add_time 0 t = t.
Proof.
  destruct t. destruct ti; simpl; try rewrite Z.add_0_r; reflexivity. 
Qed.

Lemma map_add_time_0 ts : map (add_time 0) ts = ts.
Proof.
  erewrite map_ext. apply map_id. intros. auto using add_time_0.
Qed.


Lemma adv_ext_def_until ext t d : 
  ext_def_until ext t ->
  ext_def_until (adv_ext (- Z.of_nat d) ext) (tadd' d t).
Proof.
  unfold ext_def_until. intros E. intros l i L. unfold adv_ext.
  assert (Time (- Z.of_nat d + i) <= t) as L'
  by (destruct t; simpl in *;inversion L; subst; constructor; omega).
  eapply E in L'. decompose [ex] L'. rewr_assumption. eauto.
Qed.

Lemma add_time_tle s t d : tadd' d s <= tadd' d t -> s <= t.
Proof.
  intro T. destruct s, t; simpl in *;inversion T;subst;constructor;omega.
Qed.

Lemma env_def_until_add_time d env ti tis :  
  env_def_until env tis ti
  -> env_def_until env (map (add_time d) tis) (tadd' d ti).
Proof.
  unfold env_def_until. intros.
  rewrite <- map_id with (l:=env). apply all2_map'. eapply all2_impl in H. 
  apply H. simpl. intros. rewrite type_add_time. rewrite time_add_time in *.
  eauto using add_time_tle.
Qed.


Lemma ext_def_until_adv d ext ti : 
  (d <= 0)%Z -> ext_def_until ext ti -> ext_def_until (adv_ext d ext) ti.
Proof.
  unfold ext_def_until. intros L E l i Tl. 
  assert (Time (d+i) <= ti) as Tl' by (inversion Tl; subst; constructor; omega).
  eauto.
Qed.

Lemma ext_def_until_step ext ti : ext_def_until ext ti -> ext_def_until (adv_ext (-1) ext) ti.
Proof.
  intros. apply ext_def_until_adv. omega. assumption.
Qed.


Lemma ext_def_until_tle t t' ext : t' <= t -> ext_def_until ext t -> ext_def_until ext t'.
Proof.
  unfold ext_def_until. eauto. 
Qed.

Lemma env_def_until_tle ts t t' env : t' <= t -> env_def_until env ts t -> env_def_until env ts t'.
Proof.
  unfold env_def_until. intros l T. induction T;eauto.
Qed.

Lemma fromLit_real x : (exists v, fromLit x = Some v /\ TypeVal v REAL) -> exists v, x = OpE (RLit v) nil.
Proof.
  intro E. destruct E as [v E]. destruct E as [E1 E2]. inversion E2. subst.
  apply toLit_fromLit in E1. subst. simpl. eauto.
Qed.

Lemma fromLit_bool x : (exists v, fromLit x = Some v /\ TypeVal v BOOL) -> exists v, x = OpE (BLit v) nil.
Proof.
  intro E. destruct E as [v E]. destruct E as [E1 E2]. inversion E2. subst.
  apply toLit_fromLit in E1. subst. simpl. eauto.
Qed.


Ltac inv := match goal with
              | [T : all2 _  _ _ |- _] => inversion T; clear T;subst
              | [T : _ |- _] => first [apply fromLit_bool in T|apply fromLit_real in T];
                               let x := fresh in destruct T as [x T];rewrite T;clear T
              | [t : Ty |- _] => destruct t
              | [ |- context[match ?x with _ => _ end]] => destruct x
end.

Lemma specialiseOp_complete ts ti args op env ext : 
  |-Op op ∶ ts => ti
  -> all2 (fun (e' : Exp) t' =>
             exists v : Val,
               fromLit (specialiseExp e' env ext) = Some v /\ |-V v ∶ t')  args ts
  -> exists v,  (specialiseOp op (map (fun e' : Exp => specialiseExp e' env ext) args)) >>= fromLit = Some v
               /\ TypeVal v ti.
Proof.
  intros TO As. destruct TO;repeat (inv;subst; simpl;eauto).
Qed.

(* [specialiseExp] always yields a literal, if given sufficiently
defined environments. *)

Lemma specialiseExp_complete t tis ti e ext env : 
  time ti <= t -> TiTyE tis ti e -> ext_def_until ext t -> env_def_until env tis t -> TypeExtP ext
  -> exists v, fromLit (specialiseExp e env ext) = Some v /\ TypeVal v (type ti).
Proof.
  intros M T Ti E TE. 
  generalize dependent env.   generalize dependent ext. 
  generalize dependent ti. generalize dependent tis. generalize t.
  induction e using Exp_ind';intros.
  - inversion T. subst. clear T. simpl.
    assert (all2 (fun e' t' => exists v, fromLit (specialiseExp e' env ext) = Some v
                                               /\ TypeVal v t') args (map type ts')) as G.
    inversion H4. subst. clear H4 H1.
    induction H5;constructor.
    + inversion H. inversion H0. subst. eapply H4;eauto; rewr_assumption;
      eauto using ext_def_until_tle, env_def_until_tle.
    + inversion H0. inversion H. subst. apply IHall2;  eauto. 
    + clear H. inversion H4. eapply specialiseOp_complete in G;eauto.
      destruct G as [v G]. destruct G as [G1 G2]. option_inv G1. rewr_assumption.
      simpl. eauto.
  - inversion T. subst. assert (exists v, ext l i = Some v) as D by eauto.
    decompose [ex] D. simpl. rewr_assumption. simpl. 
    assert (TypeVal' (ext l i) (type ti)) as T' by eauto.
    rewr_assumption in T'. inversion T'. eauto using fromLit_toLit. 
  - assert (exists v', lookupEnvP v env = Some v' /\ TypeVal v' (type ti)) as Hv
      by (inversion T; subst; eauto using lookupEnvP_complete).
    decompose [ex and] Hv. simpl. rewr_assumption. simpl. eauto using fromLit_toLit.
  - simpl. inversion T. subst. clear T. pose Ti as Ti'.
    apply adv_ext_def_until with (d:=d) in Ti'. 
    eapply IHe2 in Ti';try rewrite time_add_time; eauto using env_def_until_add_time.
    decompose [ex and] Ti'. clear Ti'. rewrite type_add_time in *. rewr_assumption. 
    assert (exists v : Val,
             Acc_sem
                (specialiseFun (specialiseExp e1) env
                   (adv_ext (- Z.of_nat d) ext)) d 
                (Some x) = Some v /\ |-V v ∶ type ti) as G.
    clear H0 H3.
    generalize dependent env. generalize dependent ext. induction d;intros. 
    + simpl in *. eauto.
    + simpl. pose E as E'. eapply IHd with (ext:=adv_ext (-1) ext) in E';eauto using ext_def_until_step.
      decompose [ex and] E'. repeat rewrite adv_ext_step'.
      rewr_assumption. unfold specialiseFun.
      eapply all2_cons with (y:=type ti @ TimeBot) in E;eauto. 
      eapply IHe1 in E;eauto.
      rewrite H0 in *. auto. rewrite <- adv_ext_step. rewrite adv_ext_opp by omega. assumption. 
    + decompose [ex and] G. rewr_assumption. simpl. eauto using fromLit_toLit. 
Qed.
  
Lemma tsub'_0 t: tsub' 0 t = t.
Proof.
  destruct t;simpl;f_equal. omega. reflexivity.
Qed.

Lemma map_sub_time_0 ts : map (sub_time 0) ts = ts.
Proof.
  erewrite map_ext. apply map_id. intros. destruct a. destruct ti; simpl; repeat f_equal. omega.
Qed.

Lemma fromLit_fromRLit e : 
  (exists v, fromLit e = Some v /\ TypeVal v REAL)
  -> exists r, fromRLit e = Some r.
Proof.
  intro E. decompose [ex and] E. destruct e;tryfalse. destruct op, args;tryfalse;simpl in *;eauto.
  inversion H0. subst. inversion H1. 
Qed.


Lemma fromLit_fromBLit e : 
  (exists v, fromLit e = Some v /\ TypeVal v BOOL)
  -> exists b, fromBLit e = Some b.
Proof.
  intro E. decompose [ex and] E. destruct e;tryfalse. destruct op, args;tryfalse;simpl in *;eauto.
  inversion H0. subst. inversion H1. 
Qed.


Definition mk_env_inst : TyEnv -> EnvP -> Env := 
  zipWith (fun t v => match v with
                  | Some v' => v'
                  | None => match t with
                              | BOOL => BVal false
                              | REAL => RVal 0
                            end
                      end).

Lemma mk_env_inst_env_inst env tys : TypeEnvP tys env -> env_inst env (mk_env_inst tys env).
Proof.
  intros T. induction T;constructor;eauto. intros. destruct x; congruence.
Qed.


Lemma mk_env_inst_typed env tys : TypeEnvP tys env -> TypeEnv tys (mk_env_inst tys env).
Proof.
  intros T. induction T;constructor;eauto. intros. destruct x. inversion H. auto.
  destruct y;eauto.
Qed.  

Definition mk_ext_inst (ext : ExtEnvP) : ExtEnv
  := fun l i => match ext l i with
                  | Some v => v
                  | None => match l with
                              | LabB _ => BVal false
                              | LabR _ => RVal 0
                            end
                end.


Lemma mk_ext_inst_ext_inst ext : ext_inst ext (mk_ext_inst ext).
Proof.
  unfold ext_inst, mk_ext_inst. intros. rewr_assumption. reflexivity.
Qed.


Lemma mk_ext_inst_typed ext: TypeExtP ext -> TypeExt (mk_ext_inst ext).
Proof.
  unfold TypeExt, TypeExtP, mk_ext_inst. intros. 
  cases (ext l z) as E. assert (|-V' Some v ∶ t) as V. rewr_assumption. eauto.
  inversion V. auto. destruct H0;auto.
Qed.

Hint Resolve mk_ext_inst_ext_inst mk_env_inst_env_inst mk_ext_inst_typed mk_env_inst_typed : inst.

Lemma red_empty tis ti ext env c c' t' : 
  Time 0 < ti -> TypeEnvP (map type tis) env -> TypeExtP ext -> TiTyC tis ti c -> 
  Red c env ext c' t' -> t' = empty_trans.
Proof.
  intros L Tv Tx Tc R.
  rewrite TiTyC_decompose in Tc. destruct Tc as [Tc1 Tc2].
  inversion L. subst.
  pose Tc1 as Tc1'.
  apply Csem_typed_total 
  with (env := mk_env_inst (map type tis) env)
       (ext := mk_ext_inst ext) in Tc1';
    eauto with inst. 
  unfold total_trace in *. destruct Tc1' as [t Tc1'].
  pose Tc1' as S.
  eapply red_sound1 in S;eauto with inst.
  eapply CausalC_empty in Tc1';eauto. rewrite Tc1' in S. auto. simpl. auto.
Qed.

Lemma tle_tlt x y z: x <= y -> y < z -> x < z.
Proof.
  intros X Y. destruct X. destruct Y; constructor. inversion Y;subst. inversion Y. subst.
  constructor. omega.
Qed.

Theorem red_progress ti ti' tis c env ext : 
  Time 0 <= ti -> TiTyC tis ti' c
  -> ext_def_until ext ti -> env_def_until env tis ti -> TypeExtP ext -> TypeEnvP (map type tis) env
  -> exists c' t', Red c env ext c' t'.
Proof.
  intros Ti T Ex Ev Te Tv.
  generalize dependent env. generalize dependent ext. 
  induction T; simpl; intros;eauto.
  - (* Translate *)
    destruct d; eauto.
    assert (exists c' t', Red c env ext c' t') as IH by
        (eapply IHT; try rewrite tsub'_0;try rewrite map_sub_time_0;eauto).
    decompose [ex] IH. do 2 eexists. eauto. 
  - (* Let *)
    assert (exists c' t', Red c (fromLit (specialiseExp e env ext) :: env) ext c' t') as IH
    by (eapply IHT;eauto; constructor;eauto using specialiseExp_complete;
        rewrite TiTyE_decompose in H; destruct H; eauto using fromLit_typed,specialiseExp_typed).
    decompose [ex] IH. do 2 eexists. econstructor;eauto.
  - (* Scale *)
    assert (exists c' t', Red c env ext c' t') as IH by (eapply IHT;eauto).
    decompose [ex] IH.
    cases (ti0 <=? ti) as TL.
    * rewrite tleb_tle in TL.
      eapply specialiseExp_complete in H;eauto.
      apply fromLit_fromRLit in H. decompose [ex] H.
      do 2 eexists. econstructor;eauto.
      rewr_assumption. constructor.
    * rewrite tleb_tgt in TL.
      assert (Time 0 < ti0) as Ti' by eauto using tle_tlt.
      assert (x0 = empty_trans) as Em. 
      eauto using red_empty. subst.
      do 2 eexists. econstructor;eauto.
      eapply scaleTrans_empty.
  - (* Both *)
    assert (exists c' t', Red c1 env ext c' t') as IH1 by (eapply IHT1;eauto).
    assert (exists c' t', Red c2 env ext c' t') as IH2 by (eapply IHT2;eauto).
    decompose [ex] IH1. decompose [ex] IH2. eauto.
  - (* If *)
    eapply specialiseExp_complete in H;simpl;eauto. 
    apply fromLit_fromBLit in H. destruct H as [b H].
    destruct b. 
    + assert (exists c' t', Red c1 env ext c' t') as IH1 by (eapply IHT1;eauto).
      decompose [ex] IH1. eapply red_if_true in H;eauto.
    + destruct d.
      * assert (exists c' t', Red c2 env ext c' t') as IH2 by
          (eapply IHT2;try rewrite tsub'_0;try rewrite map_sub_time_0;eauto). 
        decompose [ex] IH2.
        eapply red_if0_false in H;eauto.
      * eapply red_ifS_false in H;eauto.
Qed.


End Progress.


Module Compute.

  (* Define Red as a computable function redfun and prove it correct  *)

Open Scope R.
Import SMap.

Definition lift2M {A B C} (f : A -> B -> C) (x : option (A * B)) : option C 
  := liftM (fun x: (A * B) => let (x1,x2) := x in f x1 x2) x.



Program Definition scale_trans' (v : option R) (t : SMap) : option SMap :=
  match v with
  | None => if SMap.is_empty t then Some SMap.empty else None
  | Some v => Some (if Req_dec v 0 then SMap.empty else  SMap.map (fun x => v * x) _ t)
  end.

Next Obligation. 
apply Rmult_integral in H0. destruct H0. tryfalse. assumption.
Qed.  
  



(* Computable function that implements the reduction semantics. *)

Fixpoint redfun (c : Contr) (env : EnvP) (ext : ExtEnvP) : option (Contr * SMap) :=
  match c with
    | Zero => Some (Zero, SMap.empty)
    | Let e c => let e' := specialiseExp e env ext in
                 liftM (fun ct : Contr * SMap => let (c', t) := ct in (smartLet (translateExp (-1) e') c', t)) 
                       (redfun c (fromLit e'::env) ext)
    | Transfer c p1 p2 => Some (Zero, SMap.singleton c p1 p2 1 R1_neq_R0)
    | Scale e c => let e' := specialiseExp e env ext
                   in redfun c env ext  >>= 
                      (fun ct => let (c', t) := ct in 
                                 liftM (fun t' => (smartScale (translateExp (-1) e') c', t'))
                                       (scale_trans' (fromRLit e') t))
    | Translate n c => match n with
                         | O => redfun c env ext
                         | S n' => Some (Translate n' c, SMap.empty)
                       end
    | Both c1 c2 =>  liftM2 (fun (ct1 ct2 : Contr * SMap) => let (c1',t1) := ct1 in 
                                     let (c2',t2) := ct2 
                                     in (smartBoth c1' c2', SMap.union_with Rplus t1 t2))
                         (redfun c1 env ext) (redfun c2 env ext)
    | If b n c1 c2 => fromBLit (specialiseExp b env ext) >>=
                               (fun b' => if b' then redfun c1 env ext 
                                          else match n with
                                                 | O => redfun c2 env ext 
                                                 | S n' => Some (If b n' c1 c2,SMap.empty)
                                               end)
  end.


Definition smap_fun (m:SMap) (p1 p2 : Party) (a : Asset) : R := SMap.find p1 p2 a m.
Definition smap_fun_eq (m:SMap) f := forall p1 p2 a, SMap.find p1 p2 a m = f p1 p2 a.

Lemma smap_fun_empty : smap_fun SMap.empty = empty_trans.
Proof.
 do 3 (apply functional_extensionality;intro). unfold smap_fun.
 rewrite empty_find. reflexivity.
Qed.

Ltac eqb_eq := repeat rewrite andb_true_iff in *;repeat rewrite Party.eqb_eq in *; repeat rewrite Asset.eqb_eq in *.
Ltac eqb_refl := repeat rewrite Party.eqb_refl in *; repeat rewrite Asset.eqb_refl in *.

Lemma smap_fun_singleton p1 p2 a r p : smap_fun (singleton p1 p2 a r p) = singleton_trans p1 p2 a r.
Proof.
  unfold singleton_trans, smap_fun,find,singleton.
  do 3 (apply functional_extensionality;intro).
  cases (compare x x0) as C1. cases (Party.eqb p1 p2) as P1. reflexivity.
  rewrite compare_eq in C1. subst. 
  cases (Party.eqb p1 x0 && Party.eqb p2 x0 && Asset.eqb a x1) as E1.
  eqb_eq. decompose [and] E1. subst. rewrite Party.eqb_refl in P1.
  tryfalse. reflexivity.
  cases (Party.eqb p1 p2) as P1;simpl. rewrite Party.eqb_eq in P1. rewrite <- compare_eq in P1.
  rewrite P1. rewrite FMap.empty_find. reflexivity. 
  cases (compare p1 p2) as C2. rewrite compare_eq in C2. subst. rewrite Party.eqb_refl in P1. tryfalse.
  cases (FMap.find (x, x0, x1) (FMap.singleton (p1, p2, a) r)) as F1.
  apply FMap.find_singleton in F1. destruct F1 as [F1 F1']. inversion F1. subst.
  eqb_refl. reflexivity.  apply FMap.find_singleton_not in F1.
  cases (Party.eqb p1 x && Party.eqb p2 x0 && Asset.eqb a x1) as E1.
  eqb_eq. decompose [and] E1. subst. tryfalse.
  cases (Party.eqb p1 x0 && Party.eqb p2 x && Asset.eqb a x1) as E2.
  eqb_eq. decompose [and] E2. subst. rewrite compare_lt_gt in C1. tryfalse. reflexivity.
  cases (FMap.find (x, x0, x1) (FMap.singleton (p1, p2, a) (- r))) as F1.
  apply FMap.find_singleton in F1. destruct F1 as [F1 F1']. inversion F1. subst.
  tryfalse. apply FMap.find_singleton_not in F1.
  cases (Party.eqb p1 x && Party.eqb p2 x0 && Asset.eqb a x1) as E1.
  eqb_eq. decompose [and] E1. subst. tryfalse.
  cases (Party.eqb p1 x0 && Party.eqb p2 x && Asset.eqb a x1) as E2.
  eqb_eq. decompose [and] E2. subst. unfold FMap.singleton. 
  rewrite FMap.add_find_new. reflexivity.
  cases (FMap.find (x, x0, x1) (FMap.singleton (p2, p1, a) (- r))) as F2.
  apply FMap.find_singleton in F2. destruct F2. inversion H. subst.
  eqb_refl. tryfalse. reflexivity.
  
  rewrite <- compare_lt_gt in C1.
  cases (Party.eqb p1 p2) as P1;simpl. rewrite Party.eqb_eq in P1. rewrite <- compare_eq in P1.
  rewrite P1. rewrite FMap.empty_find. reflexivity. 
  cases (compare p1 p2) as C2. rewrite compare_eq in C2. subst. rewrite Party.eqb_refl in P1. tryfalse.
  cases (FMap.find (x0, x, x1) (FMap.singleton (p1, p2, a) r)) as F1.
  apply FMap.find_singleton in F1. destruct F1 as [F1 F1']. inversion F1. subst.
  cases (Party.eqb x0 x && Party.eqb x x0 && Asset.eqb x1 x1) as E1.
  eqb_eq. decompose [and] E1. subst x. rewrite <- compare_eq in H2. tryfalse.
  cases (Party.eqb x0 x0 && Party.eqb x x && Asset.eqb x1 x1). reflexivity.
  eqb_refl. tryfalse. apply FMap.find_singleton_not in F1.
  cases (Party.eqb p1 x && Party.eqb p2 x0 && Asset.eqb a x1) as E1. eqb_eq.
  decompose [and] E1. subst. rewrite compare_lt_gt in C1. tryfalse.
  cases (Party.eqb p1 x0 && Party.eqb p2 x && Asset.eqb a x1) as E2. eqb_eq. 
  decompose [and] E2. subst. tryfalse. reflexivity.
  cases (FMap.find (x0, x, x1) (FMap.singleton (p2, p1, a) (- r))) as F1.
  apply FMap.find_singleton in F1. destruct F1 as [F1 F1']. inversion F1. subst.
  eqb_refl. simpl. apply Ropp_involutive.
  apply FMap.find_singleton_not in F1.
  cases (Party.eqb p1 x && Party.eqb p2 x0 && Asset.eqb a x1) as E1. eqb_eq.
  decompose [and] E1. subst. tryfalse. 
  cases (Party.eqb p1 x0 && Party.eqb p2 x && Asset.eqb a x1) as E2. eqb_eq.
  decompose [and] E2. subst. tryfalse. reflexivity.
Qed.

Hint Constructors Red.

Ltac dprod := repeat match goal with
                       | [_: context[let (_,_) := ?x in _] |- _] => is_var x; destruct x
                       | [T: (_,_)=(_,_) |- _] => inversion T;clear T
                     end.

Lemma scale_trans_ScaleTrans (v : option R) t t' m m' : 
  t' = smap_fun m' -> t = smap_fun m -> scale_trans' v m = Some m' -> ScaleTrans v t t'.
Proof.
  intros. destruct v. simpl in H1. inversion H1;clear H1. assert (t' = scale_trans r t) as S.
  subst. unfold smap_fun, scale_trans. repeat (apply functional_extensionality;intro).
  cases (Req_dec r 0) as E. rewrite empty_find. subst. 
  rewrite Rmult_0_r. reflexivity.
  rewrite map_find. apply Rmult_comm. apply Rmult_0_r. intros. rewrite Ropp_mult_distr_r_reverse.
  reflexivity. rewrite S. econstructor.
  simpl in H1. cases (is_empty m) as R. inversion H1.
  rewrite empty_is_empty in R. subst. rewrite smap_fun_empty. constructor.
  tryfalse.
Qed.

Lemma smap_fun_add m1 m2 :  smap_fun (union_with Rplus m1 m2) = add_trans (smap_fun m1) (smap_fun m2).
Proof.
  unfold smap_fun, add_trans. repeat (apply functional_extensionality;intro). apply union_find.
Qed.


Theorem redfun_red c c' env ext t: 
  redfun c env ext = Some (c', t) -> Red c env ext c' (smap_fun t) .
Proof.
  intro F. generalize dependent t. generalize dependent c'. 
  generalize dependent ext. generalize dependent env. 
  induction c;intros;simpl in *;try first[option_inv' F|injection F;intros];dprod;option_inv_auto;dprod;subst;
  eauto using smap_fun_empty, smap_fun_singleton, scale_trans_ScaleTrans, smap_fun_add.
  - destruct n; inversion F; auto using smap_fun_empty.
  - destruct x. auto. destruct n. auto. inversion H2. auto using smap_fun_empty.
Qed.


Lemma smap_fun_empty_compact m : smap_fun m = empty_trans -> m = SMap.empty.
Proof.
  destruct m as [M C]. intro F. 
  apply empty_find_compact;eauto. intros.
  do 3 eapply equal_f in F.
  unfold smap_fun in F. rewrite F. reflexivity.
Qed.


Lemma ScaleTrans_scale_trans (v : option R) t t' m : 
  t = smap_fun m -> ScaleTrans v t t' -> exists m', scale_trans' v m = Some m' /\ t' = smap_fun m'.
Proof.
  intros T S. inversion S. 
  - subst. symmetry in H0. apply smap_fun_empty_compact in H0;auto.
    eexists. split. destruct v. simpl. cases (Req_dec r 0). reflexivity.
    rewrite -> H0. rewrite SMap.map_empty. reflexivity. simpl.
    cases (is_empty m). reflexivity. rewrite <- SMap.empty_is_empty in H0. tryfalse.
    rewrite smap_fun_empty. reflexivity.
  - simpl. cases (Req_dec v0 0) as R. 
    eexists. split. reflexivity. subst.
    rewrite scale_trans_0. rewrite smap_fun_empty. reflexivity.
    eexists. split. reflexivity. subst. unfold smap_fun, scale_trans.
    do 3 (apply functional_extensionality;intro). rewrite map_find. apply Rmult_comm.
    apply Rmult_0_r. intros. rewrite Ropp_mult_distr_r_reverse. reflexivity.
Qed.


Theorem red_redfun c c' env ext t: 
  Red c env ext c' t -> exists m, redfun c env ext = Some (c', m) /\ smap_fun m = t.
Proof.
  intro F. induction F; subst; 
  repeat match goal with | [T : exists _, _ /\ _ |- _] => decompose [ex and] T; clear T;subst end;
  try solve[eexists;split;simpl;try reflexivity;eauto using smap_fun_empty,smap_fun_singleton, smap_fun_add;
  repeat match goal with | [T : _ = Some _ |- _] => rewrite T; clear T end; 
  simpl;unfold pure,compose;simpl;try reflexivity].
  (* we only need to deal with scale *)
  - eapply ScaleTrans_scale_trans in H0. decompose [ex and] H0.
    eexists. split. simpl. rewrite H1. simpl.
    rewrite H3. simpl.
    unfold pure, compose. rewrite H2. reflexivity. auto. eauto. 
  Qed.

End Compute.
