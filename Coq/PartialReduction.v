Require Export Specialise.
Require Import Denotational.
Require Import Advance.
Require Import Tactics.
Require Import FunctionalExtensionality.
Require Export FinMap.


(********** Reduction semantics **********)


Inductive ScaleTrans : option R -> Trans -> Trans -> Prop :=
| scaleTrans_empty e : ScaleTrans e empty_trans empty_trans
| scaleTrans_scale v t : ScaleTrans (Some v) t (scale_trans v t)
.

Inductive Red : Contr -> EnvP -> ExtEnvP -> Contr -> Trans -> Prop :=
| red_zero env ext t c :t = empty_trans -> c = Zero -> Red Zero env ext c t
| red_let e e' env ext c c' c'' t : e' = specialiseExp e env ext ->
                                     Red c (fromLit e'::env) ext c' t ->
                                     c'' = (smartLet (adv_exp (-1) e') c') ->
                                    Red (Let e c) env ext c'' t
| red_transf c c' t' p1 p2 env ext : c' = Zero -> t' = (singleton_trans c p1 p2 1) -> Red (Transfer c p1 p2) env ext c' t'
| red_scale e e' env ext c c' c'' t t' : e' = specialiseExp e env ext -> 
                                   ScaleTrans (fromRLit e') t t' -> Red c env ext c' t ->
                                   c'' = (smartScale (adv_exp (-1) e') c') ->
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


Theorem red_typed c c' envp extp t g:
  TypeEnvP g envp -> TypeExtP extp -> 
  g |-C c -> Red c envp extp c' t ->  g |-C c'.
Proof.
  intros T1 T2 T R. generalize dependent g.
  induction R;intros;inversion T;subst;
  eauto 10 using smartLet_typed, smartBoth_typed, smartScale_typed, adv_exp_type,specialiseExp_typed, fromLit_typed.
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
    rewrite adv_exp_ext_opp in H2 by reflexivity.
    erewrite specialiseExp_sound in H2;eauto. rewrite H2 in H0. inversion H0. subst. auto.
  - option_inv_auto. spec. erewrite smartScale_sound in S2 by eauto 10 using red_typed.
    simpl in S2. option_inv_auto. rewrite adv_exp_ext_opp in H8 by reflexivity.
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

Import SMap.

Definition lift2M {A B C} (f : A -> B -> C) (x : option (A * B)) : option C 
  := liftM (fun x: (A * B) => let (x1,x2) := x in f x1 x2) x.

Definition scale_trans' (v : option R) (t : SMap) : option SMap :=
  match v with
  | None => if SMap.is_empty t then Some SMap.empty else None
  | Some v => Some (if Reqb v 0 then SMap.empty else  SMap.map (fun x => v * x) t)
  end.

Fixpoint redfun (c : Contr) (env : EnvP) (ext : ExtEnvP) : option (Contr * SMap) :=
  match c with
    | Zero => Some (Zero, SMap.empty)
    | Let e c => let e' := specialiseExp e env ext in
                 liftM (fun ct : Contr * SMap => let (c', t) := ct in (smartLet (adv_exp (-1) e') c', t)) 
                       (redfun c (fromLit e'::env) ext)
    | Transfer c p1 p2 => Some (Zero, SMap.singleton c p1 p2 1)
    | Scale e c => let e' := specialiseExp e env ext
                   in redfun c env ext  >>= 
                      (fun ct => let (c', t) := ct in 
                                 liftM (fun t' => (smartScale (adv_exp (-1) e') c', t'))
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

Lemma smap_fun_singleton p1 p2 a r : smap_fun (singleton p1 p2 a r) = singleton_trans p1 p2 a r.
Proof.
  unfold singleton_trans, smap_fun,find,singleton.
  do 3 (apply functional_extensionality;intro).
  cases (compare x x0) as C1. cases (Party.eqb p1 p2) as P1. reflexivity.
  rewrite compare_eq in C1. subst. 
  cases (Party.eqb p1 x0 && Party.eqb p2 x0 && Asset.eqb a x1) as E1.
  eqb_eq. decompose [and] E1. subst. rewrite Party.eqb_refl in P1.
  tryfalse. reflexivity.
  cases (Party.eqb p1 p2) as P1. rewrite Party.eqb_eq in P1. rewrite <- compare_eq in P1.
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
  cases (Party.eqb p1 p2) as P1. rewrite Party.eqb_eq in P1. rewrite <- compare_eq in P1.
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
  cases (Reqb r 0) as E. rewrite empty_find. apply Reqb_iff in E. subst. 
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


Hint Resolve compact_singleton compact_map compact_union compact_empty.


Lemma redfun_compact c env ext c' m : redfun c env ext = Some (c', m) -> Compact m.
Proof.
  intro R. generalize dependent m. generalize dependent ext. generalize dependent env. 
  generalize dependent c' .
  induction c;intros;simpl in R;try first[option_inv' R|injection R;intros];dprod;option_inv_auto;dprod;
  subst;eauto using R1_neq_R0.
  - cases (fromRLit (specialiseExp e env ext)). simpl in H0. 
    cases (Reqb r 0) as E. inversion H0. auto. rewrite Reqb_iff_false in E. inversion H0. 
    apply compact_map. intros. apply Rmult_integral in H. destruct H. tryfalse. auto.
    eauto.
    simpl in H0. cases (is_empty s) as E. inversion H0. auto. tryfalse.
  - destruct n. eauto. inversion R. auto.
  - destruct n; destruct x;eauto. inversion H2. eauto.
Qed.


Lemma smap_fun_empty_compact m : Compact m -> smap_fun m = empty_trans -> m = SMap.empty.
Proof.
  intros C F. 
  apply empty_find_compact;eauto. intros.
  do 3 eapply equal_f in F.
  unfold smap_fun in F. rewrite F. reflexivity.
Qed.

Hint Resolve redfun_compact smap_fun_empty_compact.


Lemma ScaleTrans_scale_trans (v : option R) t t' m : 
  Compact m ->
  t = smap_fun m -> ScaleTrans v t t' -> exists m', scale_trans' v m = Some m' /\ t' = smap_fun m'.
Proof.
  intros C T S. inversion S. 
  - subst. symmetry in H0. apply smap_fun_empty_compact in H0;auto.
    eexists. split. destruct v. simpl. cases (Reqb r 0). reflexivity.
    subst. rewrite SMap.map_empty. reflexivity. simpl.
    cases (is_empty m). reflexivity. rewrite <- SMap.empty_is_empty in H0. tryfalse.
    rewrite smap_fun_empty. reflexivity.
  - simpl. cases (Reqb v0 0) as R. 
    eexists. split. reflexivity. rewrite Reqb_iff in R. subst.
    rewrite scale_trans_0.     rewrite smap_fun_empty. reflexivity.
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
    unfold pure, compose. rewrite H2. reflexivity. auto. eauto. eauto.
  Qed.


