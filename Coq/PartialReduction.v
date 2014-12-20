Require Export Specialise.
Require Import Denotational.
Require Import Advance.
Require Import Tactics.
Require Import FunctionalExtensionality.

(********** Reduction semantics **********)


Inductive scaleTrans : Exp -> Trans -> Trans -> Prop :=
| scaleTrans_empty e : scaleTrans e empty_trans empty_trans
| scaleTrans_scale e v t : fromLit e = Some (RVal v) -> scaleTrans e t (scale_trans v t)
.

Inductive Red : Contr -> EnvP -> ExtEnvP -> Contr -> Trans -> Prop :=
| red_zero env ext : Red Zero env ext Zero empty_trans
| red_let e e' env ext c c' t : e' = specialiseExp e env ext ->
                                     Red c (fromLit e'::env) ext c' t ->
                                    Red (Let e c) env ext (smartLet (adv_exp (-1) e') c') t
| red_transf c p1 p2 env ext : Red (Transfer c p1 p2) env ext Zero (singleton_trans c p1 p2 1)
| red_scale e e' env ext c c' t t' : e' = specialiseExp e env ext -> 
                                   scaleTrans e' t t' -> Red c env ext c' t ->
                                   Red (Scale e c) env ext (smartScale (adv_exp (-1) e') c') t'
| red_trans0 c env ext c' t : Red c env ext c' t -> Red (Translate 0 c) env ext c' t
| red_transS c env ext n : Red (Translate (S n) c) env ext (Translate n c) empty_trans
| red_both c1 c1' c2 c2' env ext t1 t2 : Red c1 env ext c1' t1 -> Red c2 env ext c2' t2 -> 
                         Red (Both c1 c2) env ext (smartBoth c1' c2') (add_trans t1 t2)
| red_if0_false env ext c1 c2 c' b t : fromLit (specialiseExp b env ext) = Some (BVal false) -> 
                                         Red c2 env ext c' t -> Red (If b 0 c1 c2) env ext c' t
| red_ifS_false env ext c1 c2 n b : fromLit (specialiseExp b env ext) = Some (BVal false) -> 
                                       Red (If b (S n) c1 c2) env ext (If b n c1 c2) empty_trans
| red_if_true env ext c1 c2 c' n b t : fromLit (specialiseExp b env ext) = Some (BVal true) -> 
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
  C[|c|] env ext = Some tr -> tr 0 = t.
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
    spec. inversion H2. reflexivity. assumption.
  - unfold scale_trace,compose. option_inv_auto. erewrite IHR;eauto. inversion H0. 
    * apply scale_empty_trans.
    * spec. inversion H1. subst. simpl in H4. inversion H4. reflexivity.
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
    rewrite H8 in H3. inversion H3.  rewrite <- H7 in *. inversion H3. repeat subst.
    rewrite H9 in H6. inversion H6.  unfold scale_trace, compose. f_equal.
    eapply IHR;eauto.
  - option_inv_auto. rewrite delay_trace_0. eapply IHR;eauto.
  - option_inv_auto. rewrite delay_trace_S. f_equal.  rewrite adv_ext_iter in H2.
    rewrite Zpos_P_of_succ_nat in H0. rewrite Z.add_1_l in H2. rewrite H0 in H2. inversion H2. reflexivity.
  - option_inv_auto. erewrite smartBoth_sound in S2;eauto.
    * simpl in S2. option_inv_auto. unfold add_trace,compose. f_equal;eauto.
    * eauto 10 using red_typed.
  - spec. eapply IHR;eauto.
  - spec. option_inv_auto. rewrite delay_trace_S. rewrite delay_trace_0.
    rewrite H1 in S2. inversion S2. reflexivity.
  - spec. eapply IHR;eauto. destruct n; simpl in S1; rewrite H in S1; assumption.
    Qed.
