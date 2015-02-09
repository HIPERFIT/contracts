Require Import ZArith.
Require Import Syntax.
Require Import Causality.
Require Import ContextualCausality.
Require Import TimedTyping.


Axiom time_obs : RealObs.

Definition time := LabR time_obs.

Import ListNotations.

Definition IfBind b d c1 c2 := Let (Obs time 0) (If b d (Let (OpE Sub [Obs time 0; VarE V1]) c1) c2).



Lemma IfBind_type ts t d e c1 c2 : 
  (forall t', TiTyE (t' :: ts) (BOOL @ Time 0) e)
  -> (forall t', TiTyC (REAL @ Time 0 :: t' :: ts) t c1)
  -> (forall t', TiTyC (map (sub_time d) (t' :: ts)) (tsub' d t) c2)
  -> TiTyC ts t (IfBind e d c1 c2).
Proof.
  intros. unfold IfBind.
  apply causal_let with (t':= REAL @ Time 0). 
  econstructor;eauto. econstructor.
  apply causal_if;eauto.
  eapply causal_let;eauto. apply causal_op with (ts':=[REAL @ Time 0;REAL @ Time 0]). 
  econstructor; eauto. eauto. econstructor. econstructor; eauto. econstructor.
  eauto.
Qed.