Require Import Denotational.
Require Import Tactics.

(* advancing contracts and expressions *)

Fixpoint adv_exp {V t} (d : Z) (e : exp' V t) : exp' V t :=
  match e with
    | Lit _ _ r => Lit r
    | BinOpE _ _ _ op e1 e2 => BinOpE op (adv_exp d e1) (adv_exp d e2)
    | UnOpE _ _ _ op e' => UnOpE op (adv_exp d e')
    | Obs ty _ o i => Obs ty o (d + i)%Z
    | IfE _ _ b e1 e2 => IfE (adv_exp d b) (adv_exp d e1) (adv_exp d e2)
    | VarE _ _ a => VarE a
    | Acc _ _ f n z => Acc (adv_exp d f) n (adv_exp d z)
  end.



Ltac rewr_assumption := idtac; match goal with
                          | [R:  _ |- _ ] => rewrite R
                        end.

Lemma adv_exp_ext' {V t} (vars : Env (option ∘ TySem) V) d (e : exp' V t) rho : 
  E'[|adv_exp d e|] vars rho = E'[|e|] vars (adv_ext d rho).
Proof.
  generalize dependent rho. 
  induction e;intros; simpl; 
  try solve [repeat rewr_assumption; reflexivity].
  
  assert (adv_ext (- Z.of_nat n) (adv_ext d rho) = adv_ext d (adv_ext (- Z.of_nat n) rho)) as J.
  repeat rewrite adv_ext_iter. f_equal. omega.
  rewrite J. remember (adv_ext (- Z.of_nat n) rho) as rho'. 
  clear Heqrho' J.
  induction n.
  - simpl. apply IHe2.
  - intros. simpl. rewrite IHn. rewrite adv_ext_swap. apply IHe1. 
Qed.

Lemma adv_exp_ext t d (e : exp t) rho : E[|adv_exp d e|] rho = E[|e|] (adv_ext d rho).
Proof. apply adv_exp_ext'. Qed.
