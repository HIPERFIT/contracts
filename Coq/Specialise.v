Require Import Denotational.
Require Import Tactics.
Require Import Monotonicity.

(* Specialisation (a.k.a. partial evaluation) of contracts. *)


Import ListNotations.

Definition fromLit (e : Exp) : option Val :=
  match e with
    | OpE (RLit r) nil => Some (RVal r)
    | OpE (BLit b) nil => Some (BVal b)
    | _ => None
  end.


Fixpoint constFoldAcc (rho : ExtEnv) (f : ExtEnv -> Val -> Exp)  (l : nat) (z : ExtEnv -> Exp) :
  option Exp :=
  match l with
    | O => Some (z rho)
    | S l' => liftM (f rho) (constFoldAcc (adv_ext (-1) rho) f l' z >>= fromLit)
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

Definition OpSemLazy (op : Op) (args : list (option Val)) : option Val :=
  match op with
    | Cond => match args with
                | [e1; e2; e3] => match e1 with
                                      | Some (BVal true) => e2
                                      | Some (BVal false) => e3
                                      | _ => None
                                  end
                | _ => None
              end
    | And => match args with
               | [e1;e2] => match e1, e2 with
                              | Some (BVal false), _ => Some (BVal false)
                              | _, Some (BVal false) => Some (BVal false)
                              | Some (BVal true), Some (BVal true) => Some (BVal true)
                              | _, _ => None
                            end
               | _ => None
             end
    | Or => match args with
              | [e1; e2] => match e1, e2 with
                                | Some (BVal true), _ => Some (BVal true)
                                | _ , Some (BVal true) => Some (BVal true)
                                | Some (BVal false), Some (BVal false) => Some (BVal false)
                                | _, _ => None
                            end
               | _ => None
            end
    | _ =>  (sequence args) >>= OpSem op
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

Lemma OpSemLazy_sound (op : Op) (args : list (option Val)) :
  sequence args >>= OpSem op ⊆ OpSemLazy op args.
Proof.
  unfold "⊆". simpl. intros v S. destruct op;
  destruct args; try destruct args; try destruct args; 
  repeat (unfold liftM2, bind, pure, compose in *; simpl in *; auto; repeat destruct_match; tryfalse);
  destruct (sequence args); repeat destruct_match; auto. 
Qed.
  
Fixpoint specialiseExp (e : Exp) (rho : ExtEnv) (vars : Env) : Exp :=
    match e with
      | OpE op args => let args' := map (fun e' => specialiseExp e' rho vars) args
                       in default (OpE op args') (liftM toLit (OpSemLazy op (map fromLit args')))   
      | Obs obs t => default e (liftM toLit (rho obs t))
      | VarE v => default e (liftM toLit (lookupEnv v vars))
      | Acc f l z => let z' rho := specialiseExp z rho vars in
                     let f' rho r := specialiseExp f rho (r :: vars)
                     in default e (constFoldAcc rho f' l z')
    end.

Lemma Esem_toLit v vars rho :  E'[|toLit v|] vars rho = Some v.
Proof.
  destruct v; reflexivity.
Qed.

Lemma Esem_fromLit e vars rho : fromLit e ⊆ E'[|e|] vars rho.
Proof.
  unfold "⊆". simpl. intros. destruct e;tryfalse.
  destruct op; simpl in H; tryfalse; destruct args; tryfalse; auto.
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

Theorem specialiseExp_sound e rho vars rho':
                           rho ⊆ rho' -> E'[| e |] vars rho' ⊆
                           E'[| specialiseExp e rho vars |] vars rho'.
Proof.
  generalize dependent rho. generalize dependent rho'.
  generalize dependent vars. 
  induction e using Exp_ind'; intros vars rho' rho R. 
  - unfold "⊆". simpl.  intros v E.
    do 4 (eapply forall_list_apply_dep in H; eauto).
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
