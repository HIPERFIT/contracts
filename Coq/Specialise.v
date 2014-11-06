Require Import Denotational.

(* Specialisation (a.k.a. partial evaluation) of contracts. *)

Fixpoint constFoldAcc (rho : ExtEnv) (f : ExtEnv -> option Val -> Exp)  (l : nat) (z : ExtEnv -> Exp) :
  Exp + (nat * Exp) :=
  match l with
    | O => inl (z rho)
    | S l' => match constFoldAcc (adv_ext (-1) rho) f l'  z with
                | inl (OpE (RLit r) nil) => inl (f rho (Some (RVal r)))
                | inl (OpE (BLit b) nil) => inl (f rho (Some (BVal b)))
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.

Import ListNotations.

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

Definition default {A} (d : A) (x : option A) : A :=
  match x with
    | Some y => y
    | None => d
  end.

Fixpoint specialiseExp (e : Exp) (rho : ExtEnv) (vars : Env) : Exp :=
    match e with
      | OpE IfE [e1; e2; e3] => match fromLit (specialiseExp e1 rho vars) with
                                    | Some (BVal b) => if b 
                                                       then specialiseExp e2 rho vars
                                                       else specialiseExp e3 rho vars
                                    | _ => e
                                  end
      | OpE op args => let fix run es := 
                           match es with
                             | nil => Some nil
                             | e' :: es' => liftM2 (@cons _) (fromLit (specialiseExp e' rho vars)) (run es')
                           end
                       in default e (liftM toLit (run args >>= OpSem op))
      | Obs obs t => default e (liftM toLit (rho obs t))
      | VarE v => default e (liftM toLit (lookupEnv v vars))
      | Acc f l z => let z' rho := specialiseExp z rho vars in
                     let f' rho r := specialiseExp f rho (r :: vars)
                     in match constFoldAcc rho f' l z' with
                          | inl e => e
                          | inr (l', e') => Acc (specialiseExp f rho (None :: vars)) l' e'
                        end
    end.


(* default e (liftM toLit (mapM (fun e' => fromLit (specialiseExp e' rho vars)) args >>= OpSem op)) *)



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
