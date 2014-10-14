Require Import Denotational.
Require Import Equality.

(* Specialisation (a.k.a. partial evaluation) of contracts. *)

Definition fromLit {V t} (e : exp' V t) : option [|t|] :=
  match e with
    | Lit r => Some r
    | _ => None
  end.

Definition constFoldBin {V t s} (e1 e2 : exp' V t) : (BinOp t s) -> exp' V s :=
  match e1 with
    | Lit r1 => match e2 with
                     | Lit r2 => fun op => Lit (BinOpSem op r1 r2)
                     | _ => fun op => BinOpE op e1 e2
                   end
    | e1 => fun op => BinOpE op e1 e2
  end.


Definition constFoldAcc {V t} (rho : ext) (f : ext -> [|t|] -> exp' V t)  (l : nat) (z : ext -> exp' V t) :
  exp' V t + (nat * exp' V t).
admit. Defined.
(*  := *)
(*   match l with *)
(*     | O => inl (z rho) *)
(*     | S l' => match constFoldAcc (adv_ext (-1) rho) f l'  z with *)
(*                 | inl (Lit _ _ r) => inl (f rho r) *)
(*                 | inl e => inr (O, e) *)
(*                 | inr (n, e) => inr (S n, e) *)
(*               end *)
(* end. *)

Definition ext_empty : ext := fun _ _ _ => None.


Inductive PEnv {I} (ty : I -> Type) : list I -> list I -> Type := 
  | PEnvNil : PEnv ty nil nil
  | PEnvCons : forall {i l l'}, ty i -> PEnv ty l l' -> PEnv ty (i :: l) l'
  | PEnvSkip : forall {i l l'}, PEnv ty l l' -> PEnv ty (i :: l) (i :: l').


Require Import JMeq.

Definition shiftIndex {i j : Ty} {ty V } (x : ty i + Var V i) : ty i + Var (j :: V) i :=
  match x with
    | inl a => inl a
    | inr v => inr (VS v)
  end.


Program Fixpoint lookupPEnv {ty V V'} {i : Ty} (v : Var V i) : PEnv ty V V' -> ty i + Var V' i :=
  match v in Var V t return PEnv ty V V' -> ty i + Var V' i with
    | V1 _ _ => fun e => match e with
                       | PEnvCons _ _ _ x _ => inl x
                       | PEnvSkip i _ l' _ => inr (V1 _)
                       | PEnvNil => _
                     end
    | VS  l' i j v' => fun e => match e with
                       | PEnvCons _ _ _ _ e' => lookupPEnv v' e'
                       | PEnvSkip i _ l' e' => shiftIndex (lookupPEnv v' e')
                       | PEnvNil => _
                     end
  end.



Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.



Fixpoint Rspecialise' {V V' t} (e : exp' V t) (rho : ext) : PEnv TySem V V' -> exp' V' t :=
    match e with
      | Lit _ _ r => fun _ => Lit r
      | BinOpE _ _ _ op e1 e2 => fun vars => match option_map2 op (fromLit (Rspecialise' e1 rho vars))
                                                               (fromLit (Rspecialise' e2 rho vars)) with
                                                                            
      | UnOpE _ _ _ op e => fun vars =>
                      match Rspecialise' e rho vars with
                        | Lit _ _ r => Lit (op r)
                        | e => UnOpE op e
                      end
      | Obs _ ty obs t => fun vars =>
                         match rho t ty obs with
                           | Some r => Lit r
                           | None => Obs obs t
                         end
      | VarE _ _ v => fun vars =>
                      match lookupPEnv v vars with
                        | inl r =>  Lit r
                        | inr v' => Var v'
                      end
      | Acc _ _ f l z => fun vars =>
                        let z' rho := Rspecialise' z rho vars in
                        let f' rho r := Rspecialise' f rho (PEnvCons r vars)
                        in match constFoldAcc rho f' l z' with
                             | inl e => e
                             | inr (l', e') => Acc (Rspecialise' f ext_empty (PEnvSkip vars)) l' e'
                           end
    end.


Definition Rspecialise (e : rexp) (o : obs) : rexp := Rspecialise' e o (PEmpty (zero R)).


Fixpoint constFoldBAcc {V} (rho : ext) (f : ext -> bool -> bexp' V)  (l : nat) (z : ext -> bexp' V) :
  bexp' V + (nat * bexp' V) :=
  match l with
    | O => inl (z rho)
    | S l' => match constFoldBAcc (adv_ext (-1) rho) f l'  z with
                | inl (BLit _ b) => inl (f rho b)
                | inl e => inr (O, e)
                | inr (n, e) => inr (S n, e)
              end
end.

Definition choices_empty : choices := fun _ _ => None.

Definition ext_empty : ext := (obs_empty,choices_empty).


Definition constFoldBOp {V} (op : BoolOp) (e1 e2 : bexp' V) : bexp' V :=
  match e1 with
    | BLit _ b1 => match e2 with
                     | BLit _ b2 => BLit (BBinOp op b1 b2)
                     | _ => BOp op e1 e2
                   end
    | _ => BOp op e1 e2
  end.


Fixpoint Bspecialise' {V V'} (e : bexp' V) (rho : ext) : PEnv bool V V' -> bexp' V' :=
  match e with
    | BLit _ b => fun _ => BLit b
    | BChoice _ ch t => fun vars => match snd rho t ch with
                           | Some b => BLit b
                           | None => BChoice ch t
                         end
    | RCmp _ cmp e1 e2 => fun vars => match Rspecialise e1 (fst rho), Rspecialise e2 (fst rho) with
                          | RLit _ b1, RLit _ b2 => BLit (RCompare cmp b1 b2)
                          | e1',e2' => RCmp cmp e1' e2'
                        end
    | BNot _ e' => fun vars => match Bspecialise' e' rho vars with
                   | BLit _ b => BLit (negb b)
                   | e'' => BNot e''
                 end
    | BOp _ op e1 e2 => fun vars => constFoldBOp op (Bspecialise' e1 rho vars) (Bspecialise' e2 rho vars)
    | BVar _ v => fun vars =>
                    match lookupPEnv vars v with
                      | inl r =>  BLit r
                      | inr v' => BVar v'
                    end
    | BAcc _ f l z => fun vars =>
                        let z' rho := Bspecialise' z rho vars in
                        let f' rho r := Bspecialise' f rho (PExtend r vars)
                        in match constFoldBAcc rho f' l z' with
                             | inl e => e
                             | inr (l', e') => BAcc (Bspecialise' f ext_empty (PSkip vars)) l' e'
                           end
                                      
  end.

Definition Bspecialise (e : bexp) (rho : ext) : bexp := Bspecialise' e rho (PEmpty (zero bool)).

Fixpoint traverseIfWithin (rho : ext) (e: bexp) (c1 c2 : ext -> contract) (l : nat) : contract + (bexp * nat) :=
  match Bspecialise e rho with
      | BLit _ true => inl (c1 rho)
      | BLit _ false => match l with
                        | O => inl (c2 rho)
                        | S l' => traverseIfWithin (adv_ext 1 rho) e c1 c2 l'
                        end
      | e' => inr (e', l)
  end.

Fixpoint specialise (c : contract) (rho : ext) : contract :=
  match c with
    | Zero => c
    | TransfOne _ _ _ => c
    | Scale e c' => Scale (Rspecialise e (fst rho)) c'
    | Transl l c' => Transl l (specialise c' (adv_ext (Z.of_nat l) rho))
    | Both c1 c2 => Both (specialise c1 rho) (specialise c2 rho)
    | IfWithin e l c1 c2 => match traverseIfWithin rho e (specialise c1) (specialise c2) l with
                              | inl c' => c
                              | inr (e', l') => transl (l - l') (IfWithin e' l' c1 c2)
                            end
  end.