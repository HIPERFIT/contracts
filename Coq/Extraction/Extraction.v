Add LoadPath "..".

Require Import Denotational.
Require Import Reduction.
Require Import Horizon.
Require Import SyntacticCausality.
Require Import Specialise.


Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inlined Constant orb => "(||)".
Extract Inlined Constant andb => "(&&)".

Extract Inlined Constant option_map => "fmap".

Extract Inductive nat => "Int" ["0" "succ"] "(\fO fS n -> if n==0 then fO () else fS (n-1))".
Extract Inductive Z => "Int" ["0" "id" "negate"].
Extract Inductive positive => "Int" ["unused" "unused" "1"].

Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.add => "(+)".
Extract Inlined Constant Z.sub => "(-)".
Extract Inlined Constant Z.mul => "(*)".
Extract Inlined Constant Z.opp => "negate".

Extract Inlined Constant R => "Double".
Extract Inlined Constant Rleb => "(<=)".
Extract Inlined Constant Rplus => "(+)".
Extract Inlined Constant Rminus => "(-)".
Extract Inlined Constant Rmult => "(*)".
Extract Inlined Constant Rdiv => "(/)".
Extract Inlined Constant Ropp => "negate".
Extract Inlined Constant R1 => "1".
Extract Inlined Constant R0 => "0".


Extract Inlined Constant negb => "not".
Extract Inlined Constant Z.eqb => "(==)".
Extract Inlined Constant eq_str => "(==)".

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inlined Constant plus => "(+)".
Extract Inlined Constant minus => "(-)".
Extract Inlined Constant max => "max".
Extract Inlined Constant Z.of_nat => "id".
Extract Inlined Constant Z.to_nat => "id".

Extract Inductive option => "Maybe" [ "Just" "Nothing" ].
Extract Constant option_rect => "flip maybe".
Extraction Inline option_rect option_rec.

Extract Inductive sum => "Either" ["Left" "Right"].

Extract Inductive string => "String" ["[]" "(:)"].

Extract Inductive Ascii.ascii => "Char" ["'a'"]. (* TODO: real translation *)

Extract Inductive PEnv => "PEnv" [ "PEmpty" "PExtend" "PSkip" ].
Extract Inductive Env => "Env" [ "Empty" "Extend" ].
Extract Inductive ZeroT => "ZeroT" [].

Extraction "ContractExtracted.hs" 
  contract
  horizon
  RedFun
  pc_dec
  specialise.