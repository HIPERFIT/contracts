Add LoadPath "..".

Require Import Denotational.
Require Import Reduction.
Require Import Horizon.
Require Import Specialise.




Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inlined Constant orb => "(||)".
Extract Inlined Constant andb => "(&&)".

Extract Inlined Constant compose => "(.)".
Extract Inductive list => "List" [ "[]" "(:)" ].
Extract Inlined Constant map => "map".

Extract Inductive nat => "Int" ["0" "succ"] "(\fO fS n -> if n==0 then fO () else fS (n-1))".
Extract Inductive Z => "Int" ["0" "id" "negate"].
Extract Inductive positive => "Int" ["unused" "unused" "1"].

Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.ltb => "(<)".
Extract Inlined Constant Z.add => "(+)".
Extract Inlined Constant Z.sub => "(-)".
Extract Inlined Constant Z.mul => "(*)".
Extract Inlined Constant Z.opp => "negate".

Extract Inlined Constant R => "Double".
Extract Inlined Constant Rleb => "(<=)".
Extract Inlined Constant Reqb => "(==)".
Extract Inlined Constant Rltb => "(<)".
Extract Inlined Constant Rplus => "(+)".
Extract Inlined Constant Rminus => "(-)".
Extract Inlined Constant Rmult => "(*)".
Extract Inlined Constant Rdiv => "(/)".
Extract Inlined Constant Ropp => "negate".
Extract Inlined Constant R1 => "1".
Extract Inlined Constant R0 => "0".


Extract Inlined Constant negb => "not".
Extract Inlined Constant Z.eqb => "(==)".


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
Extract Inlined Constant bind => "(>>=)".
Extract Inlined Constant liftM => "liftM".
Extract Inlined Constant liftM2 => "liftM2".
Extract Inlined Constant pure => "return".
Extract Inlined Constant sequence => "sequence".
Extract Inlined Constant mapM => "mapM".


Extract Inductive sum => "Either" ["Left" "Right"].

Extract Inlined Constant Asset => "Asset".
Extract Inlined Constant Party => "Party".
Extract Inlined Constant BoolObs => "String".
Extract Inlined Constant RealObs => "String".

Extract Inlined Constant Asset.eqb => "(==)".
Extract Inlined Constant Party.eqb => "(==)".



Extraction "ContractExtracted.hs" 
  Contr
  horizon
  RedFun
  specialise.