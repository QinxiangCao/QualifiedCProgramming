From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Definition string_strategy1 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    emp **
    ((store_string p l))
    |--
    (
    TT &&
    emp **
    ((CharArray.full p ((string_length l) + 1) (c_string l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition string_strategy2 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (l : (@list Z)),
    TT &&
    emp **
    ((CharArray.full p ((string_length l) + 1) (c_string l))) -*
    TT &&
    emp **
    ((store_string p l))
    ).

Module Type string_Strategy_Correct.

  Axiom string_strategy1_correctness : string_strategy1.
  Axiom string_strategy2_correctness : string_strategy2.

End string_Strategy_Correct.
