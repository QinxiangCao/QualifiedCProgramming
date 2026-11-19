From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules64.
Local Open Scope sac.

Definition strstr_rel_cleanup_strategy1 :=
  forall (p : Z) (l : (@list (@option Z))) (n : Z),
    TT &&
    emp **
    ((UInt64Array.mixed_full p n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full p n))
    ).

Definition strstr_rel_cleanup_strategy2 :=
  forall (n : Z) (v : Z) (p : Z),
    TT &&
    (“ (1 <= n) ”) &&
    emp **
    ((poly_store FET_uint64 (p + (0 * sizeof(UINT64))) v)) **
    ((UInt64Array.undef_seg p 1 n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UInt64Array.undef_full p n))
    ).

Module Type strstr_rel_cleanup_Strategy_Correct.

  Axiom strstr_rel_cleanup_strategy1_correctness : strstr_rel_cleanup_strategy1.
  Axiom strstr_rel_cleanup_strategy2_correctness : strstr_rel_cleanup_strategy2.

End strstr_rel_cleanup_Strategy_Correct.
