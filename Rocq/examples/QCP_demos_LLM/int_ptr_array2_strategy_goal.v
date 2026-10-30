From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition int_ptr_array2_strategy1 :=
  forall (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((IntPtrArray2.full p n rows))
    |--
    EX (row_ptr : Z),
      (
      TT &&
      emp **
      ((IntPtrArray2.missing_i p n i row_ptr rows)) **
      ((IntArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = row_ptr) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr (p + (i * sizeof(PTR))) v))
        ).

Definition int_ptr_array2_strategy4 :=
  forall (p : Z) (rows1 : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((IntPtrArray2.full p n rows1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (rows2 : (@list (@list Z))),
      TT &&
      (“ (rows1 = rows2) ”) &&
      emp -*
      TT &&
      emp **
      ((IntPtrArray2.full p n rows2))
      ).

Definition int_ptr_array2_strategy5 :=
  forall (p : Z) (i : Z) (rows : (@list (@list Z))) (row_ptr : Z) (n : Z),
    TT &&
    emp **
    ((IntPtrArray2.missing_i p n i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntPtrArray2.missing_i p n i row_ptr rows))
    ).

Definition int_ptr_array2_strategy2 :=
  forall (i : Z) (n : Z) (rows : (@list (@list Z))) (__default_app1_Z : (@list Z)) (row_ptr : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((IntPtrArray2.missing_i p n i row_ptr rows)) **
    ((IntArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((poly_store FET_ptr (p + (i * sizeof(PTR))) row_ptr))
    |--
    (
    TT &&
    emp **
    ((IntPtrArray2.full p n rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type int_ptr_array2_Strategy_Correct.

  Axiom int_ptr_array2_strategy1_correctness : int_ptr_array2_strategy1.
  Axiom int_ptr_array2_strategy4_correctness : int_ptr_array2_strategy4.
  Axiom int_ptr_array2_strategy5_correctness : int_ptr_array2_strategy5.
  Axiom int_ptr_array2_strategy2_correctness : int_ptr_array2_strategy2.

End int_ptr_array2_Strategy_Correct.
