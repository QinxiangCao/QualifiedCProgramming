From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition ptr_array2_strategy1 :=
  forall (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharPtrArray2.full p n rows))
    |--
    EX (row_ptr : Z),
      (
      TT &&
      emp **
      ((CharPtrArray2.missing_i p n i row_ptr rows)) **
      ((CharArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = row_ptr) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr (p + (i * sizeof(PTR))) v))
        ).

Definition ptr_array2_strategy4 :=
  forall (p : Z) (rows1 : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((CharPtrArray2.full p n rows1))
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
      ((CharPtrArray2.full p n rows2))
      ).

Definition ptr_array2_strategy5 :=
  forall (p : Z) (i : Z) (rows : (@list (@list Z))) (row_ptr : Z) (n : Z),
    TT &&
    emp **
    ((CharPtrArray2.missing_i p n i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharPtrArray2.missing_i p n i row_ptr rows))
    ).

Definition ptr_array2_strategy2 :=
  forall (i : Z) (n : Z) (rows : (@list (@list Z))) (__default_app1_Z : (@list Z)) (row_ptr : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharPtrArray2.missing_i p n i row_ptr rows)) **
    ((CharArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((poly_store FET_ptr (p + (i * sizeof(PTR))) row_ptr))
    |--
    (
    TT &&
    emp **
    ((CharPtrArray2.full p n rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type ptr_array2_Strategy_Correct.

  Axiom ptr_array2_strategy1_correctness : ptr_array2_strategy1.
  Axiom ptr_array2_strategy4_correctness : ptr_array2_strategy4.
  Axiom ptr_array2_strategy5_correctness : ptr_array2_strategy5.
  Axiom ptr_array2_strategy2_correctness : ptr_array2_strategy2.

End ptr_array2_Strategy_Correct.
