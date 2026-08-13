Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition ptr_array2_strategy1 :=
  forall (i : Z) (n : Z) (__default_app1_Z : (@list Z)) (p : Z) (rows : (@list (@list Z))),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
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
        ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
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
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((CharPtrArray2.missing_i p n i row_ptr rows)) **
    ((CharArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((poly_store FET_ptr (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr))
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
