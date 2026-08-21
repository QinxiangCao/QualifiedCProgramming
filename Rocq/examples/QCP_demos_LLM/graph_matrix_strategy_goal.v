Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition graph_matrix_strategy1 :=
  forall (n : Z) (rows : list (list Z)) (p : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    emp **
    ((GraphMatrixFlat.graph_rep n matrix_model p rows))
    |--
    (
    TT &&
    (“ (matrix_model rows) ”) &&
    emp **
    ((IntArray2.full p n n rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition graph_matrix_strategy2 :=
  forall (size n : Z) (j : Z) (i : Z)
         (__default_app1_Z : list Z) (rows : list (list Z))
         (p : Z) (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (n = size) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < n) ”) &&
    emp **
    ((GraphMatrixFlat.graph_rep size matrix_model p rows))
    |--
    (
    TT &&
    (“ (matrix_model rows) ”) &&
    emp **
    ((IntArray2.missing_i p i 0 n n rows)) **
    ((IntArray.missing_i
      (Z.add p (Z.mul (Z.mul i n) (@sizeof_front_end_type FET_int)))
      j 0 n (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = Znth j (Znth i rows __default_app1_Z) 0) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int
        (Z.add p (Z.mul (Z.add (Z.mul i n) j)
          (@sizeof_front_end_type FET_int))) v))
    ).

Definition graph_matrix_strategy3 :=
  forall (size n : Z) (rows : list (list Z)) (p : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (matrix_model rows) ”) &&
    (“ (n = size) ”) &&
    emp **
    ((IntArray2.full p n n rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((GraphMatrixFlat.graph_rep size matrix_model p rows))
    ).

Definition graph_matrix_strategy4 :=
  forall (w size : Z) (j : Z) (i : Z)
         (__default_app1_Z : list Z) (rows : list (list Z))
         (p : Z) (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (w = size) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < size) ”) &&
    emp **
    ((GraphMatrixFlat.graph_rep size matrix_model p rows))
    |--
    (
    TT &&
    (“ (matrix_model rows) ”) &&
    emp **
    ((IntArray2.missing_i p i 0 size size rows)) **
    ((IntArray.missing_i
      (Z.add p (Z.mul i
        (Z.mul (@sizeof_front_end_type FET_int) w)))
      j 0 size (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = Znth j (Znth i rows __default_app1_Z) 0) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int
        (Z.add
          (Z.add p
            (Z.mul i (Z.mul (@sizeof_front_end_type FET_int) w)))
          (Z.mul j (@sizeof_front_end_type FET_int))) v))
    ).

Definition graph_matrix_strategy5 :=
  forall (n : Z) (rows : list (list Z)) (p : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    emp **
    ((GraphMatrixPtr.graph_rep n matrix_model p rows))
    |--
    (
    TT &&
    (“ (matrix_model rows) ”) &&
    emp **
    ((IntPtrArray2.full p n rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition graph_matrix_strategy6 :=
  forall (size n : Z) (rows : list (list Z)) (p : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (matrix_model rows) ”) &&
    (“ (n = size) ”) &&
    emp **
    ((IntPtrArray2.full p n rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((GraphMatrixPtr.graph_rep size matrix_model p rows))
    ).

Definition graph_matrix_strategy7 :=
  forall (i : Z) (size : Z) (__default_app1_Z : list Z)
         (rows : list (list Z)) (p : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.graph_rep size matrix_model p rows))
    |--
    EX (row_ptr : Z),
      (
      TT &&
      (“ (matrix_model rows) ”) &&
      emp **
      ((IntPtrArray2.missing_i p size i row_ptr rows)) **
      ((IntArray.full row_ptr
        (Zlength (Znth i rows __default_app1_Z))
        (Znth i rows __default_app1_Z)))
      ) ** (
      ALL (v : Z),
        TT &&
        (“ (v = row_ptr) ”) &&
        emp -*
        TT &&
        emp **
        ((poly_store FET_ptr
          (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
      ).

Definition graph_matrix_strategy8 :=
  forall (j i size : Z) (__default_app1_Z : list Z)
         (rows : list (list Z)) (p row_ptr : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < Zlength (Znth i rows __default_app1_Z)) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size matrix_model p i row_ptr rows))
    |--
    (
    TT &&
    (“ (matrix_model rows) ”) &&
    emp **
    ((poly_store FET_ptr
      (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr)) **
    ((IntArray.missing_i row_ptr j 0
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z))) **
    ((IntPtrArray2.missing_i p size i row_ptr rows))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = Znth j (Znth i rows __default_app1_Z) 0) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int
        (Z.add row_ptr (Z.mul j (@sizeof_front_end_type FET_int))) v))
    ).

Definition graph_matrix_strategy9 :=
  forall (i size : Z) (__default_app1_Z : list Z)
         (rows : list (list Z)) (p row_ptr : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size matrix_model p i row_ptr rows))
    |--
    (
    TT &&
    (“ (matrix_model rows) ”) &&
    emp **
    ((IntArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z))) **
    ((IntPtrArray2.missing_i p size i row_ptr rows))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = row_ptr) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr
        (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) v))
    ).

Definition graph_matrix_strategy10 :=
  forall (i size : Z) (__default_app1_Z : list Z)
         (rows : list (list Z)) (p row_ptr : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (matrix_model rows) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((poly_store FET_ptr
      (Z.add p (Z.mul i (@sizeof_front_end_type FET_ptr))) row_ptr)) **
    ((IntArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z))) **
    ((IntPtrArray2.missing_i p size i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((GraphMatrixPtr.row_rep size matrix_model p i row_ptr rows))
    ).

Definition graph_matrix_strategy11 :=
  forall (i size : Z) (rows : list (list Z)) (p row_ptr : Z)
         (matrix_model : list (list Z) -> Prop),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size matrix_model p i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((GraphMatrixPtr.graph_rep size matrix_model p rows))
    ).

Module Type graph_matrix_Strategy_Correct.

  Axiom graph_matrix_strategy1_correctness : graph_matrix_strategy1.
  Axiom graph_matrix_strategy2_correctness : graph_matrix_strategy2.
  Axiom graph_matrix_strategy3_correctness : graph_matrix_strategy3.
  Axiom graph_matrix_strategy4_correctness : graph_matrix_strategy4.
  Axiom graph_matrix_strategy5_correctness : graph_matrix_strategy5.
  Axiom graph_matrix_strategy6_correctness : graph_matrix_strategy6.
  Axiom graph_matrix_strategy7_correctness : graph_matrix_strategy7.
  Axiom graph_matrix_strategy8_correctness : graph_matrix_strategy8.
  Axiom graph_matrix_strategy9_correctness : graph_matrix_strategy9.
  Axiom graph_matrix_strategy10_correctness : graph_matrix_strategy10.
  Axiom graph_matrix_strategy11_correctness : graph_matrix_strategy11.

End graph_matrix_Strategy_Correct.
