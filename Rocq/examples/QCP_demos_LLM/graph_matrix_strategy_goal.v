From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Local Open Scope sac.

Definition graph_matrix_strategy2 :=
  forall (j : Z) (n : Z) (i : Z) (size : Z) (rows : (@list (@list Z))) (model : ((@list (@list Z)) -> Prop)) (__default_app1_Z : (@list Z)) (p : Z),
    TT &&
    (“ (n = size) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < n) ”) &&
    emp **
    ((GraphMatrixFlat.store_graph size model p rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((IntArray2.missing_i p i 0 n n rows)) **
    ((IntArray.missing_i (p + ((i * n) * sizeof(INT))) j 0 n (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (p + (((i * n) + j) * sizeof(INT))) v))
      ).

Definition graph_matrix_strategy3 :=
  forall (n : Z) (size : Z) (rows : (@list (@list Z))) (model : ((@list (@list Z)) -> Prop)) (p : Z),
    TT &&
    (“ (model rows) ”) &&
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
    ((GraphMatrixFlat.store_graph size model p rows))
    ).

Definition graph_matrix_strategy4 :=
  forall (j : Z) (size : Z) (i : Z) (w : Z) (rows : (@list (@list Z))) (model : ((@list (@list Z)) -> Prop)) (__default_app1_Z : (@list Z)) (p : Z),
    TT &&
    (“ (w = size) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < size) ”) &&
    emp **
    ((GraphMatrixFlat.store_graph size model p rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((IntArray2.missing_i p i 0 size size rows)) **
    ((IntArray.missing_i (p + (i * (w * sizeof(INT)))) j 0 size (Znth i rows __default_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int ((p + (i * (w * sizeof(INT)))) + (j * sizeof(INT))) v))
      ).

Definition graph_matrix_strategy6 :=
  forall (n : Z) (size : Z) (rows : (@list (@list Z))) (model : ((@list (@list Z)) -> Prop)) (p : Z),
    TT &&
    (“ (model rows) ”) &&
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
    ((GraphMatrixPtr.store_graph size model p rows))
    ).

Definition graph_matrix_strategy7 :=
  forall (i : Z) (size : Z) (model : ((@list (@list Z)) -> Prop)) (rows : (@list (@list Z))) (__default_app1_Z : (@list Z)) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.store_graph size model p rows))
    |--
    EX (row_ptr : Z),
      (
      TT &&
      (“ (model rows) ”) &&
      emp **
      ((IntPtrArray2.missing_i p size i row_ptr rows)) **
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

Definition graph_matrix_strategy8 :=
  forall (read_ptr : Z) (row_ptr : Z) (model : ((@list (@list Z)) -> Prop)) (size : Z) (rows : (@list (@list Z))) (i : Z) (__default_app1_Z : (@list Z)) (j : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < (@Zlength Z (Znth i rows __default_app1_Z))) ”) &&
    (“ (read_ptr = row_ptr) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((poly_store FET_ptr (p + (i * sizeof(PTR))) row_ptr)) **
    ((IntArray.missing_i row_ptr j 0 (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((IntPtrArray2.missing_i p size i row_ptr rows))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (@Znth Z j (Znth i rows __default_app1_Z) 0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (read_ptr + (j * sizeof(INT))) v))
      ).

Definition graph_matrix_strategy9 :=
  forall (i : Z) (size : Z) (model : ((@list (@list Z)) -> Prop)) (rows : (@list (@list Z))) (__default_app1_Z : (@list Z)) (p : Z) (row_ptr : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((IntArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((IntPtrArray2.missing_i p size i row_ptr rows))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = row_ptr) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr (p + (i * sizeof(PTR))) v))
      ).

Definition graph_matrix_strategy10 :=
  forall (i : Z) (size : Z) (model : ((@list (@list Z)) -> Prop)) (rows : (@list (@list Z))) (__default_app1_Z : (@list Z)) (p : Z) (row_ptr : Z),
    TT &&
    (“ (model rows) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((poly_store FET_ptr (p + (i * sizeof(PTR))) row_ptr)) **
    ((IntArray.full row_ptr (@Zlength Z (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
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
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    ).

Definition graph_matrix_strategy11 :=
  forall (i : Z) (size : Z) (p : Z) (row_ptr : Z) (rows : (@list (@list Z))) (model : ((@list (@list Z)) -> Prop)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((GraphMatrixPtr.store_graph size model p rows))
    ).

Definition graph_matrix_strategy1 :=
  forall (model : ((@list (@list Z)) -> Prop)) (rows : (@list (@list Z))) (n : Z) (p : Z),
    TT &&
    emp **
    ((GraphMatrixFlat.store_graph n model p rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((IntArray2.full p n n rows))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type graph_matrix_Strategy_Correct.

  Axiom graph_matrix_strategy2_correctness : graph_matrix_strategy2.
  Axiom graph_matrix_strategy3_correctness : graph_matrix_strategy3.
  Axiom graph_matrix_strategy4_correctness : graph_matrix_strategy4.
  Axiom graph_matrix_strategy6_correctness : graph_matrix_strategy6.
  Axiom graph_matrix_strategy7_correctness : graph_matrix_strategy7.
  Axiom graph_matrix_strategy8_correctness : graph_matrix_strategy8.
  Axiom graph_matrix_strategy9_correctness : graph_matrix_strategy9.
  Axiom graph_matrix_strategy10_correctness : graph_matrix_strategy10.
  Axiom graph_matrix_strategy11_correctness : graph_matrix_strategy11.
  Axiom graph_matrix_strategy1_correctness : graph_matrix_strategy1.

End graph_matrix_Strategy_Correct.
