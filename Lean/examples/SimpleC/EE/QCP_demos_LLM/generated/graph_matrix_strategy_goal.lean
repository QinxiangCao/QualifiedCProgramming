import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance graph_matrixStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string


noncomputable def graph_matrix_strategy2 : Prop :=
  forall (j : Int) (n : Int) (i : Int) (size : Int) (rows : (List (List Int))) (model : ((List (List Int)) -> Prop)) (__default_app1_Z : (List Int)) (p : Int),
    TT &&
    (“ (n = size) ”) &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < n) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < n) ”) &&
    emp **
    ((GraphMatrixFlat.store_graph size model p rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) n n rows)) **
    ((intArray.missing_i (p + (i * n) * sizeof(INT)) j (0 : Int) n (Znth i rows __default_app1_Z)))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (@Znth Int j (Znth i rows __default_app1_Z) (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + ((i * n) + j) * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def graph_matrix_strategy3 : Prop :=
  forall (n : Int) (size : Int) (rows : (List (List Int))) (model : ((List (List Int)) -> Prop)) (p : Int),
    TT &&
    (“ (model rows) ”) &&
    (“ (n = size) ”) &&
    emp **
    ((intArray2.full p n n rows))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((GraphMatrixFlat.store_graph size model p rows)))
    )

noncomputable def graph_matrix_strategy4 : Prop :=
  forall (j : Int) (size : Int) (i : Int) (w : Int) (rows : (List (List Int))) (model : ((List (List Int)) -> Prop)) (__default_app1_Z : (List Int)) (p : Int),
    TT &&
    (“ (w = size) ”) &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < size) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < size) ”) &&
    emp **
    ((GraphMatrixFlat.store_graph size model p rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((intArray2.missing_i p i (0 : Int) size size rows)) **
    ((intArray.missing_i (p + i * (sizeof(INT) * w)) j (0 : Int) size (Znth i rows __default_app1_Z)))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (@Znth Int j (Znth i rows __default_app1_Z) (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      ((((p + i * (sizeof(INT) * w)) + j * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def graph_matrix_strategy6 : Prop :=
  forall (n : Int) (size : Int) (rows : (List (List Int))) (model : ((List (List Int)) -> Prop)) (p : Int),
    TT &&
    (“ (model rows) ”) &&
    (“ (n = size) ”) &&
    emp **
    ((intPtrArray2.full p n rows))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((GraphMatrixPtr.store_graph size model p rows)))
    )

noncomputable def graph_matrix_strategy7 : Prop :=
  forall (i : Int) (size : Int) (model : ((List (List Int)) -> Prop)) (rows : (List (List Int))) (__default_app1_Z : (List Int)) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.store_graph size model p rows))
    |--
    EX row_ptr : Int, 
      (
      TT &&
      (“ (model rows) ”) &&
      emp **
      ((intPtrArray2.missing_i p size i row_ptr rows)) **
      ((intArray.full row_ptr (@Zlength Int (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)))
      ) ** (
      ALL v : Int, 
(
        TT &&
        (“ (v = row_ptr) ”) &&
        emp) -* (
        TT &&
        emp **
        (((p + i * sizeof(PTR)) # PTR |-> (v))))
        )

noncomputable def graph_matrix_strategy8 : Prop :=
  forall (read_ptr : Int) (row_ptr : Int) (model : ((List (List Int)) -> Prop)) (size : Int) (rows : (List (List Int))) (i : Int) (__default_app1_Z : (List Int)) (j : Int) (p : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < size) ”) &&
    (“ ((0 : Int) <= j) ”) &&
    (“ (j < (@Zlength Int (Znth i rows __default_app1_Z))) ”) &&
    (“ (read_ptr = row_ptr) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    (((p + i * sizeof(PTR)) # PTR |-> (row_ptr))) **
    ((intArray.missing_i row_ptr j (0 : Int) (@Zlength Int (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((intPtrArray2.missing_i p size i row_ptr rows))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = (@Znth Int j (Znth i rows __default_app1_Z) (0 : Int))) ”) &&
      emp) -* (
      TT &&
      emp **
      (((read_ptr + j * sizeof(INT)) # INT |-> (v))))
      )

noncomputable def graph_matrix_strategy9 : Prop :=
  forall (i : Int) (size : Int) (model : ((List (List Int)) -> Prop)) (rows : (List (List Int))) (__default_app1_Z : (List Int)) (p : Int) (row_ptr : Int),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((intArray.full row_ptr (@Zlength Int (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((intPtrArray2.missing_i p size i row_ptr rows))
    ) ** (
    ALL v : Int, 
(
      TT &&
      (“ (v = row_ptr) ”) &&
      emp) -* (
      TT &&
      emp **
      (((p + i * sizeof(PTR)) # PTR |-> (v))))
      )

noncomputable def graph_matrix_strategy10 : Prop :=
  forall (i : Int) (size : Int) (model : ((List (List Int)) -> Prop)) (rows : (List (List Int))) (__default_app1_Z : (List Int)) (p : Int) (row_ptr : Int),
    TT &&
    (“ (model rows) ”) &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    (((p + i * sizeof(PTR)) # PTR |-> (row_ptr))) **
    ((intArray.full row_ptr (@Zlength Int (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z))) **
    ((intPtrArray2.missing_i p size i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows)))
    )

noncomputable def graph_matrix_strategy11 : Prop :=
  forall (i : Int) (size : Int) (p : Int) (row_ptr : Int) (rows : (List (List Int))) (model : ((List (List Int)) -> Prop)),
    TT &&
    (“ ((0 : Int) <= i) ”) &&
    (“ (i < size) ”) &&
    emp **
    ((GraphMatrixPtr.row_rep size model p i row_ptr rows))
    |--
    (
    TT &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp **
    ((GraphMatrixPtr.store_graph size model p rows)))
    )

noncomputable def graph_matrix_strategy1 : Prop :=
  forall (model : ((List (List Int)) -> Prop)) (rows : (List (List Int))) (n : Int) (p : Int),
    TT &&
    emp **
    ((GraphMatrixFlat.store_graph n model p rows))
    |--
    (
    TT &&
    (“ (model rows) ”) &&
    emp **
    ((intArray2.full p n n rows))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

structure graph_matrix_Strategy_Correct : Type where
  graph_matrix_strategy2_correctness : graph_matrix_strategy2
  graph_matrix_strategy3_correctness : graph_matrix_strategy3
  graph_matrix_strategy4_correctness : graph_matrix_strategy4
  graph_matrix_strategy6_correctness : graph_matrix_strategy6
  graph_matrix_strategy7_correctness : graph_matrix_strategy7
  graph_matrix_strategy8_correctness : graph_matrix_strategy8
  graph_matrix_strategy9_correctness : graph_matrix_strategy9
  graph_matrix_strategy10_correctness : graph_matrix_strategy10
  graph_matrix_strategy11_correctness : graph_matrix_strategy11
  graph_matrix_strategy1_correctness : graph_matrix_strategy1

end SimpleC.EE.QCP_demos_LLM.generated.graph_matrix_strategy_goal
