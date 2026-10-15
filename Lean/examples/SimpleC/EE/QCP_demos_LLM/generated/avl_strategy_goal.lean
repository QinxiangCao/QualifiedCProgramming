import SimpleC.SL.LeanPrinterPrelude
import SimpleC.EE.QCP_demos_LLM.avl_shape

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC


local instance avlStrategyGoalSacContext : SacContext := { CRules := naive_C_Rules }

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


noncomputable def avl_strategy0 : Prop :=
  forall (p : Int) (tr0 : tree),
    TT &&
    emp **
    ((store_tree p tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL tr1 : tree, 
(
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp) -* (
      TT &&
      emp **
      ((store_tree p tr1)))
      )

noncomputable def avl_strategy9 : Prop :=
  forall (p : Int),
    TT &&
    emp **
    ((store_tree_shape p))
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
    ((store_tree_shape p)))
    )

noncomputable def avl_strategy12 : Prop :=
  forall (p : Int),
    TT &&
    emp **
    ((store_non_empty_tree p))
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
    ((store_non_empty_tree p)))
    )

noncomputable def avl_strategy25 : Prop :=
  forall (x : Int) (p : Int),
    TT &&
    emp **
    ((p # UCHAR |-> (x)))
    |--
    (
    TT &&
    (“ (x >= (0 : Int)) ”) &&
    emp **
    ((p # UCHAR |-> (x)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def avl_strategy26 : Prop :=
  forall (x : Int) (p : Int),
    TT &&
    emp **
    ((p # UCHAR |-> (x)))
    |--
    (
    TT &&
    (“ (x <= (255 : Int)) ”) &&
    emp **
    ((p # UCHAR |-> (x)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def avl_strategy7 : Prop :=
  forall (l : Int) (v : Int) (k : Int) (h : Int) (r : Int) (p : Int),
    TT &&
    emp **
    ((&( ((p)) # "tree" ->ₛ "key") # INT |-> (k))) **
    ((&( ((p)) # "tree" ->ₛ "value") # INT |-> (v))) **
    ((&( ((p)) # "tree" ->ₛ "height") # UCHAR |-> (h))) **
    ((&( ((p)) # "tree" ->ₛ "lchild") # PTR |-> (l))) **
    ((&( ((p)) # "tree" ->ₛ "rchild") # PTR |-> (r)))
    |--
    (
    TT &&
    emp **
    ((single_tree_node p k v h l r))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def avl_strategy8 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL p : Int, ALL v : Int, ALL l : Int, ALL r : Int, ALL h : Int, ALL k : Int, 
(
    TT &&
    emp **
    ((single_tree_node p k v h l r))) -* (
    TT &&
    emp **
    ((&( ((p)) # "tree" ->ₛ "key") # INT |-> (k))) **
    ((&( ((p)) # "tree" ->ₛ "value") # INT |-> (v))) **
    ((&( ((p)) # "tree" ->ₛ "height") # UCHAR |-> (h))) **
    ((&( ((p)) # "tree" ->ₛ "lchild") # PTR |-> (l))) **
    ((&( ((p)) # "tree" ->ₛ "rchild") # PTR |-> (r))))
    )

noncomputable def avl_strategy1 : Prop :=
  forall (p : Int) (tr : tree),
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp **
    ((store_tree p tr))
    |--
    EX k : Int, EX v : Int, EX h : Int, EX l : Int, EX r : Int, EX tr1 : tree, EX tr2 : tree, 
      (
      TT &&
      (“ (Not (p = (0 : Int))) ”) &&
      (“ (tr = (make_tree tr1 tr2)) ”) &&
      emp **
      ((single_tree_node p k v h l r)) **
      ((store_tree l tr1)) **
      ((store_tree r tr2))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def avl_strategy2 : Prop :=
  forall (p : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp
    ) ** (
    ALL tr : tree, ALL tr1 : tree, ALL tr2 : tree, ALL l : Int, ALL v : Int, ALL h : Int, ALL k : Int, ALL r : Int, 
(
      TT &&
      (“ (tr = (make_tree tr1 tr2)) ”) &&
      emp **
      ((single_tree_node p k v h l r)) **
      ((store_tree l tr1)) **
      ((store_tree r tr2))) -* (
      TT &&
      emp **
      ((store_tree p tr)))
      )

noncomputable def avl_strategy3 : Prop :=
  forall (p : Int) (tr : tree),
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp **
    ((store_tree p tr))
    |--
    (
    TT &&
    (“ (p = (0 : Int)) ”) &&
    (“ (tr = (empty)) ”) &&
    emp
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def avl_strategy4 : Prop :=
  forall (p : Int),
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp
    |--
    (
    TT &&
    (“ (p = (0 : Int)) ”) &&
    emp
    ) ** (
    ALL tr : tree, 
(
      TT &&
      (“ (tr = (empty)) ”) &&
      emp) -* (
      TT &&
      emp **
      ((store_tree p tr)))
      )

noncomputable def avl_strategy10 : Prop :=
  forall (p : Int),
    TT &&
    emp **
    ((store_tree_shape p))
    |--
    EX tr : tree, 
      (
      TT &&
      emp **
      ((store_tree p tr))
      ) ** (
(
      TT &&
      emp) -* (
      TT &&
      emp)
      )

noncomputable def avl_strategy11 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL p : Int, ALL tr : tree, 
(
    TT &&
    emp **
    ((store_tree p tr))) -* (
    TT &&
    emp **
    ((store_tree_shape p)))
    )

noncomputable def avl_strategy13 : Prop :=
  forall (p : Int),
    TT &&
    emp **
    ((store_non_empty_tree p))
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp **
    ((store_tree_shape p))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def avl_strategy15 : Prop :=
  forall (p : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp
    ) ** (
(
    TT &&
    emp **
    ((store_tree_shape p))) -* (
    TT &&
    emp **
    ((store_non_empty_tree p)))
    )

noncomputable def avl_strategy16 : Prop :=
  forall (p : Int),
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp
    |--
    (
    TT &&
    (“ (Not (p = (0 : Int))) ”) &&
    emp
    ) ** (
    ALL tr : tree, ALL tr1 : tree, ALL tr2 : tree, ALL l : Int, ALL v : Int, ALL h : Int, ALL k : Int, ALL r : Int, 
(
      TT &&
      (“ (tr = (make_tree tr1 tr2)) ”) &&
      emp **
      ((single_tree_node p k v h l r)) **
      ((store_tree l tr1)) **
      ((store_tree r tr2))) -* (
      TT &&
      emp **
      ((store_tree p tr)))
      )

noncomputable def avl_strategy17 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL tr : tree, 
(
    TT &&
    (“ (tr = (empty)) ”) &&
    emp) -* (
    TT &&
    emp **
    ((store_tree (0 : Int) tr)))
    )

noncomputable def avl_strategy5 : Prop :=
  forall (p : Int) (v : Int) (l : Int) (r : Int) (h : Int) (k : Int),
    TT &&
    emp **
    ((single_tree_node p k v h l r))
    |--
    (
    TT &&
    emp **
    ((&( ((p)) # "tree" ->ₛ "key") # INT |-> (k))) **
    ((&( ((p)) # "tree" ->ₛ "value") # INT |-> (v))) **
    ((&( ((p)) # "tree" ->ₛ "height") # UCHAR |-> (h))) **
    ((&( ((p)) # "tree" ->ₛ "lchild") # PTR |-> (l))) **
    ((&( ((p)) # "tree" ->ₛ "rchild") # PTR |-> (r)))
    ) ** (
(
    TT &&
    emp) -* (
    TT &&
    emp)
    )

noncomputable def avl_strategy6 : Prop :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL l : Int, ALL v : Int, ALL k : Int, ALL h : Int, ALL r : Int, ALL p : Int, 
(
    TT &&
    emp **
    ((&( ((p)) # "tree" ->ₛ "key") # INT |-> (k))) **
    ((&( ((p)) # "tree" ->ₛ "value") # INT |-> (v))) **
    ((&( ((p)) # "tree" ->ₛ "height") # UCHAR |-> (h))) **
    ((&( ((p)) # "tree" ->ₛ "lchild") # PTR |-> (l))) **
    ((&( ((p)) # "tree" ->ₛ "rchild") # PTR |-> (r)))) -* (
    TT &&
    emp **
    ((single_tree_node p k v h l r)))
    )

structure avl_Strategy_Correct : Type where
  avl_strategy0_correctness : avl_strategy0
  avl_strategy9_correctness : avl_strategy9
  avl_strategy12_correctness : avl_strategy12
  avl_strategy25_correctness : avl_strategy25
  avl_strategy26_correctness : avl_strategy26
  avl_strategy7_correctness : avl_strategy7
  avl_strategy8_correctness : avl_strategy8
  avl_strategy1_correctness : avl_strategy1
  avl_strategy2_correctness : avl_strategy2
  avl_strategy3_correctness : avl_strategy3
  avl_strategy4_correctness : avl_strategy4
  avl_strategy10_correctness : avl_strategy10
  avl_strategy11_correctness : avl_strategy11
  avl_strategy13_correctness : avl_strategy13
  avl_strategy15_correctness : avl_strategy15
  avl_strategy16_correctness : avl_strategy16
  avl_strategy17_correctness : avl_strategy17
  avl_strategy5_correctness : avl_strategy5
  avl_strategy6_correctness : avl_strategy6

end SimpleC.EE.QCP_demos_LLM.generated.avl_strategy_goal
