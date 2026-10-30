import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.QCP_demos_LLM.poly_sll_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.poly_sll_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance poly_sll_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def reverse_safety_wit_1 : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (p_pre : Int) ,
  ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (sll storeA p_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_entail_wit_1 : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (p_pre : Int) ,
  (sll storeA p_pre l)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (p_pre = p_pre) ”
  &&  (sll storeA (0 : Int) (@List.nil A))
  ** (sll storeA p_pre l)

noncomputable def reverse_entail_wit_2 : Prop :=
  (
forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (p_pre : Int) (w : Int) (v : Int) (PreH1 : (w = (0 : Int))) (PreH2 : (v = p_pre)) ,
  (sll storeA w (@List.nil A))
  ** (sll storeA v l)
|--
  EX l1 : (List A), EX l2 : (List A),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll storeA w l1)
  ** (sll storeA v l2)
) \/
(
forall (A : Type) (l : (List A)) (p_pre : Int) (w : Int) (v : Int) (PreH1 : (w = (0 : Int))) (PreH2 : (v = p_pre)) ,
  TT && emp 
|--
  “ (l = (((@List.nil A)).reverse ++ l)) ”
  &&  emp
)

noncomputable def reverse_entail_wit_2_split_goal_1 : Prop :=
  forall (A : Type) (l : (List A)) (p_pre : Int) (w : Int) (v : Int) (PreH1 : (w = (0 : Int))) (PreH2 : (v = p_pre)) ,
  (l = (((@List.nil A)).reverse ++ l))

noncomputable def reverse_entail_wit_3 : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (v : Int) (w : Int) (l1_2 : (List A)) (l2_2 : (List A)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) ,
  (sll storeA w l1_2)
  ** (sll storeA v l2_2)
|--
  EX vnext : Int, EX vdata : Int, EX x : A, EX xs : (List A), EX l1 : (List A), EX l2 : (List A),
  “ (l = ((l1).reverse ++ l2)) ” &&
  “ (v ≠ (0 : Int)) ” &&
  “ (l2 = (x :: xs)) ”
  &&  (sll storeA w l1)
  ** ((&((v # "list")  ->ₛ "data")) # Ptr |-> (vdata))
  ** (storeA vdata x)
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (vnext))
  ** (sll storeA vnext xs)

noncomputable def reverse_entail_wit_4 : Prop :=
  (
forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (l1_2 : (List A)) (l2_2 : (List A)) (x : A) (xs : (List A)) (vnext : Int) (vdata : Int) (v : Int) (w : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  (sll storeA w l1_2)
  ** ((&((v # "list")  ->ₛ "data")) # Ptr |-> (vdata))
  ** (storeA vdata x)
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (sll storeA vnext xs)
|--
  EX l1 : (List A), EX l2 : (List A),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll storeA v l1)
  ** (sll storeA vnext l2)
) \/
(
forall (A : Type) (l : (List A)) (l1_2 : (List A)) (l2_2 : (List A)) (x : A) (xs : (List A)) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  TT && emp 
|--
  “ (l = (((x :: l1_2)).reverse ++ xs)) ”
  &&  emp
)

noncomputable def reverse_entail_wit_4_split_goal_1 : Prop :=
  forall (A : Type) (l : (List A)) (l1_2 : (List A)) (l2_2 : (List A)) (x : A) (xs : (List A)) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  (l = (((x :: l1_2)).reverse ++ xs))

noncomputable def reverse_return_wit_1 : Prop :=
  (
forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (v : Int) (w : Int) (l1 : (List A)) (l2 : (List A)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll storeA w l1)
  ** (sll storeA v l2)
|--
  (sll storeA w (l).reverse)
) \/
(
forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (v : Int) (l1 : (List A)) (l2 : (List A)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll storeA v l2)
|--
  “ (l1 = (l).reverse) ”
  &&  emp
)

noncomputable def reverse_return_wit_1_split_goal_1 : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (v : Int) (l1 : (List A)) (l2 : (List A)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll storeA v l2)
|--
  “ (l1 = (l).reverse) ”

noncomputable def reverse_return_wit_1_split_goal_spatial : Prop :=
  forall (A : Type) (l : (List A)) (storeA : (Int -> (A -> Assertion))) (v : Int) (l1 : (List A)) (l2 : (List A)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll storeA v l2)
|--
  TT && emp 


structure VC_Correct : Type where
  proof_of_reverse_safety_wit_1 : reverse_safety_wit_1
  proof_of_reverse_entail_wit_1 : reverse_entail_wit_1
  proof_of_reverse_entail_wit_3 : reverse_entail_wit_3
  proof_of_reverse_entail_wit_2 : reverse_entail_wit_2
  proof_of_reverse_entail_wit_4 : reverse_entail_wit_4
  proof_of_reverse_return_wit_1 : reverse_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.poly_sll_goal
