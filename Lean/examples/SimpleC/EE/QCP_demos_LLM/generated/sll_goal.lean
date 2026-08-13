import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def length_safety_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (sll p_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def length_safety_wit_2 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (pnext : Int) (pdata : Int) (n : Int) (p : Int) (PreH1 : (l = (l1 ++ l2))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l2 = (pdata :: l3))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1)
  ** (sll pnext l3)
|--
  “ ((n + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n + 1)) ”
) \/
(
forall (p_pre : Int) (l : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (pnext : Int) (pdata : Int) (n : Int) (p : Int) (PreH1 : (l = (l1 ++ l2))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l2 = (pdata :: l3))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1)
  ** (sll pnext l3)
|--
  “ ((n + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n + 1)) ”
)

noncomputable def length_safety_wit_2_split_goal_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (pnext : Int) (pdata : Int) (n : Int) (p : Int) (PreH1 : (l = (l1 ++ l2))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l2 = (pdata :: l3))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1)
  ** (sll pnext l3)
|--
  “ ((n + 1) <= INT_MAX) ”

noncomputable def length_safety_wit_2_split_goal_2 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (l1 : (List Int)) (l2 : (List Int)) (l3 : (List Int)) (pnext : Int) (pdata : Int) (n : Int) (p : Int) (PreH1 : (l = (l1 ++ l2))) (PreH2 : (n = (Zlength (l1)))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l2 = (pdata :: l3))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1)
  ** (sll pnext l3)
|--
  “ ((INT_MIN) <= (n + 1)) ”

noncomputable def length_entail_wit_1 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (sll p_pre l)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((Zlength (l)) <= INT_MAX) ” &&
  “ ((0 : Int) = (Zlength (l1))) ”
  &&  (sllseg p_pre p_pre l1)
  ** (sll p_pre l2)
) \/
(
forall (l : (List Int)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 : Int) = (Zlength ((@List.nil Int)))) ” &&
  “ (l = ((@List.nil Int) ++ l)) ”
  &&  emp
)

noncomputable def length_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  ((0 : Int) = (Zlength ((@List.nil Int))))

noncomputable def length_entail_wit_1_split_goal_2 : Prop :=
  forall (l : (List Int)) (PreH1 : ((Zlength (l)) <= INT_MAX)) ,
  (l = ((@List.nil Int) ++ l))

noncomputable def length_entail_wit_2 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (p : Int) (n : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (l = (l1_2 ++ l2_2))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1_2)))) (PreH4 : (p ≠ (0 : Int))) ,
  (sllseg p_pre p l1_2)
  ** (sll p l2_2)
|--
  EX pnext : Int, EX pdata : Int, EX l3 : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ (n = (Zlength (l1))) ” &&
  “ (p ≠ (0 : Int)) ” &&
  “ (l2 = (pdata :: l3)) ” &&
  “ ((Zlength (l)) <= INT_MAX) ”
  &&  ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1)
  ** (sll pnext l3)

noncomputable def length_entail_wit_3 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l3 : (List Int)) (pnext : Int) (pdata : Int) (n : Int) (p : Int) (PreH1 : (l = (l1_2 ++ l2_2))) (PreH2 : (n = (Zlength (l1_2)))) (PreH3 : (p ≠ (0 : Int))) (PreH4 : (l2_2 = (pdata :: l3))) (PreH5 : ((Zlength (l)) <= INT_MAX)) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1_2)
  ** (sll pnext l3)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = (l1 ++ l2)) ” &&
  “ ((Zlength (l)) <= INT_MAX) ” &&
  “ ((n + 1) = (Zlength (l1))) ”
  &&  (sllseg p_pre pnext l1)
  ** (sll pnext l2)
) \/
(
forall (p_pre : Int) (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l3 : (List Int)) (pnext : Int) (pdata : Int) (n : Int) (p : Int) (PreH1 : (pdata <= INT_MAX)) (PreH2 : (pdata >= INT_MIN)) (PreH3 : (l = (l1_2 ++ l2_2))) (PreH4 : (n = (Zlength (l1_2)))) (PreH5 : (p ≠ (0 : Int))) (PreH6 : (l2_2 = (pdata :: l3))) (PreH7 : ((Zlength (l)) <= INT_MAX)) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (pdata))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (pnext))
  ** (sllseg p_pre p l1_2)
|--
  EX l1 : (List Int),
  “ (l = (l1 ++ l3)) ” &&
  “ ((Zlength (l)) <= INT_MAX) ” &&
  “ ((n + 1) = (Zlength (l1))) ”
  &&  (sllseg p_pre pnext l1)
)

noncomputable def length_return_wit_1 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) (p : Int) (n : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = (l1 ++ l2))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = (0 : Int))) ,
  (sllseg p_pre p l1)
  ** (sll p l2)
|--
  “ (n = (Zlength (l))) ”
  &&  (sll p_pre l)
) \/
(
forall (p_pre : Int) (l : (List Int)) (p : Int) (n : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = (l1 ++ l2))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = (0 : Int))) ,
  (sllseg p_pre p l1)
  ** (sll p l2)
|--
  “ (n = (Zlength (l))) ”
  &&  (sll p_pre l)
)

noncomputable def length_return_wit_1_split_goal_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (p : Int) (n : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = (l1 ++ l2))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = (0 : Int))) ,
  (sllseg p_pre p l1)
  ** (sll p l2)
|--
  “ (n = (Zlength (l))) ”

noncomputable def length_return_wit_1_split_goal_spatial : Prop :=
  forall (p_pre : Int) (l : (List Int)) (p : Int) (n : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = (l1 ++ l2))) (PreH2 : ((Zlength (l)) <= INT_MAX)) (PreH3 : (n = (Zlength (l1)))) (PreH4 : (p = (0 : Int))) ,
  (sllseg p_pre p l1)
  ** (sll p l2)
|--
  (sll p_pre l)

noncomputable def reverse_safety_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) ,
  ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (sll p_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_entail_wit_1 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) ,
  (sll p_pre l)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll (0 : Int) l1)
  ** (sll p_pre l2)
) \/
(
forall (l : (List Int)) ,
  TT && emp 
|--
  “ (l = (((@List.nil Int)).reverse ++ l)) ”
  &&  emp
)

noncomputable def reverse_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) ,
  (l = (((@List.nil Int)).reverse ++ l))

noncomputable def reverse_entail_wit_2 : Prop :=
  forall (l : (List Int)) (v : Int) (w : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) ,
  (sll w l1_2)
  ** (sll v l2_2)
|--
  EX vnext : Int, EX vdata : Int, EX l2_new : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ” &&
  “ (v ≠ (0 : Int)) ” &&
  “ (l2 = (vdata :: l2_new)) ”
  &&  (sll w l1)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (vdata))
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (vnext))
  ** (sll vnext l2_new)

noncomputable def reverse_entail_wit_3 : Prop :=
  (
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l2_new : (List Int)) (vnext : Int) (vdata : Int) (v : Int) (w : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (vdata :: l2_new))) ,
  (sll w l1_2)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (vdata))
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (sll vnext l2_new)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll v l1)
  ** (sll vnext l2)
) \/
(
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l2_new : (List Int)) (vdata : Int) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (vdata :: l2_new))) ,
  TT && emp 
|--
  “ (l = (((vdata :: l1_2)).reverse ++ l2_new)) ”
  &&  emp
)

noncomputable def reverse_entail_wit_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l2_new : (List Int)) (vdata : Int) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (vdata :: l2_new))) ,
  (l = (((vdata :: l1_2)).reverse ++ l2_new))

noncomputable def reverse_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (v : Int) (w : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll w l1)
  ** (sll v l2)
|--
  (sll w (l).reverse)
) \/
(
forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  “ (l1 = (l).reverse) ”
  &&  emp
)

noncomputable def reverse_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  “ (l1 = (l).reverse) ”

noncomputable def reverse_return_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  TT && emp 

noncomputable def reverse_alter_style1_safety_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) ,
  ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (sll p_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_alter_style1_entail_wit_1 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) ,
  (sll p_pre l)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll (0 : Int) l1)
  ** (sll p_pre l2)
) \/
(
forall (l : (List Int)) ,
  TT && emp 
|--
  “ (l = (((@List.nil Int)).reverse ++ l)) ”
  &&  emp
)

noncomputable def reverse_alter_style1_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) ,
  (l = (((@List.nil Int)).reverse ++ l))

noncomputable def reverse_alter_style1_entail_wit_2 : Prop :=
  forall (l : (List Int)) (v : Int) (w : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) ,
  (sll w l1_2)
  ** (sll v l2_2)
|--
  EX vn : Int, EX x : Int, EX xs : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ” &&
  “ (v ≠ (0 : Int)) ” &&
  “ (l2 = (x :: xs)) ”
  &&  (sll w l1)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (vn))
  ** (sll vn xs)

noncomputable def reverse_alter_style1_entail_wit_3 : Prop :=
  (
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (xs : (List Int)) (vn : Int) (v : Int) (w : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  (sll w l1_2)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (sll vn xs)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll v l1)
  ** (sll vn l2)
) \/
(
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (xs : (List Int)) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  TT && emp 
|--
  “ (l = (((x :: l1_2)).reverse ++ xs)) ”
  &&  emp
)

noncomputable def reverse_alter_style1_entail_wit_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (x : Int) (xs : (List Int)) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  (l = (((x :: l1_2)).reverse ++ xs))

noncomputable def reverse_alter_style1_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (v : Int) (w : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll w l1)
  ** (sll v l2)
|--
  (sll w (l).reverse)
) \/
(
forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  “ (l1 = (l).reverse) ”
  &&  emp
)

noncomputable def reverse_alter_style1_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  “ (l1 = (l).reverse) ”

noncomputable def reverse_alter_style1_return_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  TT && emp 

noncomputable def reverse_alter_style2_safety_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) ,
  ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (sll p_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_alter_style2_entail_wit_1 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) ,
  (sll p_pre l)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll (0 : Int) l1)
  ** (sll p_pre l2)
) \/
(
forall (l : (List Int)) ,
  TT && emp 
|--
  “ (l = (((@List.nil Int)).reverse ++ l)) ”
  &&  emp
)

noncomputable def reverse_alter_style2_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) ,
  (l = (((@List.nil Int)).reverse ++ l))

noncomputable def reverse_alter_style2_entail_wit_2 : Prop :=
  forall (l : (List Int)) (v_inv : Int) (w_inv : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v_inv ≠ (0 : Int))) ,
  (sll w_inv l1_2)
  ** (sll v_inv l2_2)
|--
  EX v_inv_next : Int, EX x : Int, EX xs : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ” &&
  “ (v_inv ≠ (0 : Int)) ” &&
  “ (l2 = (x :: xs)) ”
  &&  (sll w_inv l1)
  ** ((&((v_inv # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((v_inv # "list")  ->ₛ "next")) # Ptr |-> (v_inv_next))
  ** (sll v_inv_next xs)

noncomputable def reverse_alter_style2_entail_wit_3 : Prop :=
  (
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (w_inv : Int) (v_inv : Int) (x : Int) (xs : (List Int)) (v_inv_next : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v_inv ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  (sll w_inv l1_2)
  ** ((&((v_inv # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((v_inv # "list")  ->ₛ "next")) # Ptr |-> (w_inv))
  ** (sll v_inv_next xs)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll v_inv l1)
  ** (sll v_inv_next l2)
) \/
(
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (v_inv : Int) (x : Int) (xs : (List Int)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v_inv ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  TT && emp 
|--
  “ (l = (((x :: l1_2)).reverse ++ xs)) ”
  &&  emp
)

noncomputable def reverse_alter_style2_entail_wit_3_split_goal_1 : Prop :=
  forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (v_inv : Int) (x : Int) (xs : (List Int)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v_inv ≠ (0 : Int))) (PreH3 : (l2_2 = (x :: xs))) ,
  (l = (((x :: l1_2)).reverse ++ xs))

noncomputable def reverse_alter_style2_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (v_inv : Int) (w_inv : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v_inv = (0 : Int))) ,
  (sll w_inv l1)
  ** (sll v_inv l2)
|--
  (sll w_inv (l).reverse)
) \/
(
forall (l : (List Int)) (v_inv : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v_inv = (0 : Int))) ,
  (sll v_inv l2)
|--
  “ (l1 = (l).reverse) ”
  &&  emp
)

noncomputable def reverse_alter_style2_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (v_inv : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v_inv = (0 : Int))) ,
  (sll v_inv l2)
|--
  “ (l1 = (l).reverse) ”

noncomputable def reverse_alter_style2_return_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (v_inv : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v_inv = (0 : Int))) ,
  (sll v_inv l2)
|--
  TT && emp 

noncomputable def reverse_alter_style3_safety_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) ,
  ((( &( "v" ) )) # Ptr |->_)
  ** ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (sll p_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_alter_style3_entail_wit_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) ,
  (sll p_pre l)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (p_pre = p_pre) ”
  &&  (sll (0 : Int) (@List.nil Int))
  ** (sll p_pre l)

noncomputable def reverse_alter_style3_entail_wit_2 : Prop :=
  (
forall (p_pre : Int) (l : (List Int)) (w : Int) (v : Int) (PreH1 : (w = (0 : Int))) (PreH2 : (v = p_pre)) ,
  (sll w (@List.nil Int))
  ** (sll v l)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll w l1)
  ** (sll v l2)
) \/
(
forall (p_pre : Int) (l : (List Int)) (w : Int) (v : Int) (PreH1 : (w = (0 : Int))) (PreH2 : (w = (0 : Int))) (PreH3 : (v = p_pre)) ,
  TT && emp 
|--
  “ (l = (((@List.nil Int)).reverse ++ l)) ”
  &&  emp
)

noncomputable def reverse_alter_style3_entail_wit_2_split_goal_1 : Prop :=
  forall (p_pre : Int) (l : (List Int)) (w : Int) (v : Int) (PreH1 : (w = (0 : Int))) (PreH2 : (w = (0 : Int))) (PreH3 : (v = p_pre)) ,
  (l = (((@List.nil Int)).reverse ++ l))

noncomputable def reverse_alter_style3_entail_wit_3 : Prop :=
  forall (l : (List Int)) (v : Int) (w : Int) (l1_2 : (List Int)) (l2_2 : (List Int)) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) ,
  (sll w l1_2)
  ** (sll v l2_2)
|--
  EX vnext : Int, EX vdata : Int, EX l2_new : (List Int), EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ” &&
  “ (v ≠ (0 : Int)) ” &&
  “ (l2 = (vdata :: l2_new)) ”
  &&  (sll w l1)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (vdata))
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (vnext))
  ** (sll vnext l2_new)

noncomputable def reverse_alter_style3_entail_wit_4 : Prop :=
  (
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l2_new : (List Int)) (vnext : Int) (vdata : Int) (v : Int) (w : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (vdata :: l2_new))) ,
  (sll w l1_2)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (vdata))
  ** ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (sll vnext l2_new)
|--
  EX l1 : (List Int), EX l2 : (List Int),
  “ (l = ((l1).reverse ++ l2)) ”
  &&  (sll v l1)
  ** (sll vnext l2)
) \/
(
forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l2_new : (List Int)) (vdata : Int) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (vdata :: l2_new))) ,
  TT && emp 
|--
  “ (l = (((vdata :: l1_2)).reverse ++ l2_new)) ”
  &&  emp
)

noncomputable def reverse_alter_style3_entail_wit_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (l1_2 : (List Int)) (l2_2 : (List Int)) (l2_new : (List Int)) (vdata : Int) (v : Int) (PreH1 : (l = ((l1_2).reverse ++ l2_2))) (PreH2 : (v ≠ (0 : Int))) (PreH3 : (l2_2 = (vdata :: l2_new))) ,
  (l = (((vdata :: l1_2)).reverse ++ l2_new))

noncomputable def reverse_alter_style3_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (v : Int) (w : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll w l1)
  ** (sll v l2)
|--
  (sll w (l).reverse)
) \/
(
forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  “ (l1 = (l).reverse) ”
  &&  emp
)

noncomputable def reverse_alter_style3_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  “ (l1 = (l).reverse) ”

noncomputable def reverse_alter_style3_return_wit_1_split_goal_spatial : Prop :=
  forall (l : (List Int)) (v : Int) (l1 : (List Int)) (l2 : (List Int)) (PreH1 : (l = ((l1).reverse ++ l2))) (PreH2 : (v = (0 : Int))) ,
  (sll v l2)
|--
  TT && emp 

noncomputable def append_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) ,
  ((( &( "u" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** (sll x_pre l1)
  ** (sll y_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next : Int) (l1a : (List Int)) (t_data : Int) (t : Int) (l1b : (List Int)) (PreH1 : ((l1a ++ (t_data :: l1b)) = l1)) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (t ≠ (0 : Int))) (PreH4 : (t_next = u)) ,
  ((( &( "t" ) )) # Ptr |-> (t))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((( &( "u" ) )) # Ptr |-> (u))
  ** (sllseg x_pre t l1a)
  ** (sll u l1b)
  ** (sll y_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (sll x_pre l1)
  ** (sll y_pre l2)
|--
  EX xn : Int, EX a : Int, EX l1n : (List Int),
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (l1 = (a :: l1n)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (xn))
  ** (sll xn l1n)
  ** (sll y_pre l2)

noncomputable def append_entail_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (a : Int) (l1n : (List Int)) (xn : Int) (PreH1 : (x_pre ≠ (0 : Int))) (PreH2 : (l1 = (a :: l1n))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (xn))
  ** (sll xn l1n)
  ** (sll y_pre l2)
|--
  EX t_next : Int, EX l1a : (List Int), EX t_data : Int, EX l1b : (List Int),
  “ ((l1a ++ (t_data :: l1b)) = l1) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (t_next = xn) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (t_data))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (sllseg x_pre x_pre l1a)
  ** (sll xn l1b)
  ** (sll y_pre l2)
) \/
(
forall (x_pre : Int) (l1 : (List Int)) (a : Int) (l1n : (List Int)) (PreH1 : (x_pre ≠ (0 : Int))) (PreH2 : (l1 = (a :: l1n))) ,
  TT && emp 
|--
  “ (((@List.nil Int) ++ (a :: l1n)) = l1) ”
  &&  emp
)

noncomputable def append_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (l1 : (List Int)) (a : Int) (l1n : (List Int)) (PreH1 : (x_pre ≠ (0 : Int))) (PreH2 : (l1 = (a :: l1n))) ,
  (((@List.nil Int) ++ (a :: l1n)) = l1)

noncomputable def append_entail_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next_2 : Int) (l1a_2 : (List Int)) (t_data_2 : Int) (t : Int) (l1b_2 : (List Int)) (PreH1 : (u ≠ (0 : Int))) (PreH2 : ((l1a_2 ++ (t_data_2 :: l1b_2)) = l1)) (PreH3 : (x_pre ≠ (0 : Int))) (PreH4 : (t ≠ (0 : Int))) (PreH5 : (t_next_2 = u)) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** (sllseg x_pre t l1a_2)
  ** (sll u l1b_2)
  ** (sll y_pre l2)
|--
  EX unext : Int, EX udata : Int, EX l1b_new : (List Int), EX t_next : Int, EX l1a : (List Int), EX t_data : Int, EX l1b : (List Int),
  “ ((l1a ++ (t_data :: l1b)) = l1) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (t_next = u) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (l1b = (udata :: l1b_new)) ”
  &&  ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (sllseg x_pre t l1a)
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (udata))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l1b_new)
  ** (sll y_pre l2)

noncomputable def append_entail_wit_4 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l1a_2 : (List Int)) (l1b_2 : (List Int)) (l1b_new : (List Int)) (udata : Int) (unext : Int) (t : Int) (t_data_2 : Int) (t_next_2 : Int) (u : Int) (PreH1 : ((l1a_2 ++ (t_data_2 :: l1b_2)) = l1)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (t_next_2 = u)) (PreH4 : (u ≠ (0 : Int))) (PreH5 : (x_pre ≠ (0 : Int))) (PreH6 : (l1b_2 = (udata :: l1b_new))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** (sllseg x_pre t l1a_2)
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (udata))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (unext))
  ** (sll unext l1b_new)
  ** (sll y_pre l2)
|--
  EX t_next : Int, EX l1a : (List Int), EX t_data : Int, EX l1b : (List Int),
  “ ((l1a ++ (t_data :: l1b)) = l1) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (t_next = unext) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (t_data))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (sllseg x_pre u l1a)
  ** (sll unext l1b)
  ** (sll y_pre l2)
) \/
(
forall (x_pre : Int) (l1 : (List Int)) (l1a_2 : (List Int)) (l1b_2 : (List Int)) (l1b_new : (List Int)) (udata : Int) (t : Int) (t_data_2 : Int) (t_next_2 : Int) (u : Int) (PreH1 : (t_data_2 <= INT_MAX)) (PreH2 : (t_data_2 >= INT_MIN)) (PreH3 : ((l1a_2 ++ (t_data_2 :: l1b_2)) = l1)) (PreH4 : (t ≠ (0 : Int))) (PreH5 : (t_next_2 = u)) (PreH6 : (u ≠ (0 : Int))) (PreH7 : (x_pre ≠ (0 : Int))) (PreH8 : (l1b_2 = (udata :: l1b_new))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** (sllseg x_pre t l1a_2)
|--
  EX l1a : (List Int),
  “ ((l1a ++ (udata :: l1b_new)) = l1) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  (sllseg x_pre u l1a)
)

noncomputable def append_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next : Int) (l1a : (List Int)) (t_data : Int) (t : Int) (l1b : (List Int)) (PreH1 : (u = (0 : Int))) (PreH2 : ((l1a ++ (t_data :: l1b)) = l1)) (PreH3 : (x_pre ≠ (0 : Int))) (PreH4 : (t ≠ (0 : Int))) (PreH5 : (t_next = u)) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (sllseg x_pre t l1a)
  ** (sll u l1b)
  ** (sll y_pre l2)
|--
  (sll x_pre (l1 ++ l2))
) \/
(
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next : Int) (l1a : (List Int)) (t_data : Int) (t : Int) (l1b : (List Int)) (PreH1 : (t_data <= INT_MAX)) (PreH2 : (t_data >= INT_MIN)) (PreH3 : (u = (0 : Int))) (PreH4 : ((l1a ++ (t_data :: l1b)) = l1)) (PreH5 : (x_pre ≠ (0 : Int))) (PreH6 : (t ≠ (0 : Int))) (PreH7 : (t_next = u)) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (t_data))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (sllseg x_pre t l1a)
  ** (sll u l1b)
  ** (sll y_pre l2)
|--
  EX y : Int, EX l0 : (List Int), EX x : Int,
  “ (x_pre ≠ (0 : Int)) ” &&
  “ ((l1 ++ l2) = (x :: l0)) ”
  &&  (sll y l0)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
)

noncomputable def append_return_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
  ** (sll y_pre l2)
|--
  (sll y_pre (l1 ++ l2))
) \/
(
forall (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
|--
  “ (l2 = (l1 ++ l2)) ”
  &&  emp
)

noncomputable def append_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
|--
  “ (l2 = (l1 ++ l2)) ”

noncomputable def append_return_wit_2_split_goal_spatial : Prop :=
  forall (x_pre : Int) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
|--
  TT && emp 

noncomputable def append_long_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) ,
  ((( &( "u" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** (sll x_pre l1)
  ** (sll y_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_long_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (x_pre ≠ (0 : Int))) (PreH2 : (l1 = (a :: l1b))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "u" ) )) # Ptr |-> (xn))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (xn))
  ** (sll xn l1b)
  ** (sll y_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_long_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next : Int) (t : Int) (l1a : (List Int)) (b : Int) (l1c : (List Int)) (PreH1 : ((l1a ++ (b :: l1c)) = l1)) (PreH2 : (t_next = u)) (PreH3 : (t ≠ (0 : Int))) (PreH4 : (x_pre ≠ (0 : Int))) ,
  ((( &( "t" ) )) # Ptr |-> (t))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (b))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((( &( "u" ) )) # Ptr |-> (u))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** (sllseg x_pre t l1a)
  ** (sll u l1c)
  ** (sll y_pre l2)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_long_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (sll x_pre l1)
  ** (sll y_pre l2)
|--
  EX xn : Int, EX a : Int, EX l1b : (List Int),
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (l1 = (a :: l1b)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (xn))
  ** (sll xn l1b)
  ** (sll y_pre l2)

noncomputable def append_long_entail_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn ≠ (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (xn))
  ** (sll xn l1b)
  ** (sll y_pre l2)
|--
  EX t_next : Int, EX l1a : (List Int), EX b : Int, EX l1c : (List Int),
  “ ((l1a ++ (b :: l1c)) = l1) ” &&
  “ (t_next = xn) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (b))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (sllseg x_pre x_pre l1a)
  ** (sll xn l1c)
  ** (sll y_pre l2)
) \/
(
forall (x_pre : Int) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn ≠ (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  TT && emp 
|--
  “ (((@List.nil Int) ++ (a :: l1b)) = l1) ”
  &&  emp
)

noncomputable def append_long_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn ≠ (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  (((@List.nil Int) ++ (a :: l1b)) = l1)

noncomputable def append_long_entail_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next_2 : Int) (t : Int) (l1a_2 : (List Int)) (b_2 : Int) (l1c_2 : (List Int)) (PreH1 : (u ≠ (0 : Int))) (PreH2 : ((l1a_2 ++ (b_2 :: l1c_2)) = l1)) (PreH3 : (t_next_2 = u)) (PreH4 : (t ≠ (0 : Int))) (PreH5 : (x_pre ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (b_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** (sllseg x_pre t l1a_2)
  ** (sll u l1c_2)
  ** (sll y_pre l2)
|--
  EX un : Int, EX c : Int, EX l1d : (List Int), EX t_next : Int, EX l1a : (List Int), EX b : Int, EX l1c : (List Int),
  “ ((l1a ++ (b :: l1c)) = l1) ” &&
  “ (t_next = u) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (x_pre ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (l1c = (c :: l1d)) ”
  &&  ((&((t # "list")  ->ₛ "data")) # Int |-> (b))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (c))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (un))
  ** (sllseg x_pre t l1a)
  ** (sll un l1d)
  ** (sll y_pre l2)

noncomputable def append_long_entail_wit_4 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (l1a_2 : (List Int)) (b_2 : Int) (l1c_2 : (List Int)) (l1d : (List Int)) (c : Int) (un : Int) (t : Int) (t_next_2 : Int) (u : Int) (PreH1 : ((l1a_2 ++ (b_2 :: l1c_2)) = l1)) (PreH2 : (t_next_2 = u)) (PreH3 : (t ≠ (0 : Int))) (PreH4 : (x_pre ≠ (0 : Int))) (PreH5 : (u ≠ (0 : Int))) (PreH6 : (l1c_2 = (c :: l1d))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (b_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (c))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (un))
  ** (sllseg x_pre t l1a_2)
  ** (sll un l1d)
  ** (sll y_pre l2)
|--
  EX t_next : Int, EX l1a : (List Int), EX b : Int, EX l1c : (List Int),
  “ ((l1a ++ (b :: l1c)) = l1) ” &&
  “ (t_next = un) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (b))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (sllseg x_pre u l1a)
  ** (sll un l1c)
  ** (sll y_pre l2)
) \/
(
forall (x_pre : Int) (l1 : (List Int)) (l1a_2 : (List Int)) (b_2 : Int) (l1c_2 : (List Int)) (l1d : (List Int)) (c : Int) (t : Int) (t_next_2 : Int) (u : Int) (PreH1 : (b_2 <= INT_MAX)) (PreH2 : (b_2 >= INT_MIN)) (PreH3 : ((l1a_2 ++ (b_2 :: l1c_2)) = l1)) (PreH4 : (t_next_2 = u)) (PreH5 : (t ≠ (0 : Int))) (PreH6 : (x_pre ≠ (0 : Int))) (PreH7 : (u ≠ (0 : Int))) (PreH8 : (l1c_2 = (c :: l1d))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (b_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** (sllseg x_pre t l1a_2)
|--
  EX l1a : (List Int),
  “ ((l1a ++ (c :: l1d)) = l1) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  (sllseg x_pre u l1a)
)

noncomputable def append_long_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next : Int) (t : Int) (l1a : (List Int)) (b : Int) (l1c : (List Int)) (PreH1 : (u = (0 : Int))) (PreH2 : ((l1a ++ (b :: l1c)) = l1)) (PreH3 : (t_next = u)) (PreH4 : (t ≠ (0 : Int))) (PreH5 : (x_pre ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (b))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (sllseg x_pre t l1a)
  ** (sll u l1c)
  ** (sll y_pre l2)
|--
  (sll x_pre (l1 ++ l2))
) \/
(
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (u : Int) (t_next : Int) (t : Int) (l1a : (List Int)) (b : Int) (l1c : (List Int)) (PreH1 : (b <= INT_MAX)) (PreH2 : (b >= INT_MIN)) (PreH3 : (u = (0 : Int))) (PreH4 : ((l1a ++ (b :: l1c)) = l1)) (PreH5 : (t_next = u)) (PreH6 : (t ≠ (0 : Int))) (PreH7 : (x_pre ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (b))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (sllseg x_pre t l1a)
  ** (sll u l1c)
  ** (sll y_pre l2)
|--
  EX y : Int, EX l0 : (List Int), EX x : Int,
  “ (x_pre ≠ (0 : Int)) ” &&
  “ ((l1 ++ l2) = (x :: l0)) ”
  &&  (sll y l0)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
)

noncomputable def append_long_return_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn = (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (a))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (sll xn l1b)
  ** (sll y_pre l2)
|--
  (sll x_pre (l1 ++ l2))
) \/
(
forall (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn = (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  (sll xn l1b)
|--
  “ ((l1 ++ l2) = (a :: l2)) ”
  &&  emp
)

noncomputable def append_long_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn = (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  (sll xn l1b)
|--
  “ ((l1 ++ l2) = (a :: l2)) ”

noncomputable def append_long_return_wit_2_split_goal_spatial : Prop :=
  forall (x_pre : Int) (l1 : (List Int)) (a : Int) (l1b : (List Int)) (xn : Int) (PreH1 : (xn = (0 : Int))) (PreH2 : (x_pre ≠ (0 : Int))) (PreH3 : (l1 = (a :: l1b))) ,
  (sll xn l1b)
|--
  TT && emp 

noncomputable def append_long_return_wit_3 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
  ** (sll y_pre l2)
|--
  (sll y_pre (l1 ++ l2))
) \/
(
forall (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
|--
  “ (l2 = (l1 ++ l2)) ”
  &&  emp
)

noncomputable def append_long_return_wit_3_split_goal_1 : Prop :=
  forall (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
|--
  “ (l2 = (l1 ++ l2)) ”

noncomputable def append_long_return_wit_3_split_goal_spatial : Prop :=
  forall (x_pre : Int) (l1 : (List Int)) (PreH1 : (x_pre = (0 : Int))) ,
  (sll x_pre l1)
|--
  TT && emp 

noncomputable def append_2p_entail_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (l2 : (List Int)) (l1 : (List Int)) ,
  (sll x_pre l1)
  ** (sll y_pre l2)
|--
  EX l1a : (List Int), EX l1b : (List Int),
  “ ((l1a ++ l1b) = l1) ”
  &&  (sllbseg ( &( "x" ) ) ( &( "x" ) ) l1a)
  ** (sll x_pre l1b)
  ** (sll y_pre l2)
) \/
(
forall (l1 : (List Int)) ,
  TT && emp 
|--
  EX l1a : (List Int),
  “ ((l1a ++ l1) = l1) ”
  &&  (sllbseg ( &( "x" ) ) ( &( "x" ) ) l1a)
)

noncomputable def append_2p_entail_wit_2 : Prop :=
  (
forall (y_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (ptvv_2 : Int) (ptv : Int) (l1a_2 : (List Int)) (l1b_2 : (List Int)) (PreH1 : ((l1a_2 ++ l1b_2) = l1)) (PreH2 : (ptvv_2 ≠ (0 : Int))) ,
  ((ptv) # Ptr |-> (ptvv_2))
  ** (sllbseg ( &( "x" ) ) ptv l1a_2)
  ** (sll ptvv_2 l1b_2)
  ** (sll y_pre l2)
|--
  EX ptvv : Int, EX l1a : (List Int), EX l1b : (List Int),
  “ ((l1a ++ l1b) = l1) ”
  &&  ((&((ptvv_2 # "list")  ->ₛ "next")) # Ptr |-> (ptvv))
  ** (sllbseg ( &( "x" ) ) &((ptvv_2 # "list")  ->ₛ "next") l1a)
  ** (sll ptvv l1b)
  ** (sll y_pre l2)
) \/
(
forall (l1 : (List Int)) (ptvv_2 : Int) (ptv : Int) (l1a_2 : (List Int)) (l1b_2 : (List Int)) (x : Int) (l0 : (List Int)) (PreH1 : (x <= INT_MAX)) (PreH2 : (x >= INT_MIN)) (PreH3 : (l1b_2 = (x :: l0))) (PreH4 : ((l1a_2 ++ l1b_2) = l1)) (PreH5 : (ptvv_2 ≠ (0 : Int))) ,
  ((&((ptvv_2 # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((ptv) # Ptr |-> (ptvv_2))
  ** (sllbseg ( &( "x" ) ) ptv l1a_2)
|--
  EX l1a : (List Int),
  “ ((l1a ++ l0) = l1) ”
  &&  (sllbseg ( &( "x" ) ) &((ptvv_2 # "list")  ->ₛ "next") l1a)
)

noncomputable def append_2p_entail_wit_3 : Prop :=
  (
forall (y_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (ptvv : Int) (ptv : Int) (l1a : (List Int)) (l1b : (List Int)) (PreH1 : ((l1a ++ l1b) = l1)) (PreH2 : (ptvv = (0 : Int))) ,
  ((ptv) # Ptr |-> (y_pre))
  ** (sllbseg ( &( "x" ) ) ptv l1a)
  ** (sll ptvv l1b)
  ** (sll y_pre l2)
|--
  EX presv : Int,
  ((( &( "x" ) )) # Ptr |-> (presv))
  ** (sllseg presv y_pre l1)
  ** (sll y_pre l2)
) \/
(
forall (y_pre : Int) (l1 : (List Int)) (ptvv : Int) (ptv : Int) (l1a : (List Int)) (l1b : (List Int)) (PreH1 : ((l1a ++ l1b) = l1)) (PreH2 : (ptvv = (0 : Int))) ,
  ((ptv) # Ptr |-> (y_pre))
  ** (sllbseg ( &( "x" ) ) ptv l1a)
  ** (sll ptvv l1b)
|--
  EX presv : Int,
  ((( &( "x" ) )) # Ptr |-> (presv))
  ** (sllseg presv y_pre l1)
)

noncomputable def append_2p_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (presv : Int) ,
  (sllseg presv y_pre l1)
  ** (sll y_pre l2)
|--
  (sll presv (l1 ++ l2))
) \/
(
forall (y_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (presv : Int) ,
  (sllseg presv y_pre l1)
  ** (sll y_pre l2)
|--
  (sll presv (l1 ++ l2))
)

noncomputable def append_2p_return_wit_1_split_goal_spatial : Prop :=
  forall (y_pre : Int) (l2 : (List Int)) (l1 : (List Int)) (presv : Int) ,
  (sllseg presv y_pre l1)
  ** (sll y_pre l2)
|--
  (sll presv (l1 ++ l2))


structure VC_Correct : Type where
  proof_of_length_safety_wit_1 : length_safety_wit_1
  proof_of_length_entail_wit_2 : length_entail_wit_2
  proof_of_reverse_safety_wit_1 : reverse_safety_wit_1
  proof_of_reverse_entail_wit_2 : reverse_entail_wit_2
  proof_of_reverse_alter_style1_safety_wit_1 : reverse_alter_style1_safety_wit_1
  proof_of_reverse_alter_style1_entail_wit_2 : reverse_alter_style1_entail_wit_2
  proof_of_reverse_alter_style2_safety_wit_1 : reverse_alter_style2_safety_wit_1
  proof_of_reverse_alter_style2_entail_wit_2 : reverse_alter_style2_entail_wit_2
  proof_of_reverse_alter_style3_safety_wit_1 : reverse_alter_style3_safety_wit_1
  proof_of_reverse_alter_style3_entail_wit_1 : reverse_alter_style3_entail_wit_1
  proof_of_reverse_alter_style3_entail_wit_3 : reverse_alter_style3_entail_wit_3
  proof_of_append_safety_wit_1 : append_safety_wit_1
  proof_of_append_safety_wit_2 : append_safety_wit_2
  proof_of_append_entail_wit_1 : append_entail_wit_1
  proof_of_append_entail_wit_3 : append_entail_wit_3
  proof_of_append_long_safety_wit_1 : append_long_safety_wit_1
  proof_of_append_long_safety_wit_2 : append_long_safety_wit_2
  proof_of_append_long_safety_wit_3 : append_long_safety_wit_3
  proof_of_append_long_entail_wit_1 : append_long_entail_wit_1
  proof_of_append_long_entail_wit_3 : append_long_entail_wit_3
  proof_of_length_safety_wit_2 : length_safety_wit_2
  proof_of_length_entail_wit_1 : length_entail_wit_1
  proof_of_length_entail_wit_3 : length_entail_wit_3
  proof_of_length_return_wit_1 : length_return_wit_1
  proof_of_reverse_entail_wit_1 : reverse_entail_wit_1
  proof_of_reverse_entail_wit_3 : reverse_entail_wit_3
  proof_of_reverse_return_wit_1 : reverse_return_wit_1
  proof_of_reverse_alter_style1_entail_wit_1 : reverse_alter_style1_entail_wit_1
  proof_of_reverse_alter_style1_entail_wit_3 : reverse_alter_style1_entail_wit_3
  proof_of_reverse_alter_style1_return_wit_1 : reverse_alter_style1_return_wit_1
  proof_of_reverse_alter_style2_entail_wit_1 : reverse_alter_style2_entail_wit_1
  proof_of_reverse_alter_style2_entail_wit_3 : reverse_alter_style2_entail_wit_3
  proof_of_reverse_alter_style2_return_wit_1 : reverse_alter_style2_return_wit_1
  proof_of_reverse_alter_style3_entail_wit_2 : reverse_alter_style3_entail_wit_2
  proof_of_reverse_alter_style3_entail_wit_4 : reverse_alter_style3_entail_wit_4
  proof_of_reverse_alter_style3_return_wit_1 : reverse_alter_style3_return_wit_1
  proof_of_append_entail_wit_2 : append_entail_wit_2
  proof_of_append_entail_wit_4 : append_entail_wit_4
  proof_of_append_return_wit_1 : append_return_wit_1
  proof_of_append_return_wit_2 : append_return_wit_2
  proof_of_append_long_entail_wit_2 : append_long_entail_wit_2
  proof_of_append_long_entail_wit_4 : append_long_entail_wit_4
  proof_of_append_long_return_wit_1 : append_long_return_wit_1
  proof_of_append_long_return_wit_2 : append_long_return_wit_2
  proof_of_append_long_return_wit_3 : append_long_return_wit_3
  proof_of_append_2p_entail_wit_1 : append_2p_entail_wit_1
  proof_of_append_2p_entail_wit_2 : append_2p_entail_wit_2
  proof_of_append_2p_entail_wit_3 : append_2p_entail_wit_3
  proof_of_append_2p_return_wit_1 : append_2p_return_wit_1

end SimpleC.EE.QCP_demos_LLM.generated.sll_goal
