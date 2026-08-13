import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_shape_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_auto_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sll_auto_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def sll_copy_safety_wit_1 : Prop :=
  forall (x_pre : Int) ,
  ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** (listrep x_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sll_copy_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** (listrep x_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sll_copy_entail_wit_1 : Prop :=
  forall (x_pre : Int) (x : Int) (y : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (x_pre ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
|--
  EX v : Int, EX t_next : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ”
  &&  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre y)
  ** (listrep y)
  ** (lseg retval retval)

noncomputable def sll_copy_entail_wit_2 : Prop :=
  forall (x_pre : Int) (y : Int) (p : Int) (v_2 : Int) (t_next_2 : Int) (t : Int) (x : Int) (y_2 : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (t ≠ (0 : Int))) (PreH4 : (t_next_2 = (0 : Int))) (PreH5 : (p ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_2)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** (lseg x_pre p)
  ** (lseg y t)
|--
  EX v : Int, EX t_next : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ”
  &&  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre y_2)
  ** (listrep y_2)
  ** (lseg y retval)

noncomputable def sll_copy_return_wit_1 : Prop :=
  forall (x_pre : Int) (y : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre p)
  ** (listrep p)
  ** (lseg y t)
|--
  (listrep y)
  ** (listrep x_pre)

noncomputable def sll_copy_return_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (listrep x_pre)
|--
  (listrep (0 : Int))
  ** (listrep x_pre)

noncomputable def sll_copy_partial_solve_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (listrep x_pre)
|--
  EX x : Int, EX y : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))

noncomputable def sll_copy_partial_solve_wit_2_pure : Prop :=
  forall (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
|--
  “ (x = x) ”

noncomputable def sll_copy_partial_solve_wit_2_aux : Prop :=
  forall (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
|--
  “ (x = x) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))

noncomputable def sll_copy_partial_solve_wit_2 : Prop := sll_copy_partial_solve_wit_2_pure -> sll_copy_partial_solve_wit_2_aux

noncomputable def sll_copy_partial_solve_wit_3 : Prop :=
  forall (x_pre : Int) (y : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre p)
  ** (listrep p)
  ** (lseg y t)
|--
  EX x : Int, EX y_2 : Int,
  “ (t ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ” &&
  “ (p ≠ (0 : Int)) ”
  &&  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_2)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre p)
  ** (lseg y t)

noncomputable def sll_copy_partial_solve_wit_4_pure : Prop :=
  forall (x_pre : Int) (y : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (x : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_2)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** (lseg x_pre p)
  ** ((( &( "y" ) )) # Ptr |-> (y))
  ** (lseg y t)
|--
  “ (x = x) ”

noncomputable def sll_copy_partial_solve_wit_4_aux : Prop :=
  forall (x_pre : Int) (y : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (x : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_2)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre p)
  ** (lseg y t)
|--
  “ (x = x) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ” &&
  “ (p ≠ (0 : Int)) ”
  &&  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_2)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (lseg x_pre p)
  ** (lseg y t)

noncomputable def sll_copy_partial_solve_wit_4 : Prop := sll_copy_partial_solve_wit_4_pure -> sll_copy_partial_solve_wit_4_aux

noncomputable def sll_free_entail_wit_1 : Prop :=
  forall (x_pre : Int) ,
  (listrep x_pre)
|--
  (listrep x_pre)

noncomputable def sll_free_entail_wit_2 : Prop :=
  forall (x : Int) (y : Int) (PreH1 : (x ≠ (0 : Int))) ,
  (listrep y)
  ** ((( &( "y" ) )) # Ptr |-> (y))
|--
  ((( &( "y" ) )) # Ptr |->_)
  ** (listrep y)

noncomputable def sll_free_return_wit_1 : Prop :=
  forall (x : Int) (PreH1 : (x = (0 : Int))) ,
  (listrep x)
|--
  TT && emp 

noncomputable def sll_free_partial_solve_wit_1 : Prop :=
  forall (x : Int) (PreH1 : (x ≠ (0 : Int))) ,
  (listrep x)
|--
  EX y : Int, EX x_2 : Int,
  “ (x ≠ (0 : Int)) ”
  &&  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_2))

noncomputable def sll_free_partial_solve_wit_2 : Prop :=
  forall (x : Int) (x_2 : Int) (y : Int) (PreH1 : (x ≠ (0 : Int))) ,
  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_2))
|--
  “ (x ≠ (0 : Int)) ”
  &&  ((&((x # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)

noncomputable def reverse_safety_wit_1 : Prop :=
  forall (p_pre : Int) ,
  ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (listrep p_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_entail_wit_1 : Prop :=
  forall (p_pre : Int) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (listrep p_pre)
|--
  ((( &( "p" ) )) # Ptr |->_)
  ** (listrep (0 : Int))
  ** (listrep p_pre)

noncomputable def reverse_entail_wit_2 : Prop :=
  forall (v : Int) (w : Int) (x : Int) (y : Int) (PreH1 : (v ≠ (0 : Int))) ,
  ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (listrep y)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep w)
|--
  (listrep v)
  ** (listrep y)

noncomputable def reverse_return_wit_1 : Prop :=
  forall (v : Int) (w : Int) (PreH1 : (v = (0 : Int))) ,
  (listrep w)
  ** (listrep v)
|--
  (listrep w)

noncomputable def reverse_partial_solve_wit_1 : Prop :=
  forall (v : Int) (w : Int) (PreH1 : (v ≠ (0 : Int))) ,
  (listrep w)
  ** (listrep v)
|--
  EX y : Int, EX x : Int,
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep w)

noncomputable def append_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) ,
  ((( &( "u" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** (listrep x_pre)
  ** (listrep y_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_pre)
|--
  EX w : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (w))
  ** (listrep y_pre)
  ** (listrep y)
  ** (lseg x_pre x_pre)

noncomputable def append_entail_wit_2 : Prop :=
  forall (x : Int) (y : Int) (w_2 : Int) (u : Int) (t : Int) (x_2 : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) ,
  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (w_2))
  ** (listrep y)
  ** (lseg x t)
|--
  EX w : Int,
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (w))
  ** (listrep y)
  ** (listrep y_2)
  ** (lseg x u)

noncomputable def append_return_wit_1 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (u : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (w))
  ** (listrep y)
  ** (listrep u)
  ** (lseg x t)
|--
  (listrep x)

noncomputable def append_return_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (listrep x_pre)
  ** (listrep y_pre)
|--
  (listrep y_pre)

noncomputable def append_partial_solve_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (listrep x_pre)
  ** (listrep y_pre)
|--
  EX y : Int, EX x : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_pre)

noncomputable def append_partial_solve_wit_2 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (u : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (w))
  ** (listrep y)
  ** (listrep u)
  ** (lseg x t)
|--
  EX y_2 : Int, EX x_2 : Int,
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (w))
  ** (listrep y)
  ** (lseg x t)

noncomputable def merge_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) ,
  ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "z" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** (listrep x_pre)
  ** (listrep y_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def merge_safety_wit_2 : Prop :=
  forall (z : Int) (x : Int) (t : Int) (y : Int) (x_2 : Int) (y_2 : Int) (x_3 : Int) (y_3 : Int) (PreH1 : (y = t)) (PreH2 : (x ≠ (0 : Int))) (PreH3 : (y ≠ (0 : Int))) ,
  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y_3)
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((( &( "y" ) )) # Ptr |-> (y))
  ** ((( &( "t" ) )) # Ptr |-> (y_2))
  ** ((( &( "x" ) )) # Ptr |-> (x))
  ** ((( &( "z" ) )) # Ptr |-> (z))
  ** (lseg z x)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def merge_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (listrep x_pre)
  ** (listrep y_pre)
|--
  “ (y_pre = y_pre) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  (lseg x_pre x_pre)
  ** (listrep x_pre)
  ** (listrep y_pre)

noncomputable def merge_entail_wit_2 : Prop :=
  forall (z : Int) (x : Int) (t : Int) (y_3 : Int) (x_2 : Int) (y : Int) (x_3 : Int) (y_2 : Int) (PreH1 : (y_2 ≠ (0 : Int))) (PreH2 : (y_3 = t)) (PreH3 : (x ≠ (0 : Int))) (PreH4 : (y_3 ≠ (0 : Int))) ,
  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** (listrep y_2)
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((y_3 # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y)
  ** ((&((y_3 # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (lseg z x)
|--
  “ (y = y) ” &&
  “ (y_2 ≠ (0 : Int)) ”
  &&  (lseg z y_2)
  ** (listrep y_2)
  ** (listrep y)

noncomputable def merge_return_wit_1 : Prop :=
  forall (z : Int) (x : Int) (t : Int) (y : Int) (PreH1 : (y = t)) (PreH2 : (x ≠ (0 : Int))) (PreH3 : (y = (0 : Int))) ,
  (lseg z x)
  ** (listrep x)
  ** (listrep y)
|--
  (listrep z)

noncomputable def merge_return_wit_2 : Prop :=
  forall (z : Int) (x : Int) (t : Int) (y : Int) (x_2 : Int) (y_2 : Int) (x_3 : Int) (y_3 : Int) (PreH1 : (y_3 = (0 : Int))) (PreH2 : (y = t)) (PreH3 : (x ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) ,
  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y_3)
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (lseg z x)
|--
  (listrep z)

noncomputable def merge_return_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (listrep x_pre)
  ** (listrep y_pre)
|--
  (listrep y_pre)

noncomputable def merge_partial_solve_wit_1 : Prop :=
  forall (z : Int) (x : Int) (t : Int) (y : Int) (PreH1 : (y = t)) (PreH2 : (x ≠ (0 : Int))) (PreH3 : (y ≠ (0 : Int))) ,
  (lseg z x)
  ** (listrep x)
  ** (listrep y)
|--
  EX y_2 : Int, EX x_2 : Int,
  “ (y = t) ” &&
  “ (x ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (lseg z x)
  ** (listrep x)

noncomputable def merge_partial_solve_wit_2 : Prop :=
  forall (z : Int) (x : Int) (t : Int) (y : Int) (x_2 : Int) (y_2 : Int) (PreH1 : (y = t)) (PreH2 : (x ≠ (0 : Int))) (PreH3 : (y ≠ (0 : Int))) ,
  ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (lseg z x)
  ** (listrep x)
|--
  EX y_3 : Int, EX x_3 : Int,
  “ (y = t) ” &&
  “ (x ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** (listrep y_3)
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (lseg z x)

noncomputable def multi_append_safety_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) ,
  ((( &( "u" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "z" ) )) # Ptr |-> (z_pre))
  ** (listrep x_pre)
  ** (listrep y_pre)
  ** (listrep z_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_append_entail_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_pre)
  ** (listrep z_pre)
|--
  EX v : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y_pre)
  ** (listrep z_pre)
  ** (listrep y)
  ** (lseg x_pre x_pre)

noncomputable def multi_append_entail_wit_2 : Prop :=
  forall (x : Int) (z : Int) (y_3 : Int) (u : Int) (v_2 : Int) (t : Int) (x_2 : Int) (y : Int) (x_3 : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) (PreH3 : (y_3 ≠ (0 : Int))) ,
  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((y_3 # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (listrep y)
  ** ((&((y_3 # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** (listrep z)
  ** (lseg x t)
|--
  EX v : Int,
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y)
  ** (listrep z)
  ** (listrep y_2)
  ** (lseg x u)

noncomputable def multi_append_return_wit_1 : Prop :=
  forall (x : Int) (u : Int) (v : Int) (t : Int) (retval : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u = (0 : Int))) ,
  (listrep retval)
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (lseg x t)
|--
  (listrep x)

noncomputable def multi_append_return_wit_2 : Prop :=
  forall (x : Int) (y : Int) (u : Int) (v : Int) (t : Int) (retval : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) (PreH3 : (y = (0 : Int))) ,
  (listrep retval)
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (lseg x t)
|--
  (listrep x)

noncomputable def multi_append_return_wit_3 : Prop :=
  forall (x_pre : Int) (retval : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (listrep retval)
|--
  (listrep retval)

noncomputable def multi_append_partial_solve_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (listrep x_pre)
  ** (listrep y_pre)
  ** (listrep z_pre)
|--
  “ (x_pre = (0 : Int)) ”
  &&  (listrep y_pre)
  ** (listrep z_pre)

noncomputable def multi_append_partial_solve_wit_2 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (listrep x_pre)
  ** (listrep y_pre)
  ** (listrep z_pre)
|--
  EX y : Int, EX x : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (listrep y_pre)
  ** (listrep z_pre)

noncomputable def multi_append_partial_solve_wit_3 : Prop :=
  forall (x : Int) (z : Int) (y : Int) (u : Int) (v : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) (PreH3 : (y ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep y)
  ** (listrep z)
  ** (listrep u)
  ** (lseg x t)
|--
  EX y_2 : Int, EX x_2 : Int,
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep z)
  ** (listrep u)
  ** (lseg x t)

noncomputable def multi_append_partial_solve_wit_4 : Prop :=
  forall (x : Int) (z : Int) (y : Int) (u : Int) (v : Int) (t : Int) (x_2 : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) (PreH3 : (y ≠ (0 : Int))) ,
  ((&((y # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep z)
  ** (listrep u)
  ** (lseg x t)
|--
  EX y_3 : Int, EX x_3 : Int,
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** (listrep y_3)
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (listrep y_2)
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (listrep z)
  ** (lseg x t)

noncomputable def multi_append_partial_solve_wit_5 : Prop :=
  forall (x : Int) (z : Int) (y : Int) (u : Int) (v : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u ≠ (0 : Int))) (PreH3 : (y = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (listrep y)
  ** (listrep z)
  ** (listrep u)
  ** (lseg x t)
|--
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y = (0 : Int)) ”
  &&  (listrep u)
  ** (listrep z)
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (lseg x t)

noncomputable def multi_append_partial_solve_wit_6 : Prop :=
  forall (x : Int) (z : Int) (y : Int) (u : Int) (v : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (u = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (listrep y)
  ** (listrep z)
  ** (listrep u)
  ** (lseg x t)
|--
  “ (t ≠ (0 : Int)) ” &&
  “ (u = (0 : Int)) ”
  &&  (listrep y)
  ** (listrep z)
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** (lseg x t)


structure VC_Correct : Type where
  proof_of_sll_copy_safety_wit_1 : sll_copy_safety_wit_1
  proof_of_sll_copy_safety_wit_2 : sll_copy_safety_wit_2
  proof_of_sll_copy_entail_wit_1 : sll_copy_entail_wit_1
  proof_of_sll_copy_entail_wit_2 : sll_copy_entail_wit_2
  proof_of_sll_copy_return_wit_1 : sll_copy_return_wit_1
  proof_of_sll_copy_return_wit_2 : sll_copy_return_wit_2
  proof_of_sll_copy_partial_solve_wit_1 : sll_copy_partial_solve_wit_1
  proof_of_sll_copy_partial_solve_wit_2_pure : sll_copy_partial_solve_wit_2_pure
  proof_of_sll_copy_partial_solve_wit_2 : sll_copy_partial_solve_wit_2
  proof_of_sll_copy_partial_solve_wit_3 : sll_copy_partial_solve_wit_3
  proof_of_sll_copy_partial_solve_wit_4_pure : sll_copy_partial_solve_wit_4_pure
  proof_of_sll_copy_partial_solve_wit_4 : sll_copy_partial_solve_wit_4
  proof_of_sll_free_entail_wit_1 : sll_free_entail_wit_1
  proof_of_sll_free_entail_wit_2 : sll_free_entail_wit_2
  proof_of_sll_free_return_wit_1 : sll_free_return_wit_1
  proof_of_sll_free_partial_solve_wit_1 : sll_free_partial_solve_wit_1
  proof_of_sll_free_partial_solve_wit_2 : sll_free_partial_solve_wit_2
  proof_of_reverse_safety_wit_1 : reverse_safety_wit_1
  proof_of_reverse_entail_wit_1 : reverse_entail_wit_1
  proof_of_reverse_entail_wit_2 : reverse_entail_wit_2
  proof_of_reverse_return_wit_1 : reverse_return_wit_1
  proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1
  proof_of_append_safety_wit_1 : append_safety_wit_1
  proof_of_append_entail_wit_1 : append_entail_wit_1
  proof_of_append_entail_wit_2 : append_entail_wit_2
  proof_of_append_return_wit_1 : append_return_wit_1
  proof_of_append_return_wit_2 : append_return_wit_2
  proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1
  proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2
  proof_of_merge_safety_wit_1 : merge_safety_wit_1
  proof_of_merge_safety_wit_2 : merge_safety_wit_2
  proof_of_merge_entail_wit_1 : merge_entail_wit_1
  proof_of_merge_entail_wit_2 : merge_entail_wit_2
  proof_of_merge_return_wit_1 : merge_return_wit_1
  proof_of_merge_return_wit_2 : merge_return_wit_2
  proof_of_merge_return_wit_3 : merge_return_wit_3
  proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1
  proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2
  proof_of_multi_append_safety_wit_1 : multi_append_safety_wit_1
  proof_of_multi_append_entail_wit_1 : multi_append_entail_wit_1
  proof_of_multi_append_entail_wit_2 : multi_append_entail_wit_2
  proof_of_multi_append_return_wit_1 : multi_append_return_wit_1
  proof_of_multi_append_return_wit_2 : multi_append_return_wit_2
  proof_of_multi_append_return_wit_3 : multi_append_return_wit_3
  proof_of_multi_append_partial_solve_wit_1 : multi_append_partial_solve_wit_1
  proof_of_multi_append_partial_solve_wit_2 : multi_append_partial_solve_wit_2
  proof_of_multi_append_partial_solve_wit_3 : multi_append_partial_solve_wit_3
  proof_of_multi_append_partial_solve_wit_4 : multi_append_partial_solve_wit_4
  proof_of_multi_append_partial_solve_wit_5 : multi_append_partial_solve_wit_5
  proof_of_multi_append_partial_solve_wit_6 : multi_append_partial_solve_wit_6

end SimpleC.EE.QCP_demos_LLM.generated.sll_auto_goal
