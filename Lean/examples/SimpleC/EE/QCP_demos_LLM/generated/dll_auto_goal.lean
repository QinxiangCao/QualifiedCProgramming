import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.dll_shape_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.dll_auto_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance dll_auto_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def dll_copy_safety_wit_1 : Prop :=
  forall (x_pre : Int) ,
  ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** (dlistrep_shape x_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dll_copy_safety_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** (dlistrep_shape x_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def dll_copy_entail_wit_1 : Prop :=
  forall (x_pre : Int) (x : Int) (y : Int) (retval_prev : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (retval_prev = (0 : Int))) (PreH4 : (x_pre ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> (retval_prev))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
|--
  EX t_prev : Int, EX p_prev : Int, EX v : Int, EX t_next : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ”
  &&  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev y)
  ** (dlistrep_shape y p_prev)
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape retval (0 : Int) t_prev retval)

noncomputable def dll_copy_entail_wit_2 : Prop :=
  forall (x_pre : Int) (y : Int) (t_prev_2 : Int) (p_prev_2 : Int) (p : Int) (v_2 : Int) (t_next_2 : Int) (t : Int) (x : Int) (y_2 : Int) (retval_prev : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (retval_prev = (0 : Int))) (PreH4 : (t ≠ (0 : Int))) (PreH5 : (t_next_2 = (0 : Int))) (PreH6 : (p ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_2 p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev_2))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** (dllseg_shape x_pre (0 : Int) p_prev_2 p)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev_2))
  ** (dllseg_shape y (0 : Int) t_prev_2 t)
|--
  EX t_prev : Int, EX p_prev : Int, EX v : Int, EX t_next : Int,
  “ (retval ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ”
  &&  ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev y_2)
  ** (dlistrep_shape y_2 p_prev)
  ** ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape y (0 : Int) t_prev retval)

noncomputable def dll_copy_return_wit_1 : Prop :=
  forall (x_pre : Int) (y : Int) (t_prev : Int) (p_prev : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev p)
  ** (dlistrep_shape p p_prev)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape y (0 : Int) t_prev t)
|--
  (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape x_pre (0 : Int))

noncomputable def dll_copy_return_wit_2 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (dlistrep_shape x_pre (0 : Int))
|--
  (dlistrep_shape (0 : Int) (0 : Int))
  ** (dlistrep_shape x_pre (0 : Int))

noncomputable def dll_copy_partial_solve_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (dlistrep_shape x_pre (0 : Int))
|--
  EX x : Int, EX y : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))

noncomputable def dll_copy_partial_solve_wit_2_pure : Prop :=
  forall (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
|--
  “ (x = x) ”

noncomputable def dll_copy_partial_solve_wit_2_aux : Prop :=
  forall (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
|--
  “ (x = x) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))

noncomputable def dll_copy_partial_solve_wit_2 : Prop := dll_copy_partial_solve_wit_2_pure -> dll_copy_partial_solve_wit_2_aux

noncomputable def dll_copy_partial_solve_wit_3 : Prop :=
  forall (x_pre : Int) (y : Int) (t_prev : Int) (p_prev : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev p)
  ** (dlistrep_shape p p_prev)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape y (0 : Int) t_prev t)
|--
  EX x : Int, EX y_2 : Int,
  “ (t ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ” &&
  “ (p ≠ (0 : Int)) ”
  &&  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_2 p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev p)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape y (0 : Int) t_prev t)

noncomputable def dll_copy_partial_solve_wit_4_pure : Prop :=
  forall (x_pre : Int) (y : Int) (t_prev : Int) (p_prev : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (x : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_2 p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "t" ) )) # Ptr |-> (t))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((( &( "p" ) )) # Ptr |-> (p))
  ** (dllseg_shape x_pre (0 : Int) p_prev p)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** ((( &( "y" ) )) # Ptr |-> (y))
  ** (dllseg_shape y (0 : Int) t_prev t)
|--
  “ (x = x) ”

noncomputable def dll_copy_partial_solve_wit_4_aux : Prop :=
  forall (x_pre : Int) (y : Int) (t_prev : Int) (p_prev : Int) (p : Int) (v : Int) (t_next : Int) (t : Int) (x : Int) (y_2 : Int) (PreH1 : (t ≠ (0 : Int))) (PreH2 : (t_next = (0 : Int))) (PreH3 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_2 p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev p)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape y (0 : Int) t_prev t)
|--
  “ (x = x) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (t_next = (0 : Int)) ” &&
  “ (p ≠ (0 : Int)) ”
  &&  ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_2 p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** (dllseg_shape x_pre (0 : Int) p_prev p)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape y (0 : Int) t_prev t)

noncomputable def dll_copy_partial_solve_wit_4 : Prop := dll_copy_partial_solve_wit_4_pure -> dll_copy_partial_solve_wit_4_aux

noncomputable def dll_free_entail_wit_1 : Prop :=
  forall (x_pre : Int) ,
  (dlistrep_shape x_pre (0 : Int))
|--
  EX prev : Int,
  (dlistrep_shape x_pre prev)

noncomputable def dll_free_entail_wit_2 : Prop :=
  forall (x : Int) (y : Int) (PreH1 : (x ≠ (0 : Int))) ,
  (dlistrep_shape y x)
  ** ((( &( "y" ) )) # Ptr |-> (y))
|--
  EX prev : Int,
  ((( &( "y" ) )) # Ptr |->_)
  ** (dlistrep_shape y prev)

noncomputable def dll_free_return_wit_1 : Prop :=
  forall (x : Int) (prev : Int) (PreH1 : (x = (0 : Int))) ,
  (dlistrep_shape x prev)
|--
  TT && emp 

noncomputable def dll_free_partial_solve_wit_1 : Prop :=
  forall (x : Int) (prev : Int) (PreH1 : (x ≠ (0 : Int))) ,
  (dlistrep_shape x prev)
|--
  EX y : Int, EX x_2 : Int,
  “ (x ≠ (0 : Int)) ”
  &&  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y x)
  ** ((&((x # "list")  ->ₛ "prev")) # Ptr |-> (prev))
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_2))

noncomputable def dll_free_partial_solve_wit_2 : Prop :=
  forall (x : Int) (prev : Int) (x_2 : Int) (y : Int) (PreH1 : (x ≠ (0 : Int))) ,
  ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y x)
  ** ((&((x # "list")  ->ₛ "prev")) # Ptr |-> (prev))
  ** ((&((x # "list")  ->ₛ "data")) # Int |-> (x_2))
|--
  “ (x ≠ (0 : Int)) ”
  &&  ((&((x # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((x # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((x # "list")  ->ₛ "prev")) # Ptr |-> (prev))
  ** (dlistrep_shape y x)

noncomputable def reverse_safety_wit_1 : Prop :=
  forall (p_pre : Int) ,
  ((( &( "v" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (dlistrep_shape p_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def reverse_entail_wit_1 : Prop :=
  forall (p_pre : Int) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (dlistrep_shape p_pre (0 : Int))
|--
  ((( &( "p" ) )) # Ptr |->_)
  ** (dlistrep_shape (0 : Int) p_pre)
  ** (dlistrep_shape p_pre (0 : Int))

noncomputable def reverse_entail_wit_2 : Prop :=
  forall (w : Int) (v : Int) (x : Int) (y : Int) (PreH1 : (v ≠ (0 : Int))) ,
  ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (dlistrep_shape y v)
  ** ((&((v # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((( &( "t" ) )) # Ptr |-> (y))
  ** (dlistrep_shape w v)
|--
  ((( &( "t" ) )) # Ptr |->_)
  ** (dlistrep_shape v y)
  ** (dlistrep_shape y v)

noncomputable def reverse_return_wit_1 : Prop :=
  forall (w : Int) (v : Int) (PreH1 : (v = (0 : Int))) ,
  (dlistrep_shape w v)
  ** (dlistrep_shape v w)
|--
  (dlistrep_shape w (0 : Int))

noncomputable def reverse_partial_solve_wit_1 : Prop :=
  forall (w : Int) (v : Int) (PreH1 : (v ≠ (0 : Int))) ,
  (dlistrep_shape w v)
  ** (dlistrep_shape v w)
|--
  EX y : Int, EX x : Int,
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y v)
  ** ((&((v # "list")  ->ₛ "prev")) # Ptr |-> (w))
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape w v)

noncomputable def append_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) ,
  ((( &( "u" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** (dlistrep_shape x_pre (0 : Int))
  ** (dlistrep_shape y_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def append_entail_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_pre (0 : Int))
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y = t_next) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev x_pre)

noncomputable def append_entail_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (t_prev_2 : Int) (t_next_2 : Int) (u : Int) (v_2 : Int) (t : Int) (x : Int) (y : Int) (PreH1 : (u = t_next_2)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) ,
  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next_2))
  ** (dlistrep_shape y_pre (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev_2))
  ** (dllseg_shape x_pre (0 : Int) t_prev_2 t)
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y = t_next) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape y u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev u)

noncomputable def append_return_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (v : Int) (t : Int) (x : Int) (y : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) (PreH4 : (y_pre ≠ (0 : Int))) ,
  ((&((y_pre # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y y_pre)
  ** ((&((y_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((y_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def append_return_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (v : Int) (t : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) (PreH4 : (y_pre = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def append_return_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (dlistrep_shape x_pre (0 : Int))
  ** (dlistrep_shape y_pre (0 : Int))
|--
  (dlistrep_shape y_pre (0 : Int))

noncomputable def append_partial_solve_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (dlistrep_shape x_pre (0 : Int))
  ** (dlistrep_shape y_pre (0 : Int))
|--
  EX y : Int, EX x : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_pre (0 : Int))

noncomputable def append_partial_solve_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (v : Int) (t : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y : Int, EX x : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y_pre (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def append_partial_solve_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (v : Int) (t : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) (PreH4 : (y_pre ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y : Int, EX x : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u = (0 : Int)) ” &&
  “ (y_pre ≠ (0 : Int)) ”
  &&  ((&((y_pre # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y y_pre)
  ** ((&((y_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((y_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_pre))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def iter_entail_wit_1 : Prop :=
  forall (l_pre : Int) ,
  (dlistrep_shape l_pre (0 : Int))
|--
  EX p_prev : Int,
  (dllseg_shape l_pre (0 : Int) p_prev l_pre)
  ** (dlistrep_shape l_pre p_prev)

noncomputable def iter_entail_wit_2 : Prop :=
  forall (l_pre : Int) (p_prev_2 : Int) (p : Int) (x : Int) (y : Int) (PreH1 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev_2))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dllseg_shape l_pre (0 : Int) p_prev_2 p)
|--
  EX p_prev : Int,
  (dllseg_shape l_pre (0 : Int) p_prev y)
  ** (dlistrep_shape y p_prev)

noncomputable def iter_return_wit_1 : Prop :=
  forall (l_pre : Int) (p_prev : Int) (p : Int) (PreH1 : (p = (0 : Int))) ,
  (dllseg_shape l_pre (0 : Int) p_prev p)
  ** (dlistrep_shape p p_prev)
|--
  (dlistrep_shape l_pre (0 : Int))

noncomputable def iter_partial_solve_wit_1 : Prop :=
  forall (l_pre : Int) (p_prev : Int) (p : Int) (PreH1 : (p ≠ (0 : Int))) ,
  (dllseg_shape l_pre (0 : Int) p_prev p)
  ** (dlistrep_shape p p_prev)
|--
  EX y : Int, EX x : Int,
  “ (p ≠ (0 : Int)) ”
  &&  ((&((p # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y p)
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dllseg_shape l_pre (0 : Int) p_prev p)

noncomputable def iter_back_safety_wit_1 : Prop :=
  forall (head_pre : Int) (l_pre : Int) (l_prev : Int) (PreH1 : (head_pre ≠ (0 : Int))) ,
  ((( &( "p" ) )) # Ptr |->_)
  ** ((( &( "l" ) )) # Ptr |-> (l_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** (dllseg_shape head_pre (0 : Int) l_prev l_pre)
  ** (dlistrep_shape l_pre l_prev)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def iter_back_entail_wit_1 : Prop :=
  forall (head_pre : Int) (l_pre : Int) (l_prev : Int) (PreH1 : (l_pre ≠ (0 : Int))) (PreH2 : (head_pre ≠ (0 : Int))) ,
  (dllseg_shape head_pre (0 : Int) l_prev l_pre)
  ** (dlistrep_shape l_pre l_prev)
|--
  EX p_next : Int, EX p_prev : Int, EX v : Int,
  “ (l_pre ≠ (0 : Int)) ”
  &&  ((&((l_pre # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((l_pre # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** (dllseg_shape head_pre (0 : Int) p_prev l_pre)
  ** ((&((l_pre # "list")  ->ₛ "next")) # Ptr |-> (p_next))
  ** (dlistrep_shape p_next l_pre)

noncomputable def iter_back_entail_wit_2 : Prop :=
  forall (head_pre : Int) (p_next_2 : Int) (p_prev_2 : Int) (v_2 : Int) (p : Int) (PreH1 : (p ≠ head_pre)) (PreH2 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev_2))
  ** (dllseg_shape head_pre (0 : Int) p_prev_2 p)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (p_next_2))
  ** (dlistrep_shape p_next_2 p)
|--
  EX p_next : Int, EX p_prev : Int, EX v : Int,
  “ (p_prev_2 ≠ (0 : Int)) ”
  &&  ((&((p_prev_2 # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((p_prev_2 # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** (dllseg_shape head_pre (0 : Int) p_prev p_prev_2)
  ** ((&((p_prev_2 # "list")  ->ₛ "next")) # Ptr |-> (p_next))
  ** (dlistrep_shape p_next p_prev_2)

noncomputable def iter_back_return_wit_1 : Prop :=
  forall (head_pre : Int) (p_next : Int) (p_prev : Int) (v : Int) (p : Int) (PreH1 : (p = head_pre)) (PreH2 : (p ≠ (0 : Int))) ,
  ((&((p # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** (dllseg_shape head_pre (0 : Int) p_prev p)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (p_next))
  ** (dlistrep_shape p_next p)
|--
  (dlistrep_shape p (0 : Int))

noncomputable def iter_back_return_wit_2 : Prop :=
  forall (head_pre : Int) (l_pre : Int) (l_prev : Int) (PreH1 : (l_pre = (0 : Int))) (PreH2 : (head_pre ≠ (0 : Int))) ,
  (dllseg_shape head_pre (0 : Int) l_prev l_pre)
  ** (dlistrep_shape l_pre l_prev)
|--
  (dlistrep_shape head_pre (0 : Int))

noncomputable def iter_back_2_entail_wit_1 : Prop :=
  forall (tail_pre : Int) (head_pre : Int) (tail_prev : Int) (tail_node : Int) (head_node : Int) (PreH1 : (head_node ≠ tail_node)) (PreH2 : (head_node ≠ (0 : Int))) (PreH3 : (tail_node ≠ (0 : Int))) ,
  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** (dllseg_shape head_node (0 : Int) tail_prev tail_node)
  ** (dlistrep_shape tail_node tail_prev)
|--
  EX p_next : Int, EX p_prev : Int, EX v : Int,
  “ (tail_node ≠ (0 : Int)) ”
  &&  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** ((&((tail_node # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail_node # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** (dllseg_shape head_node (0 : Int) p_prev tail_node)
  ** ((&((tail_node # "list")  ->ₛ "next")) # Ptr |-> (p_next))
  ** (dlistrep_shape p_next tail_node)

noncomputable def iter_back_2_entail_wit_2 : Prop :=
  forall (tail_pre : Int) (head_pre : Int) (tail_node : Int) (head_node : Int) (p_next_2 : Int) (p_prev_2 : Int) (v_2 : Int) (p : Int) (PreH1 : (p ≠ head_node)) (PreH2 : (p ≠ (0 : Int))) ,
  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev_2))
  ** (dllseg_shape head_node (0 : Int) p_prev_2 p)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (p_next_2))
  ** (dlistrep_shape p_next_2 p)
|--
  EX p_next : Int, EX p_prev : Int, EX v : Int,
  “ (p_prev_2 ≠ (0 : Int)) ”
  &&  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** ((&((p_prev_2 # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((p_prev_2 # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** (dllseg_shape head_node (0 : Int) p_prev p_prev_2)
  ** ((&((p_prev_2 # "list")  ->ₛ "next")) # Ptr |-> (p_next))
  ** (dlistrep_shape p_next p_prev_2)

noncomputable def iter_back_2_return_wit_1 : Prop :=
  forall (tail_pre : Int) (head_pre : Int) (tail_node : Int) (head_node : Int) (p_next : Int) (p_prev : Int) (v : Int) (p : Int) (PreH1 : (p = head_node)) (PreH2 : (p ≠ (0 : Int))) ,
  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** ((&((p # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((p # "list")  ->ₛ "prev")) # Ptr |-> (p_prev))
  ** (dllseg_shape head_node (0 : Int) p_prev p)
  ** ((&((p # "list")  ->ₛ "next")) # Ptr |-> (p_next))
  ** (dlistrep_shape p_next p)
|--
  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** (dlistrep_shape p (0 : Int))

noncomputable def iter_back_2_return_wit_2 : Prop :=
  forall (tail_pre : Int) (head_pre : Int) (tail_prev : Int) (tail_node : Int) (head_node : Int) (PreH1 : (head_node = tail_node)) (PreH2 : (head_node ≠ (0 : Int))) (PreH3 : (tail_node ≠ (0 : Int))) ,
  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** (dllseg_shape head_node (0 : Int) tail_prev tail_node)
  ** (dlistrep_shape tail_node tail_prev)
|--
  ((head_pre) # Ptr |-> (head_node))
  ** ((tail_pre) # Ptr |-> (tail_node))
  ** (dlistrep_shape tail_node (0 : Int))

noncomputable def multi_merge_safety_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) ,
  ((( &( "u" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "z" ) )) # Ptr |-> (z_pre))
  ** (dlistrep_shape x_pre (0 : Int))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_merge_safety_wit_2 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) ,
  ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "t" ) )) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((( &( "u" ) )) # Ptr |-> (u))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((( &( "y" ) )) # Ptr |-> (y_2))
  ** ((( &( "z" ) )) # Ptr |-> (z))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_merge_safety_wit_3 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (x_3 : Int) (y_4 : Int) (x_4 : Int) (y_5 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_5 ≠ (0 : Int))) ,
  ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_5 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "t" ) )) # Ptr |-> (z))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((( &( "u" ) )) # Ptr |-> (u))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((( &( "y" ) )) # Ptr |-> (y_2))
  ** ((( &( "z" ) )) # Ptr |-> (y_5))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_merge_safety_wit_4 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (x_3 : Int) (y_4 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 = (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_4 ≠ (0 : Int))) ,
  ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_4 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "t" ) )) # Ptr |-> (z))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((( &( "u" ) )) # Ptr |-> (u))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((( &( "y" ) )) # Ptr |-> (y_2))
  ** ((( &( "z" ) )) # Ptr |-> (y_4))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_merge_entail_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (x : Int) (y : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y = t_next) ” &&
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev x_pre)

noncomputable def multi_merge_entail_wit_2_1 : Prop :=
  forall (x_pre : Int) (t_prev_2 : Int) (z : Int) (y_4 : Int) (t_next_2 : Int) (u : Int) (t : Int) (v_2 : Int) (x : Int) (y : Int) (x_2 : Int) (y_2 : Int) (x_3 : Int) (y_5 : Int) (x_4 : Int) (y_3 : Int) (x_5 : Int) (y_6 : Int) (PreH1 : (u = t_next_2)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y_4 ≠ (0 : Int))) (PreH5 : (y ≠ (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_3 ≠ (0 : Int))) ,
  ((&((y_3 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_6 y_3)
  ** ((&((y_3 # "list")  ->ₛ "next")) # Ptr |-> (y_6))
  ** ((&((y_3 # "list")  ->ₛ "data")) # Int |-> (x_5))
  ** ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y_4))
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_5 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y_4 # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y_4 # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y_4 # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev_2))
  ** (dllseg_shape x_pre (0 : Int) t_prev_2 t)
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y_2 = t_next) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape y_3 (0 : Int))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev u)

noncomputable def multi_merge_entail_wit_2_2 : Prop :=
  forall (x_pre : Int) (t_prev_2 : Int) (z : Int) (y_4 : Int) (t_next_2 : Int) (u : Int) (t : Int) (v_2 : Int) (x : Int) (y : Int) (x_2 : Int) (y_2 : Int) (x_3 : Int) (y_3 : Int) (x_4 : Int) (y_5 : Int) (PreH1 : (u = t_next_2)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y_4 ≠ (0 : Int))) (PreH5 : (y = (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_3 ≠ (0 : Int))) ,
  ((&((y_3 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_5 y_3)
  ** ((&((y_3 # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((y_3 # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y_4))
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y_4 # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y_4 # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y_4 # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev_2))
  ** (dllseg_shape x_pre (0 : Int) t_prev_2 t)
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y_2 = t_next) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape y_3 (0 : Int))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev u)

noncomputable def multi_merge_entail_wit_2_3 : Prop :=
  forall (x_pre : Int) (t_prev_2 : Int) (z : Int) (y_4 : Int) (t_next_2 : Int) (u : Int) (t : Int) (v_2 : Int) (x : Int) (y : Int) (x_2 : Int) (y_2 : Int) (x_3 : Int) (y_5 : Int) (x_4 : Int) (y_3 : Int) (PreH1 : (u = t_next_2)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y_4 ≠ (0 : Int))) (PreH5 : (y ≠ (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_3 = (0 : Int))) ,
  ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y_4))
  ** (dlistrep_shape y_3 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_5 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y_4 # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y_4 # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y_4 # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev_2))
  ** (dllseg_shape x_pre (0 : Int) t_prev_2 t)
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y_2 = t_next) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape y_3 (0 : Int))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev u)

noncomputable def multi_merge_entail_wit_2_4 : Prop :=
  forall (x_pre : Int) (t_prev_2 : Int) (z : Int) (y_4 : Int) (t_next_2 : Int) (u : Int) (t : Int) (v_2 : Int) (x : Int) (y : Int) (x_2 : Int) (y_2 : Int) (x_3 : Int) (y_3 : Int) (PreH1 : (u = t_next_2)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y_4 ≠ (0 : Int))) (PreH5 : (y = (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_3 = (0 : Int))) ,
  ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y_4))
  ** (dlistrep_shape y_3 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (u))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y_4 # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y_4 # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y_4 # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev_2))
  ** (dllseg_shape x_pre (0 : Int) t_prev_2 t)
|--
  EX t_prev : Int, EX t_next : Int, EX v : Int,
  “ (y_2 = t_next) ” &&
  “ (u ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape y_3 (0 : Int))
  ** (dlistrep_shape y_2 u)
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev u)

noncomputable def multi_merge_return_wit_1 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (retval : Int) (x : Int) (y : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) (PreH4 : (retval ≠ (0 : Int))) ,
  ((&((retval # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y retval)
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def multi_merge_return_wit_2 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (retval : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) (PreH4 : (retval = (0 : Int))) ,
  (dlistrep_shape retval (0 : Int))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def multi_merge_return_wit_3 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (retval : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) (PreH6 : (z = (0 : Int))) ,
  (dlistrep_shape retval y)
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def multi_merge_return_wit_4 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (retval : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 = (0 : Int))) (PreH6 : (z = (0 : Int))) ,
  (dlistrep_shape retval y)
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def multi_merge_return_wit_5 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (retval : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y = (0 : Int))) ,
  (dlistrep_shape retval t)
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  (dlistrep_shape x_pre (0 : Int))

noncomputable def multi_merge_return_wit_6 : Prop :=
  forall (x_pre : Int) (retval : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (dlistrep_shape retval (0 : Int))
|--
  (dlistrep_shape retval (0 : Int))

noncomputable def multi_merge_partial_solve_wit_1 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre = (0 : Int))) ,
  (dlistrep_shape x_pre (0 : Int))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))
|--
  “ (x_pre = (0 : Int)) ”
  &&  (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))

noncomputable def multi_merge_partial_solve_wit_2 : Prop :=
  forall (z_pre : Int) (y_pre : Int) (x_pre : Int) (PreH1 : (x_pre ≠ (0 : Int))) ,
  (dlistrep_shape x_pre (0 : Int))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))
|--
  EX y : Int, EX x : Int,
  “ (x_pre ≠ (0 : Int)) ”
  &&  ((&((x_pre # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y x_pre)
  ** ((&((x_pre # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** ((&((x_pre # "list")  ->ₛ "data")) # Int |-> (x))
  ** (dlistrep_shape y_pre (0 : Int))
  ** (dlistrep_shape z_pre (0 : Int))

noncomputable def multi_merge_partial_solve_wit_3 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape z (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_2 : Int, EX x : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((y # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_4 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) ,
  ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_3 : Int, EX x_2 : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((u # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_5 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) ,
  ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_4 : Int, EX x_3 : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 ≠ (0 : Int)) ”
  &&  ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_6 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape z (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y = (0 : Int)) ”
  &&  (dlistrep_shape u t)
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_7 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (x_3 : Int) (y_4 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) (PreH6 : (z ≠ (0 : Int))) ,
  ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_5 : Int, EX x_4 : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 ≠ (0 : Int)) ” &&
  “ (z ≠ (0 : Int)) ”
  &&  ((&((z # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_5 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_8 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 = (0 : Int))) (PreH6 : (z ≠ (0 : Int))) ,
  ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_4 : Int, EX x_3 : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 = (0 : Int)) ” &&
  “ (z ≠ (0 : Int)) ”
  &&  ((&((z # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_4 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_9 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (x_3 : Int) (y_4 : Int) (x_4 : Int) (y_5 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_5 ≠ (0 : Int))) ,
  ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_5 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_6 : Int, EX x_5 : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 ≠ (0 : Int)) ” &&
  “ (z ≠ (0 : Int)) ” &&
  “ (y_5 ≠ (0 : Int)) ”
  &&  ((&((y_5 # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_6 y_5)
  ** ((&((y_5 # "list")  ->ₛ "next")) # Ptr |-> (y_6))
  ** ((&((y_5 # "list")  ->ₛ "data")) # Int |-> (x_5))
  ** ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_10 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (x_3 : Int) (y_4 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 = (0 : Int))) (PreH6 : (z ≠ (0 : Int))) (PreH7 : (y_4 ≠ (0 : Int))) ,
  ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_4 z)
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y_5 : Int, EX x_4 : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 = (0 : Int)) ” &&
  “ (z ≠ (0 : Int)) ” &&
  “ (y_4 ≠ (0 : Int)) ”
  &&  ((&((y_4 # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y_5 y_4)
  ** ((&((y_4 # "list")  ->ₛ "next")) # Ptr |-> (y_5))
  ** ((&((y_4 # "list")  ->ₛ "data")) # Int |-> (x_4))
  ** ((&((z # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** ((&((z # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((z # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (z))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (z))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_11 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (x_3 : Int) (y_4 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 ≠ (0 : Int))) (PreH6 : (z = (0 : Int))) ,
  ((&((y_2 # "list")  ->ₛ "prev")) # Ptr |-> ((0 : Int)))
  ** (dlistrep_shape y_4 y_2)
  ** ((&((y_2 # "list")  ->ₛ "next")) # Ptr |-> (y_4))
  ** ((&((y_2 # "list")  ->ₛ "data")) # Int |-> (x_3))
  ** ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 ≠ (0 : Int)) ” &&
  “ (z = (0 : Int)) ”
  &&  (dlistrep_shape u y)
  ** (dlistrep_shape y_2 (0 : Int))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_12 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (x : Int) (y_2 : Int) (x_2 : Int) (y_3 : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u ≠ (0 : Int))) (PreH4 : (y ≠ (0 : Int))) (PreH5 : (y_2 = (0 : Int))) (PreH6 : (z = (0 : Int))) ,
  ((&((u # "list")  ->ₛ "prev")) # Ptr |-> (y))
  ** (dlistrep_shape y_3 u)
  ** ((&((u # "list")  ->ₛ "next")) # Ptr |-> (y_3))
  ** ((&((u # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u ≠ (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ” &&
  “ (y_2 = (0 : Int)) ” &&
  “ (z = (0 : Int)) ”
  &&  (dlistrep_shape u y)
  ** (dlistrep_shape y_2 (0 : Int))
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (t))
  ** ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_13 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (z : Int) (y : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) ,
  ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape z (0 : Int))
  ** (dlistrep_shape u t)
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u = (0 : Int)) ”
  &&  (dlistrep_shape y (0 : Int))
  ** (dlistrep_shape z (0 : Int))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (t_next))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_merge_partial_solve_wit_14 : Prop :=
  forall (x_pre : Int) (t_prev : Int) (t_next : Int) (u : Int) (t : Int) (v : Int) (retval : Int) (PreH1 : (u = t_next)) (PreH2 : (t ≠ (0 : Int))) (PreH3 : (u = (0 : Int))) (PreH4 : (retval ≠ (0 : Int))) ,
  (dlistrep_shape retval (0 : Int))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)
|--
  EX y : Int, EX x : Int,
  “ (u = t_next) ” &&
  “ (t ≠ (0 : Int)) ” &&
  “ (u = (0 : Int)) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  ((&((retval # "list")  ->ₛ "prev")) # Ptr |->_)
  ** (dlistrep_shape y retval)
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (y))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((t # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((t # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** ((&((t # "list")  ->ₛ "prev")) # Ptr |-> (t_prev))
  ** (dllseg_shape x_pre (0 : Int) t_prev t)

noncomputable def multi_rev_safety_wit_1 : Prop :=
  forall (q_pre : Int) (p_pre : Int) ,
  ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |->_)
  ** ((( &( "v" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "w" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (dlistrep_shape p_pre (0 : Int))
  ** (dlistrep_shape q_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_rev_safety_wit_2 : Prop :=
  forall (q_pre : Int) (p_pre : Int) ,
  ((( &( "y" ) )) # Ptr |->_)
  ** ((( &( "x" ) )) # Ptr |->_)
  ** ((( &( "v" ) )) # Ptr |->_)
  ** ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "w" ) )) # Ptr |-> ((0 : Int)))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** (dlistrep_shape p_pre (0 : Int))
  ** (dlistrep_shape q_pre (0 : Int))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def multi_rev_safety_wit_3 : Prop :=
  forall (q_pre : Int) (p_pre : Int) (x : Int) (y : Int) (w : Int) (v : Int) ,
  ((( &( "t" ) )) # Ptr |->_)
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "q" ) )) # Ptr |-> (q_pre))
  ** ((( &( "v" ) )) # Ptr |-> (v))
  ** ((( &( "w" ) )) # Ptr |-> (w))
  ** (dlistrep_shape w v)
  ** (dlistrep_shape v w)
  ** ((( &( "y" ) )) # Ptr |-> (y))
  ** ((( &( "x" ) )) # Ptr |-> (x))
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def multi_rev_entail_wit_1 : Prop :=
  forall (q_pre : Int) (p_pre : Int) ,
  (dlistrep_shape p_pre (0 : Int))
  ** (dlistrep_shape q_pre (0 : Int))
|--
  (dlistrep_shape (0 : Int) p_pre)
  ** (dlistrep_shape p_pre (0 : Int))
  ** (dlistrep_shape (0 : Int) q_pre)
  ** (dlistrep_shape q_pre (0 : Int))

noncomputable def multi_rev_entail_wit_2_1 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (v : Int) (x_2 : Int) (y_2 : Int) (PreH1 : (v ≠ (0 : Int))) ,
  ((&((v # "list")  ->ₛ "next")) # Ptr |-> (w))
  ** (dlistrep_shape y_2 v)
  ** ((&((v # "list")  ->ₛ "prev")) # Ptr |-> (y_2))
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((( &( "t" ) )) # Ptr |-> (y_2))
  ** (dlistrep_shape w v)
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)
|--
  ((( &( "t" ) )) # Ptr |->_)
  ** (dlistrep_shape v y_2)
  ** (dlistrep_shape y_2 v)
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)

noncomputable def multi_rev_entail_wit_2_2 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (v : Int) (x_2 : Int) (y_2 : Int) (PreH1 : (v = (0 : Int))) (PreH2 : (y ≠ (0 : Int))) ,
  ((&((y # "list")  ->ₛ "next")) # Ptr |-> (x))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (y_2))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** ((( &( "t" ) )) # Ptr |-> (y_2))
  ** (dlistrep_shape w v)
  ** (dlistrep_shape x y)
|--
  ((( &( "t" ) )) # Ptr |->_)
  ** (dlistrep_shape w v)
  ** (dlistrep_shape v w)
  ** (dlistrep_shape y y_2)
  ** (dlistrep_shape y_2 y)

noncomputable def multi_rev_return_wit_1 : Prop :=
  forall (y : Int) (v : Int) (retval : Int) (PreH1 : (v = (0 : Int))) (PreH2 : (y = (0 : Int))) ,
  (dlistrep_shape retval (0 : Int))
|--
  (dlistrep_shape retval (0 : Int))

noncomputable def multi_rev_partial_solve_wit_1 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (v : Int) (PreH1 : (v ≠ (0 : Int))) ,
  (dlistrep_shape w v)
  ** (dlistrep_shape v w)
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)
|--
  EX y_2 : Int, EX x_2 : Int,
  “ (v ≠ (0 : Int)) ”
  &&  ((&((v # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (dlistrep_shape y_2 v)
  ** ((&((v # "list")  ->ₛ "prev")) # Ptr |-> (w))
  ** ((&((v # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (dlistrep_shape w v)
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)

noncomputable def multi_rev_partial_solve_wit_2 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (v : Int) (PreH1 : (v = (0 : Int))) (PreH2 : (y ≠ (0 : Int))) ,
  (dlistrep_shape w v)
  ** (dlistrep_shape v w)
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)
|--
  EX y_2 : Int, EX x_2 : Int,
  “ (v = (0 : Int)) ” &&
  “ (y ≠ (0 : Int)) ”
  &&  ((&((y # "list")  ->ₛ "next")) # Ptr |-> (y_2))
  ** (dlistrep_shape y_2 y)
  ** ((&((y # "list")  ->ₛ "prev")) # Ptr |-> (x))
  ** ((&((y # "list")  ->ₛ "data")) # Int |-> (x_2))
  ** (dlistrep_shape w v)
  ** (dlistrep_shape x y)

noncomputable def multi_rev_partial_solve_wit_3 : Prop :=
  forall (x : Int) (y : Int) (w : Int) (v : Int) (PreH1 : (v = (0 : Int))) (PreH2 : (y = (0 : Int))) ,
  (dlistrep_shape w v)
  ** (dlistrep_shape v w)
  ** (dlistrep_shape x y)
  ** (dlistrep_shape y x)
|--
  “ (v = (0 : Int)) ” &&
  “ (y = (0 : Int)) ”
  &&  (dlistrep_shape w (0 : Int))
  ** (dlistrep_shape x (0 : Int))


structure VC_Correct : Type where
  proof_of_dll_copy_safety_wit_1 : dll_copy_safety_wit_1
  proof_of_dll_copy_safety_wit_2 : dll_copy_safety_wit_2
  proof_of_dll_copy_entail_wit_1 : dll_copy_entail_wit_1
  proof_of_dll_copy_entail_wit_2 : dll_copy_entail_wit_2
  proof_of_dll_copy_return_wit_1 : dll_copy_return_wit_1
  proof_of_dll_copy_return_wit_2 : dll_copy_return_wit_2
  proof_of_dll_copy_partial_solve_wit_1 : dll_copy_partial_solve_wit_1
  proof_of_dll_copy_partial_solve_wit_2_pure : dll_copy_partial_solve_wit_2_pure
  proof_of_dll_copy_partial_solve_wit_2 : dll_copy_partial_solve_wit_2
  proof_of_dll_copy_partial_solve_wit_3 : dll_copy_partial_solve_wit_3
  proof_of_dll_copy_partial_solve_wit_4_pure : dll_copy_partial_solve_wit_4_pure
  proof_of_dll_copy_partial_solve_wit_4 : dll_copy_partial_solve_wit_4
  proof_of_dll_free_entail_wit_1 : dll_free_entail_wit_1
  proof_of_dll_free_entail_wit_2 : dll_free_entail_wit_2
  proof_of_dll_free_return_wit_1 : dll_free_return_wit_1
  proof_of_dll_free_partial_solve_wit_1 : dll_free_partial_solve_wit_1
  proof_of_dll_free_partial_solve_wit_2 : dll_free_partial_solve_wit_2
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
  proof_of_append_return_wit_3 : append_return_wit_3
  proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1
  proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2
  proof_of_append_partial_solve_wit_3 : append_partial_solve_wit_3
  proof_of_iter_entail_wit_1 : iter_entail_wit_1
  proof_of_iter_entail_wit_2 : iter_entail_wit_2
  proof_of_iter_return_wit_1 : iter_return_wit_1
  proof_of_iter_partial_solve_wit_1 : iter_partial_solve_wit_1
  proof_of_iter_back_safety_wit_1 : iter_back_safety_wit_1
  proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1
  proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2
  proof_of_iter_back_return_wit_1 : iter_back_return_wit_1
  proof_of_iter_back_return_wit_2 : iter_back_return_wit_2
  proof_of_iter_back_2_entail_wit_1 : iter_back_2_entail_wit_1
  proof_of_iter_back_2_entail_wit_2 : iter_back_2_entail_wit_2
  proof_of_iter_back_2_return_wit_1 : iter_back_2_return_wit_1
  proof_of_iter_back_2_return_wit_2 : iter_back_2_return_wit_2
  proof_of_multi_merge_safety_wit_1 : multi_merge_safety_wit_1
  proof_of_multi_merge_safety_wit_2 : multi_merge_safety_wit_2
  proof_of_multi_merge_safety_wit_3 : multi_merge_safety_wit_3
  proof_of_multi_merge_safety_wit_4 : multi_merge_safety_wit_4
  proof_of_multi_merge_entail_wit_1 : multi_merge_entail_wit_1
  proof_of_multi_merge_entail_wit_2_1 : multi_merge_entail_wit_2_1
  proof_of_multi_merge_entail_wit_2_2 : multi_merge_entail_wit_2_2
  proof_of_multi_merge_entail_wit_2_3 : multi_merge_entail_wit_2_3
  proof_of_multi_merge_entail_wit_2_4 : multi_merge_entail_wit_2_4
  proof_of_multi_merge_return_wit_1 : multi_merge_return_wit_1
  proof_of_multi_merge_return_wit_2 : multi_merge_return_wit_2
  proof_of_multi_merge_return_wit_3 : multi_merge_return_wit_3
  proof_of_multi_merge_return_wit_4 : multi_merge_return_wit_4
  proof_of_multi_merge_return_wit_5 : multi_merge_return_wit_5
  proof_of_multi_merge_return_wit_6 : multi_merge_return_wit_6
  proof_of_multi_merge_partial_solve_wit_1 : multi_merge_partial_solve_wit_1
  proof_of_multi_merge_partial_solve_wit_2 : multi_merge_partial_solve_wit_2
  proof_of_multi_merge_partial_solve_wit_3 : multi_merge_partial_solve_wit_3
  proof_of_multi_merge_partial_solve_wit_4 : multi_merge_partial_solve_wit_4
  proof_of_multi_merge_partial_solve_wit_5 : multi_merge_partial_solve_wit_5
  proof_of_multi_merge_partial_solve_wit_6 : multi_merge_partial_solve_wit_6
  proof_of_multi_merge_partial_solve_wit_7 : multi_merge_partial_solve_wit_7
  proof_of_multi_merge_partial_solve_wit_8 : multi_merge_partial_solve_wit_8
  proof_of_multi_merge_partial_solve_wit_9 : multi_merge_partial_solve_wit_9
  proof_of_multi_merge_partial_solve_wit_10 : multi_merge_partial_solve_wit_10
  proof_of_multi_merge_partial_solve_wit_11 : multi_merge_partial_solve_wit_11
  proof_of_multi_merge_partial_solve_wit_12 : multi_merge_partial_solve_wit_12
  proof_of_multi_merge_partial_solve_wit_13 : multi_merge_partial_solve_wit_13
  proof_of_multi_merge_partial_solve_wit_14 : multi_merge_partial_solve_wit_14
  proof_of_multi_rev_safety_wit_1 : multi_rev_safety_wit_1
  proof_of_multi_rev_safety_wit_2 : multi_rev_safety_wit_2
  proof_of_multi_rev_safety_wit_3 : multi_rev_safety_wit_3
  proof_of_multi_rev_entail_wit_1 : multi_rev_entail_wit_1
  proof_of_multi_rev_entail_wit_2_1 : multi_rev_entail_wit_2_1
  proof_of_multi_rev_entail_wit_2_2 : multi_rev_entail_wit_2_2
  proof_of_multi_rev_return_wit_1 : multi_rev_return_wit_1
  proof_of_multi_rev_partial_solve_wit_1 : multi_rev_partial_solve_wit_1
  proof_of_multi_rev_partial_solve_wit_2 : multi_rev_partial_solve_wit_2
  proof_of_multi_rev_partial_solve_wit_3 : multi_rev_partial_solve_wit_3

end SimpleC.EE.QCP_demos_LLM.generated.dll_auto_goal
