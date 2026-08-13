import SimpleC.SL.SeparationLogic

import SimpleC.EE.QCP_demos_LLM.sll_shape_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.QCP_demos_LLM.generated.array_auto_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance array_auto_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def arr_sum_safety_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "ret" ) )) # UInt |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (uintArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_safety_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "ret" ) )) # UInt |-> ((0 : Int)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** (uintArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def arr_sum_safety_wit_3 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (i : Int) (v : Int) (x : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (uintArray.full_shape a_pre n_pre)
  ** ((( &( "ret" ) )) # UInt |-> ((unsigned_last_nbits ((v + x)) (32))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def arr_sum_entail_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  (uintArray.full_shape a_pre n_pre)

noncomputable def arr_sum_entail_wit_2 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (uintArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ”
  &&  (uintArray.full_shape a_pre n_pre)

noncomputable def arr_sum_return_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (uintArray.full_shape a_pre n_pre)
|--
  (uintArray.full_shape a_pre n_pre)

noncomputable def arr_sum_partial_solve_wit_1 : Prop :=
  forall (a_pre : Int) (n_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) ,
  (uintArray.full_shape a_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt |-> (x))
  ** (uintArray.missing_i_shape a_pre i (0 : Int) n_pre)

noncomputable def array_copy1_safety_wit_1 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "dest" ) )) # Ptr |-> (dest_pre))
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.undef_full dest_pre n_pre)
  ** (intArray.full_shape src_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_copy1_safety_wit_2 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape dest_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full_shape src_pre n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "dest" ) )) # Ptr |-> (dest_pre))
  ** ((( &( "src" ) )) # Ptr |-> (src_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_copy1_entail_wit_1 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.undef_full dest_pre n_pre)
  ** (intArray.full_shape src_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.seg_shape dest_pre (0 : Int) (0 : Int))
  ** (intArray.undef_seg dest_pre (0 : Int) n_pre)
  ** (intArray.full_shape src_pre n_pre)

noncomputable def array_copy1_entail_wit_2 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape dest_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full_shape src_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.seg_shape dest_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full_shape src_pre n_pre)

noncomputable def array_copy1_return_wit_1 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape dest_pre (0 : Int) i)
  ** (intArray.undef_seg dest_pre i n_pre)
  ** (intArray.full_shape src_pre n_pre)
|--
  (intArray.full_shape dest_pre n_pre)
  ** (intArray.full_shape src_pre n_pre)

noncomputable def array_copy1_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape dest_pre (0 : Int) i)
  ** (intArray.undef_seg dest_pre i n_pre)
  ** (intArray.full_shape src_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((src_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape src_pre i (0 : Int) n_pre)
  ** (intArray.seg_shape dest_pre (0 : Int) i)
  ** (intArray.undef_seg dest_pre i n_pre)

noncomputable def array_copy1_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (src_pre : Int) (dest_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape src_pre n_pre)
  ** (intArray.seg_shape dest_pre (0 : Int) i)
  ** (intArray.undef_seg dest_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((dest_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dest_pre (i + 1) n_pre)
  ** (intArray.full_shape src_pre n_pre)
  ** (intArray.seg_shape dest_pre (0 : Int) i)

noncomputable def array_concat_safety_wit_1 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : ((n_pre + m_pre) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
  ** (intArray.undef_full ret_pre (n_pre + m_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_concat_safety_wit_2 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full_shape b_pre m_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_concat_safety_wit_3 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.seg_shape ret_pre (0 : Int) i)
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_concat_safety_wit_4 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.seg_shape ret_pre (0 : Int) (n_pre + i))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  “ ((n_pre + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + i)) ”

noncomputable def array_concat_safety_wit_5 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) ((n_pre + i) + 1))
  ** (intArray.undef_seg ret_pre ((n_pre + i) + 1) (n_pre + m_pre))
  ** (intArray.full_shape b_pre m_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_concat_entail_wit_1 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
  ** (intArray.undef_full ret_pre (n_pre + m_pre))
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg_shape ret_pre (0 : Int) (0 : Int))
  ** (intArray.undef_seg ret_pre (0 : Int) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)

noncomputable def array_concat_entail_wit_2 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg_shape ret_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)

noncomputable def array_concat_entail_wit_3 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) i)
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg_shape ret_pre (0 : Int) (n_pre + (0 : Int)))
  ** (intArray.undef_seg ret_pre (n_pre + (0 : Int)) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)

noncomputable def array_concat_entail_wit_4 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) ((n_pre + i) + 1))
  ** (intArray.undef_seg ret_pre ((n_pre + i) + 1) (n_pre + m_pre))
  ** (intArray.full_shape b_pre m_pre)
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (intArray.seg_shape ret_pre (0 : Int) (n_pre + (i + 1)))
  ** (intArray.undef_seg ret_pre (n_pre + (i + 1)) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)

noncomputable def array_concat_return_wit_1 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i >= m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) (n_pre + i))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
  ** (intArray.full_shape ret_pre (n_pre + m_pre))

noncomputable def array_concat_partial_solve_wit_1 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) i)
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape a_pre i (0 : Int) n_pre)
  ** (intArray.seg_shape ret_pre (0 : Int) i)
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full_shape b_pre m_pre)

noncomputable def array_concat_partial_solve_wit_2 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.seg_shape ret_pre (0 : Int) i)
  ** (intArray.undef_seg ret_pre i (n_pre + m_pre))
  ** (intArray.full_shape b_pre m_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((ret_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ret_pre (i + 1) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.seg_shape ret_pre (0 : Int) i)
  ** (intArray.full_shape b_pre m_pre)

noncomputable def array_concat_partial_solve_wit_3 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.seg_shape ret_pre (0 : Int) (n_pre + i))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre m_pre)
|--
  EX x : Int,
  “ (i < m_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape b_pre i (0 : Int) m_pre)
  ** (intArray.seg_shape ret_pre (0 : Int) (n_pre + i))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_concat_partial_solve_wit_4 : Prop :=
  forall (m_pre : Int) (b_pre : Int) (n_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < m_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= m_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : ((n_pre + m_pre) < INT_MAX)) ,
  (intArray.full_shape b_pre m_pre)
  ** (intArray.seg_shape ret_pre (0 : Int) (n_pre + i))
  ** (intArray.undef_seg ret_pre (n_pre + i) (n_pre + m_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ (i < m_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ ((n_pre + m_pre) < INT_MAX) ”
  &&  (((ret_pre + ((n_pre + i) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ret_pre ((n_pre + i) + 1) (n_pre + m_pre))
  ** (intArray.full_shape b_pre m_pre)
  ** (intArray.seg_shape ret_pre (0 : Int) (n_pre + i))
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_swap_safety_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_swap_safety_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape b_pre n_pre)
  ** (intArray.full_shape a_pre n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_swap_entail_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)

noncomputable def array_swap_entail_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape b_pre n_pre)
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)

noncomputable def array_swap_return_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)
|--
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)

noncomputable def array_swap_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape a_pre i (0 : Int) n_pre)
  ** (intArray.full_shape b_pre n_pre)

noncomputable def array_swap_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape b_pre i (0 : Int) n_pre)
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_swap_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape b_pre n_pre)
  ** (intArray.full_shape a_pre n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i_shape a_pre i (0 : Int) n_pre)
  ** (intArray.full_shape b_pre n_pre)

noncomputable def array_swap_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** (intArray.full_shape b_pre n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i_shape b_pre i (0 : Int) n_pre)
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_vector_sum_safety_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.undef_full ret_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_vector_sum_safety_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape ret_pre (0 : Int) (i + 1))
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "ret" ) )) # Ptr |-> (ret_pre))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_vector_sum_entail_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.undef_full ret_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (uintArray.seg_shape ret_pre (0 : Int) (0 : Int))
  ** (uintArray.undef_seg ret_pre (0 : Int) n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)

noncomputable def array_vector_sum_entail_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape ret_pre (0 : Int) (i + 1))
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (uintArray.seg_shape ret_pre (0 : Int) (i + 1))
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)

noncomputable def array_vector_sum_return_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape ret_pre (0 : Int) i)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
|--
  (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape ret_pre n_pre)

noncomputable def array_vector_sum_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape ret_pre (0 : Int) i)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt |-> (x))
  ** (uintArray.missing_i_shape a_pre i (0 : Int) n_pre)
  ** (uintArray.seg_shape ret_pre (0 : Int) i)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full_shape b_pre n_pre)

noncomputable def array_vector_sum_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape ret_pre (0 : Int) i)
  ** (uintArray.undef_seg ret_pre i n_pre)
  ** (uintArray.full_shape b_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt |-> (x))
  ** (uintArray.missing_i_shape b_pre i (0 : Int) n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape ret_pre (0 : Int) i)
  ** (uintArray.undef_seg ret_pre i n_pre)

noncomputable def array_vector_sum_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (b_pre : Int) (a_pre : Int) (ret_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape ret_pre (0 : Int) i)
  ** (uintArray.undef_seg ret_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((ret_pre + (i * sizeof(UINT)))) # UInt |->_)
  ** (uintArray.undef_seg ret_pre (i + 1) n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape ret_pre (0 : Int) i)

noncomputable def pointwise_mul_safety_wit_1 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "c" ) )) # Ptr |-> (c_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.undef_full c_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def pointwise_mul_safety_wit_2 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape c_pre (0 : Int) (i + 1))
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "b" ) )) # Ptr |-> (b_pre))
  ** ((( &( "c" ) )) # Ptr |-> (c_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def pointwise_mul_entail_wit_1 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.undef_full c_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (uintArray.seg_shape c_pre (0 : Int) (0 : Int))
  ** (uintArray.undef_seg c_pre (0 : Int) n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)

noncomputable def pointwise_mul_entail_wit_2 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape c_pre (0 : Int) (i + 1))
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (uintArray.seg_shape c_pre (0 : Int) (i + 1))
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)

noncomputable def pointwise_mul_return_wit_1 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape c_pre (0 : Int) i)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
|--
  (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape c_pre n_pre)

noncomputable def pointwise_mul_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.seg_shape c_pre (0 : Int) i)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.full_shape b_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt |-> (x))
  ** (uintArray.missing_i_shape a_pre i (0 : Int) n_pre)
  ** (uintArray.seg_shape c_pre (0 : Int) i)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full_shape b_pre n_pre)

noncomputable def pointwise_mul_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape c_pre (0 : Int) i)
  ** (uintArray.undef_seg c_pre i n_pre)
  ** (uintArray.full_shape b_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt |-> (x))
  ** (uintArray.missing_i_shape b_pre i (0 : Int) n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape c_pre (0 : Int) i)
  ** (uintArray.undef_seg c_pre i n_pre)

noncomputable def pointwise_mul_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (c_pre : Int) (b_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape c_pre (0 : Int) i)
  ** (uintArray.undef_seg c_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((c_pre + (i * sizeof(UINT)))) # UInt |->_)
  ** (uintArray.undef_seg c_pre (i + 1) n_pre)
  ** (uintArray.full_shape b_pre n_pre)
  ** (uintArray.full_shape a_pre n_pre)
  ** (uintArray.seg_shape c_pre (0 : Int) i)

noncomputable def array_max_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "max" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def array_max_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "max" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def array_max_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "max" ) )) # Int |-> ((-1)))
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_max_safety_wit_4 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (v : Int) (x : Int) (x_2 : Int) (PreH1 : (x > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** ((( &( "max" ) )) # Int |-> (x_2))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_max_safety_wit_5 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (v : Int) (x : Int) (PreH1 : (x <= v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** ((( &( "max" ) )) # Int |-> (v))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_max_entail_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)

noncomputable def array_max_entail_wit_2_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (v : Int) (x : Int) (PreH1 : (x > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)

noncomputable def array_max_entail_wit_2_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (v : Int) (x : Int) (PreH1 : (x <= v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)

noncomputable def array_max_return_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  (intArray.full_shape a_pre n_pre)

noncomputable def array_max_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape a_pre i (0 : Int) n_pre)

noncomputable def array_max_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (v : Int) (x : Int) (PreH1 : (x > v)) (PreH2 : (i < n_pre)) (PreH3 : ((0 : Int) <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  EX x_2 : Int,
  “ (x > v) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> (x_2))
  ** (intArray.missing_i_shape a_pre i (0 : Int) n_pre)

noncomputable def memset_safety_wit_1 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
  ** (intArray.undef_full a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def memset_safety_wit_2 : Prop :=
  forall (value_pre : Int) (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape a_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "value" ) )) # Int |-> (value_pre))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def memset_entail_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.undef_full a_pre n_pre)
|--
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.seg_shape a_pre (0 : Int) (0 : Int))
  ** (intArray.undef_seg a_pre (0 : Int) n_pre)

noncomputable def memset_entail_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape a_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.seg_shape a_pre (0 : Int) (i + 1))
  ** (intArray.undef_seg a_pre (i + 1) n_pre)

noncomputable def memset_return_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape a_pre (0 : Int) i)
  ** (intArray.undef_seg a_pre i n_pre)
|--
  (intArray.full_shape a_pre n_pre)

noncomputable def memset_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (intArray.seg_shape a_pre (0 : Int) i)
  ** (intArray.undef_seg a_pre i n_pre)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg a_pre (i + 1) n_pre)
  ** (intArray.seg_shape a_pre (0 : Int) i)

noncomputable def array_to_list_safety_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "head" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_to_list_safety_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "tail" ) )) # Ptr |-> (retval))
  ** ((&((retval # "list")  ->ₛ "data")) # Int |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** ((( &( "head" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def array_to_list_safety_wit_3 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (v : Int) (tail : Int) (head : Int) (i : Int) (x : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head ≠ (0 : Int))) (PreH7 : (tail ≠ (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre < INT_MAX)) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full_shape a_pre n_pre)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Ptr |-> (head))
  ** ((( &( "tail" ) )) # Ptr |-> (retval))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (lseg head tail)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def array_to_list_entail_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> ((0 : Int)))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full_shape a_pre n_pre)
|--
  EX v : Int,
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg retval retval)
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_to_list_entail_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (v_2 : Int) (tail : Int) (head : Int) (i : Int) (x : Int) (retval_next : Int) (retval : Int) (PreH1 : (retval ≠ (0 : Int))) (PreH2 : (retval_next = (0 : Int))) (PreH3 : (i < n_pre)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head ≠ (0 : Int))) (PreH7 : (tail ≠ (0 : Int))) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre < INT_MAX)) ,
  ((&((retval # "list")  ->ₛ "data")) # Int |-> (x))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> (retval_next))
  ** (intArray.full_shape a_pre n_pre)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v_2))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> (retval))
  ** (lseg head tail)
|--
  EX v : Int,
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (head ≠ (0 : Int)) ” &&
  “ (retval ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  ((&((retval # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((retval # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head retval)
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_to_list_return_wit_1 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre < INT_MAX)) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head tail)
  ** (intArray.full_shape a_pre n_pre)
|--
  (listrep head)
  ** (intArray.full_shape a_pre n_pre)

noncomputable def array_to_list_partial_solve_wit_1_pure : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "head" ) )) # Ptr |->_)
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) = (0 : Int)) ”

noncomputable def array_to_list_partial_solve_wit_1_aux : Prop :=
  forall (n_pre : Int) (a_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)

noncomputable def array_to_list_partial_solve_wit_1 : Prop := array_to_list_partial_solve_wit_1_pure -> array_to_list_partial_solve_wit_1_aux

noncomputable def array_to_list_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (a_pre : Int) (v : Int) (tail : Int) (head : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre < INT_MAX)) ,
  ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head tail)
  ** (intArray.full_shape a_pre n_pre)
|--
  EX x : Int,
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (head ≠ (0 : Int)) ” &&
  “ (tail ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int |-> (x))
  ** (intArray.missing_i_shape a_pre i (0 : Int) n_pre)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head tail)

noncomputable def array_to_list_partial_solve_wit_3_pure : Prop :=
  forall (n_pre : Int) (a_pre : Int) (v : Int) (tail : Int) (head : Int) (i : Int) (x : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** ((( &( "node" ) )) # Ptr |->_)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "head" ) )) # Ptr |-> (head))
  ** ((( &( "tail" ) )) # Ptr |-> (tail))
  ** ((( &( "a" ) )) # Ptr |-> (a_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head tail)
|--
  “ (x = x) ”

noncomputable def array_to_list_partial_solve_wit_3_aux : Prop :=
  forall (n_pre : Int) (a_pre : Int) (v : Int) (tail : Int) (head : Int) (i : Int) (x : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head ≠ (0 : Int))) (PreH5 : (tail ≠ (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre < INT_MAX)) ,
  (intArray.full_shape a_pre n_pre)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head tail)
|--
  “ (x = x) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (head ≠ (0 : Int)) ” &&
  “ (tail ≠ (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre < INT_MAX) ”
  &&  (intArray.full_shape a_pre n_pre)
  ** ((&((tail # "list")  ->ₛ "data")) # Int |-> (v))
  ** ((&((tail # "list")  ->ₛ "next")) # Ptr |-> ((0 : Int)))
  ** (lseg head tail)

noncomputable def array_to_list_partial_solve_wit_3 : Prop := array_to_list_partial_solve_wit_3_pure -> array_to_list_partial_solve_wit_3_aux


structure VC_Correct : Type where
  proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1
  proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2
  proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3
  proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1
  proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2
  proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1
  proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1
  proof_of_array_copy1_safety_wit_1 : array_copy1_safety_wit_1
  proof_of_array_copy1_safety_wit_2 : array_copy1_safety_wit_2
  proof_of_array_copy1_entail_wit_1 : array_copy1_entail_wit_1
  proof_of_array_copy1_entail_wit_2 : array_copy1_entail_wit_2
  proof_of_array_copy1_return_wit_1 : array_copy1_return_wit_1
  proof_of_array_copy1_partial_solve_wit_1 : array_copy1_partial_solve_wit_1
  proof_of_array_copy1_partial_solve_wit_2 : array_copy1_partial_solve_wit_2
  proof_of_array_concat_safety_wit_1 : array_concat_safety_wit_1
  proof_of_array_concat_safety_wit_2 : array_concat_safety_wit_2
  proof_of_array_concat_safety_wit_3 : array_concat_safety_wit_3
  proof_of_array_concat_safety_wit_4 : array_concat_safety_wit_4
  proof_of_array_concat_safety_wit_5 : array_concat_safety_wit_5
  proof_of_array_concat_entail_wit_1 : array_concat_entail_wit_1
  proof_of_array_concat_entail_wit_2 : array_concat_entail_wit_2
  proof_of_array_concat_entail_wit_3 : array_concat_entail_wit_3
  proof_of_array_concat_entail_wit_4 : array_concat_entail_wit_4
  proof_of_array_concat_return_wit_1 : array_concat_return_wit_1
  proof_of_array_concat_partial_solve_wit_1 : array_concat_partial_solve_wit_1
  proof_of_array_concat_partial_solve_wit_2 : array_concat_partial_solve_wit_2
  proof_of_array_concat_partial_solve_wit_3 : array_concat_partial_solve_wit_3
  proof_of_array_concat_partial_solve_wit_4 : array_concat_partial_solve_wit_4
  proof_of_array_swap_safety_wit_1 : array_swap_safety_wit_1
  proof_of_array_swap_safety_wit_2 : array_swap_safety_wit_2
  proof_of_array_swap_entail_wit_1 : array_swap_entail_wit_1
  proof_of_array_swap_entail_wit_2 : array_swap_entail_wit_2
  proof_of_array_swap_return_wit_1 : array_swap_return_wit_1
  proof_of_array_swap_partial_solve_wit_1 : array_swap_partial_solve_wit_1
  proof_of_array_swap_partial_solve_wit_2 : array_swap_partial_solve_wit_2
  proof_of_array_swap_partial_solve_wit_3 : array_swap_partial_solve_wit_3
  proof_of_array_swap_partial_solve_wit_4 : array_swap_partial_solve_wit_4
  proof_of_array_vector_sum_safety_wit_1 : array_vector_sum_safety_wit_1
  proof_of_array_vector_sum_safety_wit_2 : array_vector_sum_safety_wit_2
  proof_of_array_vector_sum_entail_wit_1 : array_vector_sum_entail_wit_1
  proof_of_array_vector_sum_entail_wit_2 : array_vector_sum_entail_wit_2
  proof_of_array_vector_sum_return_wit_1 : array_vector_sum_return_wit_1
  proof_of_array_vector_sum_partial_solve_wit_1 : array_vector_sum_partial_solve_wit_1
  proof_of_array_vector_sum_partial_solve_wit_2 : array_vector_sum_partial_solve_wit_2
  proof_of_array_vector_sum_partial_solve_wit_3 : array_vector_sum_partial_solve_wit_3
  proof_of_pointwise_mul_safety_wit_1 : pointwise_mul_safety_wit_1
  proof_of_pointwise_mul_safety_wit_2 : pointwise_mul_safety_wit_2
  proof_of_pointwise_mul_entail_wit_1 : pointwise_mul_entail_wit_1
  proof_of_pointwise_mul_entail_wit_2 : pointwise_mul_entail_wit_2
  proof_of_pointwise_mul_return_wit_1 : pointwise_mul_return_wit_1
  proof_of_pointwise_mul_partial_solve_wit_1 : pointwise_mul_partial_solve_wit_1
  proof_of_pointwise_mul_partial_solve_wit_2 : pointwise_mul_partial_solve_wit_2
  proof_of_pointwise_mul_partial_solve_wit_3 : pointwise_mul_partial_solve_wit_3
  proof_of_array_max_safety_wit_1 : array_max_safety_wit_1
  proof_of_array_max_safety_wit_2 : array_max_safety_wit_2
  proof_of_array_max_safety_wit_3 : array_max_safety_wit_3
  proof_of_array_max_safety_wit_4 : array_max_safety_wit_4
  proof_of_array_max_safety_wit_5 : array_max_safety_wit_5
  proof_of_array_max_entail_wit_1 : array_max_entail_wit_1
  proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1
  proof_of_array_max_entail_wit_2_2 : array_max_entail_wit_2_2
  proof_of_array_max_return_wit_1 : array_max_return_wit_1
  proof_of_array_max_partial_solve_wit_1 : array_max_partial_solve_wit_1
  proof_of_array_max_partial_solve_wit_2 : array_max_partial_solve_wit_2
  proof_of_memset_safety_wit_1 : memset_safety_wit_1
  proof_of_memset_safety_wit_2 : memset_safety_wit_2
  proof_of_memset_entail_wit_1 : memset_entail_wit_1
  proof_of_memset_entail_wit_2 : memset_entail_wit_2
  proof_of_memset_return_wit_1 : memset_return_wit_1
  proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1
  proof_of_array_to_list_safety_wit_1 : array_to_list_safety_wit_1
  proof_of_array_to_list_safety_wit_2 : array_to_list_safety_wit_2
  proof_of_array_to_list_safety_wit_3 : array_to_list_safety_wit_3
  proof_of_array_to_list_entail_wit_1 : array_to_list_entail_wit_1
  proof_of_array_to_list_entail_wit_2 : array_to_list_entail_wit_2
  proof_of_array_to_list_return_wit_1 : array_to_list_return_wit_1
  proof_of_array_to_list_partial_solve_wit_1_pure : array_to_list_partial_solve_wit_1_pure
  proof_of_array_to_list_partial_solve_wit_1 : array_to_list_partial_solve_wit_1
  proof_of_array_to_list_partial_solve_wit_2 : array_to_list_partial_solve_wit_2
  proof_of_array_to_list_partial_solve_wit_3_pure : array_to_list_partial_solve_wit_3_pure
  proof_of_array_to_list_partial_solve_wit_3 : array_to_list_partial_solve_wit_3

end SimpleC.EE.QCP_demos_LLM.generated.array_auto_goal
