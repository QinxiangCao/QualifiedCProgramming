import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P053_1594D_the_number_of_imposters_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def solver_safety_wit_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (m_pre <= 500000)) (PreH4 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> ((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))))) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((((Znth i_2 comment_sources (0 : Int)) = (fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((Znth i_2 comment_targets (0 : Int)) = (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i_2 comment_kinds (0 : Int)) = (snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) ,
  ((( &( "v" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (ws : (List Int)) (ts : (List Int)) (ns : (List Int)) (hs : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs)) = (n_pre + 1))) (PreH14 : ((Zlength (ns)) = (2 * m_pre))) (PreH15 : ((Zlength (ts)) = (2 * m_pre))) (PreH16 : ((Zlength (ws)) = (2 * m_pre))) (PreH17 : ((Zlength (cs)) = (n_pre + 1))) (PreH18 : ((Zlength (ks)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs v)) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth (v) ((-1)) (hs)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((v + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (v + 1)) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (ws : (List Int)) (ts : (List Int)) (ns : (List Int)) (hs : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs)) = (n_pre + 1))) (PreH14 : ((Zlength (ns)) = (2 * m_pre))) (PreH15 : ((Zlength (ts)) = (2 * m_pre))) (PreH16 : ((Zlength (ws)) = (2 * m_pre))) (PreH17 : ((Zlength (cs)) = (n_pre + 1))) (PreH18 : ((Zlength (ks)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs v)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (ws : (List Int)) (ts : (List Int)) (ns : (List Int)) (hs : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs)) = (n_pre + 1))) (PreH14 : ((Zlength (ns)) = (2 * m_pre))) (PreH15 : ((Zlength (ts)) = (2 * m_pre))) (PreH16 : ((Zlength (ws)) = (2 * m_pre))) (PreH17 : ((Zlength (cs)) = (n_pre + 1))) (PreH18 : ((Zlength (ks)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs v)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (ws : (List Int)) (ts : (List Int)) (ns : (List Int)) (hs : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs)) = (n_pre + 1))) (PreH14 : ((Zlength (ns)) = (2 * m_pre))) (PreH15 : ((Zlength (ts)) = (2 * m_pre))) (PreH16 : ((Zlength (ws)) = (2 * m_pre))) (PreH17 : ((Zlength (cs)) = (n_pre + 1))) (PreH18 : ((Zlength (ks)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs v)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "e" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((2 * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "e" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (((2 * i) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i) + 1)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (((2 * i) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i) + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (((2 * i) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i) + 1)) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full nxt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (((2 * i) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i) + 1)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full nxt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** ((( &( "v" ) )) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "u" ) )) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** ((( &( "e" ) )) # Int |-> ((2 * i)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_targets (0 : Int))) (((2 * i) + 1)) ((replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "v" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH15 : ((Zlength (cs)) = (n_pre + 1))) (PreH16 : ((Zlength (ks)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs v)) ,
  (intArray.full color_pre (n_pre + 1) (replace_Znth (v) ((-1)) (cs)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((v + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (v + 1)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH15 : ((Zlength (cs)) = (n_pre + 1))) (PreH16 : ((Zlength (ks)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs v)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH15 : ((Zlength (cs)) = (n_pre + 1))) (PreH16 : ((Zlength (ks)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs v)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH15 : ((Zlength (cs)) = (n_pre + 1))) (PreH16 : ((Zlength (ks)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs v)) ,
  ((( &( "total" ) )) # Int64 |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH15 : ((Zlength (cs)) = (n_pre + 1))) (PreH16 : ((Zlength (ks)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs v)) ,
  ((( &( "s" ) )) # Int |->_)
  ** ((( &( "total" ) )) # Int64 |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_23 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (s <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1))) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH16 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH17 : (ColourValues n_pre cs)) (PreH18 : (ParityRespected comments cs)) (PreH19 : (ColouredClosed comments cs)) (PreH20 : (MaxImpostersOn n_pre comments cs total)) (PreH21 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "top" ) )) # Int |->_)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "top" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full stack__pre (n_pre + 1) (replace_Znth ((0 : Int)) (s) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth (s) ((0 : Int)) (cs)))
  ** ((( &( "top" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ (((0 : Int) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((0 : Int) + 1)) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "c1" ) )) # Int |->_)
  ** ((( &( "c0" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full stack__pre (n_pre + 1) (replace_Znth ((0 : Int)) (s) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth (s) ((0 : Int)) (cs)))
  ** ((( &( "top" ) )) # Int |-> (((0 : Int) + 1)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  ((( &( "c0" ) )) # Int |->_)
  ** (intArray.full stack__pre (n_pre + 1) (replace_Znth ((0 : Int)) (s) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth (s) ((0 : Int)) (cs)))
  ** ((( &( "top" ) )) # Int |-> (((0 : Int) + 1)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : ((0 : Int) <= top)) (PreH15 : (top <= n_pre)) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1))) (PreH21 : ((Zlength (ks)) = (n_pre + 1))) (PreH22 : (ColourValues n_pre before)) (PreH23 : (ParityRespected comments before)) (PreH24 : (ColouredClosed comments before)) (PreH25 : (MaxImpostersOn n_pre comments before total)) (PreH26 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH27 : ((Znth s before (0 : Int)) = (-1))) (PreH28 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH32 : (top ≠ (0 : Int))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((top - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top - 1)) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : ((0 : Int) <= top)) (PreH15 : (top <= n_pre)) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1))) (PreH21 : ((Zlength (ks)) = (n_pre + 1))) (PreH22 : (ColourValues n_pre before)) (PreH23 : (ParityRespected comments before)) (PreH24 : (ColouredClosed comments before)) (PreH25 : (MaxImpostersOn n_pre comments before total)) (PreH26 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH27 : ((Znth s before (0 : Int)) = (-1))) (PreH28 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH32 : (top ≠ (0 : Int))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** ((( &( "u" ) )) # Int |-> ((Znth (top - 1) ks (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> ((top - 1)))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : ((0 : Int) <= top)) (PreH16 : (top <= n_pre)) (PreH17 : ((0 : Int) <= c0)) (PreH18 : ((0 : Int) <= c1)) (PreH19 : ((c0 + c1) <= n_pre)) (PreH20 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) (PreH23 : (ColourValues n_pre before)) (PreH24 : (ParityRespected comments before)) (PreH25 : (ColouredClosed comments before)) (PreH26 : (MaxImpostersOn n_pre comments before total)) (PreH27 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH28 : ((Znth s before (0 : Int)) = (-1))) (PreH29 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH33 : (top ≠ (0 : Int))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** ((( &( "u" ) )) # Int |-> ((Znth (top - 1) ks (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> ((top - 1)))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((c0 + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c0 + 1)) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : ((0 : Int) <= top)) (PreH16 : (top <= n_pre)) (PreH17 : ((0 : Int) <= c0)) (PreH18 : ((0 : Int) <= c1)) (PreH19 : ((c0 + c1) <= n_pre)) (PreH20 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) (PreH23 : (ColourValues n_pre before)) (PreH24 : (ParityRespected comments before)) (PreH25 : (ColouredClosed comments before)) (PreH26 : (MaxImpostersOn n_pre comments before total)) (PreH27 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH28 : ((Znth s before (0 : Int)) = (-1))) (PreH29 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH33 : (top ≠ (0 : Int))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** ((( &( "u" ) )) # Int |-> ((Znth (top - 1) ks (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> ((top - 1)))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((c1 + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (c1 + 1)) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs (0 : Int)) = 1)) (PreH17 : ((0 : Int) <= top)) (PreH18 : (top <= n_pre)) (PreH19 : ((0 : Int) <= c0)) (PreH20 : ((0 : Int) <= c1)) (PreH21 : ((c0 + c1) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre))) (PreH24 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH25 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH26 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1))) (PreH28 : ((Zlength (ks)) = (n_pre + 1))) (PreH29 : (ColourValues n_pre before)) (PreH30 : (ParityRespected comments before)) (PreH31 : (ColouredClosed comments before)) (PreH32 : (MaxImpostersOn n_pre comments before total)) (PreH33 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH34 : ((Znth s before (0 : Int)) = (-1))) (PreH35 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH17 : ((0 : Int) <= top)) (PreH18 : (top <= n_pre)) (PreH19 : ((0 : Int) <= c0)) (PreH20 : ((0 : Int) <= c1)) (PreH21 : ((c0 + c1) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre))) (PreH24 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH25 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH26 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1))) (PreH28 : ((Zlength (ks)) = (n_pre + 1))) (PreH29 : (ColourValues n_pre before)) (PreH30 : (ParityRespected comments before)) (PreH31 : (ColouredClosed comments before)) (PreH32 : (MaxImpostersOn n_pre comments before total)) (PreH33 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH34 : ((Znth s before (0 : Int)) = (-1))) (PreH35 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH17 : ((0 : Int) <= top)) (PreH18 : (top <= n_pre)) (PreH19 : ((0 : Int) <= c0)) (PreH20 : ((0 : Int) <= c1)) (PreH21 : ((c0 + c1) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre))) (PreH24 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH25 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH26 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1))) (PreH28 : ((Zlength (ks)) = (n_pre + 1))) (PreH29 : (ColourValues n_pre before)) (PreH30 : (ParityRespected comments before)) (PreH31 : (ColouredClosed comments before)) (PreH32 : (MaxImpostersOn n_pre comments before total)) (PreH33 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH34 : ((Znth s before (0 : Int)) = (-1))) (PreH35 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : (1 <= u)) (PreH15 : (u <= n_pre)) (PreH16 : ((Znth u cs (0 : Int)) = 1)) (PreH17 : ((0 : Int) <= top)) (PreH18 : (top <= n_pre)) (PreH19 : ((0 : Int) <= c0)) (PreH20 : ((0 : Int) <= c1)) (PreH21 : ((c0 + c1) <= n_pre)) (PreH22 : ((-1) <= e)) (PreH23 : (e < (2 * m_pre))) (PreH24 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH25 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH26 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH27 : ((Zlength (before)) = (n_pre + 1))) (PreH28 : ((Zlength (ks)) = (n_pre + 1))) (PreH29 : (ColourValues n_pre before)) (PreH30 : (ParityRespected comments before)) (PreH31 : (ColouredClosed comments before)) (PreH32 : (MaxImpostersOn n_pre comments before total)) (PreH33 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH34 : ((Znth s before (0 : Int)) = (-1))) (PreH35 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH36 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH37 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH38 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** ((( &( "want" ) )) # Int |-> ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))))
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** ((( &( "v" ) )) # Int |-> ((Znth e ts (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_38 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** ((( &( "want" ) )) # Int |-> ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))))
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** ((( &( "v" ) )) # Int |-> ((Znth e ts (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_39 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts (0 : Int))) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** ((( &( "want" ) )) # Int |-> ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))))
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** ((( &( "v" ) )) # Int |-> ((Znth e ts (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
|--
  “ ((top + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top + 1)) ”

noncomputable def solver_safety_wit_40 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = 1)) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts (0 : Int))) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** ((( &( "want" ) )) # Int |-> ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))))
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** ((( &( "v" ) )) # Int |-> ((Znth e ts (0 : Int))))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
|--
  “ ((top + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (top + 1)) ”

noncomputable def solver_safety_wit_41 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (e : Int) (u : Int) (v : Int) (want : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= n_pre)) (PreH12 : ((0 : Int) <= c0)) (PreH13 : ((0 : Int) <= c1)) (PreH14 : ((c0 + c1) <= n_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e < (2 * m_pre))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((0 : Int) <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "want" ) )) # Int |-> (want))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def solver_safety_wit_42 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (e : Int) (u : Int) (v : Int) (want : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= n_pre)) (PreH12 : ((0 : Int) <= c0)) (PreH13 : ((0 : Int) <= c1)) (PreH14 : ((c0 + c1) <= n_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e < (2 * m_pre))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((0 : Int) <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** ((( &( "e" ) )) # Int |-> (e))
  ** ((( &( "u" ) )) # Int |-> (u))
  ** ((( &( "v" ) )) # Int |-> (v))
  ** ((( &( "want" ) )) # Int |-> (want))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_43 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (before : (List Int)) (cs : (List Int)) (ks : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((total + c1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + c1)) ”

noncomputable def solver_safety_wit_44 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (before : (List Int)) (cs : (List Int)) (ks : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "top" ) )) # Int |-> (top))
  ** ((( &( "c0" ) )) # Int |-> (c0))
  ** ((( &( "c1" ) )) # Int |-> (c1))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((total + c0) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + c0)) ”

noncomputable def solver_safety_wit_45 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (before : (List Int)) (cs : (List Int)) (ks : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> ((total + c0)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((s + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s + 1)) ”

noncomputable def solver_safety_wit_46 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (before : (List Int)) (cs : (List Int)) (ks : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> ((total + c1)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((s + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s + 1)) ”

noncomputable def solver_safety_wit_47 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) >= (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "comment_u" ) )) # Ptr |-> (comment_u_pre))
  ** ((( &( "comment_v" ) )) # Ptr |-> (comment_v_pre))
  ** ((( &( "comment_diff" ) )) # Ptr |-> (comment_diff_pre))
  ** ((( &( "head" ) )) # Ptr |-> (head_pre))
  ** ((( &( "nxt" ) )) # Ptr |-> (nxt_pre))
  ** ((( &( "to" ) )) # Ptr |-> (to_pre))
  ** ((( &( "wt" ) )) # Ptr |-> (wt_pre))
  ** ((( &( "color" ) )) # Ptr |-> (color_pre))
  ** ((( &( "stack_" ) )) # Ptr |-> (stack__pre))
  ** ((( &( "s" ) )) # Int |-> (s))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((s + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (s + 1)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (m_pre <= 500000)) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((((((1 <= (fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = 1))))) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < m_pre)) -> ((((Znth i_3 comment_sources (0 : Int)) = (fst ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((Znth i_3 comment_targets (0 : Int)) = (snd ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i_3 comment_kinds (0 : Int)) = (snd ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
|--
  EX ks : (List Int), EX cs : (List Int), EX ws : (List Int), EX ts : (List Int), EX ns : (List Int), EX hs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (hs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ns)) = (2 * m_pre)) ” &&
  “ ((Zlength (ts)) = (2 * m_pre)) ” &&
  “ ((Zlength (ws)) = (2 * m_pre)) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (HeadsInitialised hs 1) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (m_pre <= 500000)) (PreH4 : forall (i_2 : Int) , ((((0 : Int) <= i_2) ∧ (i_2 < m_pre)) -> ((((((1 <= (fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i_2 comments __default__Prod__Prod_Z_Z_Z))) = 1))))) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (i_3 : Int) , ((((0 : Int) <= i_3) ∧ (i_3 < m_pre)) -> ((((Znth i_3 comment_sources (0 : Int)) = (fst ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((Znth i_3 comment_targets (0 : Int)) = (snd ((fst ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i_3 comment_kinds (0 : Int)) = (snd ((Znth i_3 comments __default__Prod__Prod_Z_Z_Z))))))) ,
  (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
|--
  EX ks : (List Int), EX cs : (List Int), EX ws : (List Int), EX ts : (List Int), EX ns : (List Int), EX hs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((Zlength (hs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ns)) = (2 * m_pre)) ” &&
  “ ((Zlength (ts)) = (2 * m_pre)) ” &&
  “ ((Zlength (ws)) = (2 * m_pre)) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (HeadsInitialised hs 1) ”
  &&  (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth (v) ((-1)) (hs_2)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX ws : (List Int), EX ts : (List Int), EX ns : (List Int), EX hs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= (v + 1)) ” &&
  “ ((v + 1) <= (n_pre + 1)) ” &&
  “ ((Zlength (hs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ns)) = (2 * m_pre)) ” &&
  “ ((Zlength (ts)) = (2 * m_pre)) ” &&
  “ ((Zlength (ws)) = (2 * m_pre)) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (HeadsInitialised hs (v + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  TT && emp 
|--
  “ (HeadsInitialised (replace_Znth (v) ((-1)) (hs_2)) (v + 1)) ” &&
  “ ((Zlength ((replace_Znth (v) ((-1)) (hs_2)))) = (n_pre + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  (HeadsInitialised (replace_Znth (v) ((-1)) (hs_2)) (v + 1))

noncomputable def solver_entail_wit_2_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  ((Zlength ((replace_Znth (v) ((-1)) (hs_2)))) = (n_pre + 1))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (((0 : Int) < m_pre) -> (((((1 <= (Znth (0 : Int) comment_sources (0 : Int))) ∧ ((Znth (0 : Int) comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth (0 : Int) comment_targets (0 : Int)))) ∧ ((Znth (0 : Int) comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth (0 : Int) comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth (0 : Int) comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre (0 : Int) hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre (0 : Int) hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  TT && emp 
|--
  “ (ForwardStarRanges n_pre (0 : Int) hs_2 ns_2 ts_2 ws_2) ” &&
  “ (ForwardStar n_pre m_pre (0 : Int) hs_2 ns_2 ts_2 ws_2 comments) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  (ForwardStarRanges n_pre (0 : Int) hs_2 ns_2 ts_2 ws_2)

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  (ForwardStar n_pre m_pre (0 : Int) hs_2 ns_2 ts_2 ws_2 comments)

noncomputable def solver_entail_wit_3_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (ns_2 : (List Int)) (hs_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs_2)) = (n_pre + 1))) (PreH14 : ((Zlength (ns_2)) = (2 * m_pre))) (PreH15 : ((Zlength (ts_2)) = (2 * m_pre))) (PreH16 : ((Zlength (ws_2)) = (2 * m_pre))) (PreH17 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH18 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs_2 v)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_targets (0 : Int))) (((2 * i) + 1)) ((replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)))))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs_2 (0 : Int))) (ns_2)))))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws_2)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts_2)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= m_pre) ” &&
  “ (((i + 1) < m_pre) -> (((((1 <= (Znth (i + 1) comment_sources (0 : Int))) ∧ ((Znth (i + 1) comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth (i + 1) comment_targets (0 : Int)))) ∧ ((Znth (i + 1) comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth (i + 1) comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth (i + 1) comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre (i + 1) hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre (i + 1) hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  TT && emp 
|--
  “ (ForwardStarRanges n_pre (i + 1) (replace_Znth ((Znth i comment_targets (0 : Int))) (((2 * i) + 1)) ((replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)))) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs_2 (0 : Int))) (ns_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws_2))))) ” &&
  “ (ForwardStar n_pre m_pre (i + 1) (replace_Znth ((Znth i comment_targets (0 : Int))) (((2 * i) + 1)) ((replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)))) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs_2 (0 : Int))) (ns_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws_2)))) comments) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (ForwardStarRanges n_pre (i + 1) (replace_Znth ((Znth i comment_targets (0 : Int))) (((2 * i) + 1)) ((replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)))) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs_2 (0 : Int))) (ns_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws_2)))))

noncomputable def solver_entail_wit_4_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (ForwardStar n_pre m_pre (i + 1) (replace_Znth ((Znth i comment_targets (0 : Int))) (((2 * i) + 1)) ((replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)))) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs_2)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs_2 (0 : Int))) (ns_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts_2)))) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws_2)))) comments)

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColoursInitialised cs 1) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  TT && emp 
|--
  “ (ColoursInitialised cs_2 1) ” &&
  “ (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (ColoursInitialised cs_2 1)

noncomputable def solver_entail_wit_5_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)

noncomputable def solver_entail_wit_5_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)

noncomputable def solver_entail_wit_5_split_goal_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i >= m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs_2 ns_2 ts_2 ws_2 comments)) (PreH15 : (ForwardStarRanges n_pre i hs_2 ns_2 ts_2 ws_2)) (PreH16 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH17 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v)) ,
  (intArray.full color_pre (n_pre + 1) (replace_Znth (v) ((-1)) (cs_2)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= (v + 1)) ” &&
  “ ((v + 1) <= (n_pre + 1)) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColoursInitialised cs (v + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v)) ,
  TT && emp 
|--
  “ (ColoursInitialised (replace_Znth (v) ((-1)) (cs_2)) (v + 1)) ” &&
  “ ((Zlength ((replace_Znth (v) ((-1)) (cs_2)))) = (n_pre + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v)) ,
  (ColoursInitialised (replace_Znth (v) ((-1)) (cs_2)) (v + 1))

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v)) ,
  ((Zlength ((replace_Znth (v) ((-1)) (cs_2)))) = (n_pre + 1))

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs (0 : Int)) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < 1)) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  TT && emp 
|--
  “ forall (v : Int) , (((1 <= v) ∧ (v < 1)) -> ((Znth v cs_2 (0 : Int)) ≠ (-1))) ” &&
  “ (MaxImpostersOn n_pre comments cs_2 (0 : Int)) ” &&
  “ (ColouredClosed comments cs_2) ” &&
  “ (ParityRespected comments cs_2) ” &&
  “ (ColourValues n_pre cs_2) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  forall (v : Int) , (((1 <= v) ∧ (v < 1)) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))

noncomputable def solver_entail_wit_7_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  (MaxImpostersOn n_pre comments cs_2 (0 : Int))

noncomputable def solver_entail_wit_7_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  (ColouredClosed comments cs_2)

noncomputable def solver_entail_wit_7_split_goal_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  (ParityRespected comments cs_2)

noncomputable def solver_entail_wit_7_split_goal_5 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  (ColourValues n_pre cs_2)

noncomputable def solver_entail_wit_7_split_goal_6 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (v_2 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v_2 > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v_2)) (PreH12 : (v_2 <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH15 : ((Zlength (cs_2)) = (n_pre + 1))) (PreH16 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs_2 v_2)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))

noncomputable def solver_entail_wit_8 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs_2 (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH18 : (ColourValues n_pre cs_2)) (PreH19 : (ParityRespected comments cs_2)) (PreH20 : (ColouredClosed comments cs_2)) (PreH21 : (MaxImpostersOn n_pre comments cs_2 total)) (PreH22 : forall (v_2 : Int) , (((1 <= v_2) ∧ (v_2 < s)) -> ((Znth v_2 cs_2 (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (intArray.full stack__pre (n_pre + 1) (replace_Znth ((0 : Int)) (s) (ks_2)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth (s) ((0 : Int)) (cs_2)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
|--
  EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int), EX finished : (List Int), EX cs : (List Int), EX before : (List Int), EX ks : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= ((0 : Int) + 1)) ” &&
  “ (((0 : Int) + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (((0 : Int) + (0 : Int)) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < ((0 : Int) + 1))) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (((0 : Int) + 1)) (ks)) (0 : Int) (0 : Int)) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs_2 (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH18 : (ColourValues n_pre cs_2)) (PreH19 : (ParityRespected comments cs_2)) (PreH20 : (ColouredClosed comments cs_2)) (PreH21 : (MaxImpostersOn n_pre comments cs_2 total)) (PreH22 : forall (v_2 : Int) , (((1 <= v_2) ∧ (v_2 < s)) -> ((Znth v_2 cs_2 (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  TT && emp 
|--
  EX finished : (List Int), EX before : (List Int),
  “ ((0 : Int) <= ((0 : Int) + 1)) ” &&
  “ (((0 : Int) + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ (((0 : Int) + (0 : Int)) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < ((0 : Int) + 1))) -> ((1 <= (Znth j (replace_Znth ((0 : Int)) (s) (ks_2)) (0 : Int))) ∧ ((Znth j (replace_Znth ((0 : Int)) (s) (ks_2)) (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength ((replace_Znth ((0 : Int)) (s) (ks_2)))) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s (replace_Znth (s) ((0 : Int)) (cs_2)) (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before (replace_Znth (s) ((0 : Int)) (cs_2)) finished (sublist ((0 : Int)) (((0 : Int) + 1)) ((replace_Znth ((0 : Int)) (s) (ks_2)))) (0 : Int) (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_9_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (finished_2 : (List Int)) (cs_2 : (List Int)) (before_2 : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth (top - 1) ks (0 : Int)) cs_2 (0 : Int)) = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : ((0 : Int) <= top)) (PreH16 : (top <= n_pre)) (PreH17 : ((0 : Int) <= c0)) (PreH18 : ((0 : Int) <= c1)) (PreH19 : ((c0 + c1) <= n_pre)) (PreH20 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < top)) -> ((1 <= (Znth j_2 ks (0 : Int))) ∧ ((Znth j_2 ks (0 : Int)) <= n_pre)))) (PreH21 : ((Zlength (before_2)) = (n_pre + 1))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) (PreH23 : (ColourValues n_pre before_2)) (PreH24 : (ParityRespected comments before_2)) (PreH25 : (ColouredClosed comments before_2)) (PreH26 : (MaxImpostersOn n_pre comments before_2 total)) (PreH27 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before_2 (0 : Int)) ≠ (-1)))) (PreH28 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH29 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns_2 ts_2 ws_2 comments)) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns_2 ts_2 ws_2)) (PreH33 : (top ≠ (0 : Int))) ,
  (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
|--
  (EX hs_2 : (List Int), EX finished : (List Int), EX before : (List Int), EX ks_2 : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= (Znth (top - 1) ks (0 : Int))) ” &&
  “ ((Znth (top - 1) ks (0 : Int)) <= n_pre) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (c0 + 1)) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ (((c0 + 1) + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int))) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top - 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top - 1))) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks_2)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top - 1)) (ks_2)) (Znth (top - 1) ks (0 : Int)) (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) (c0 + 1) c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks_2))
  ||
  (EX hs_2 : (List Int), EX finished : (List Int), EX before : (List Int), EX ks_2 : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= (Znth (top - 1) ks (0 : Int))) ” &&
  “ ((Znth (top - 1) ks (0 : Int)) <= n_pre) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (c0 + 1)) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ (((c0 + 1) + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int))) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top - 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top - 1))) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks_2)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top - 1)) (ks_2)) (Znth (top - 1) ks (0 : Int)) (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) (c0 + 1) c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks_2))

noncomputable def solver_entail_wit_9_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (finished_2 : (List Int)) (cs_2 : (List Int)) (before_2 : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth (top - 1) ks (0 : Int)) cs_2 (0 : Int)) ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : ((0 : Int) <= top)) (PreH16 : (top <= n_pre)) (PreH17 : ((0 : Int) <= c0)) (PreH18 : ((0 : Int) <= c1)) (PreH19 : ((c0 + c1) <= n_pre)) (PreH20 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < top)) -> ((1 <= (Znth j_2 ks (0 : Int))) ∧ ((Znth j_2 ks (0 : Int)) <= n_pre)))) (PreH21 : ((Zlength (before_2)) = (n_pre + 1))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) (PreH23 : (ColourValues n_pre before_2)) (PreH24 : (ParityRespected comments before_2)) (PreH25 : (ColouredClosed comments before_2)) (PreH26 : (MaxImpostersOn n_pre comments before_2 total)) (PreH27 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before_2 (0 : Int)) ≠ (-1)))) (PreH28 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH29 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns_2 ts_2 ws_2 comments)) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns_2 ts_2 ws_2)) (PreH33 : (top ≠ (0 : Int))) ,
  (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
|--
  (EX hs_2 : (List Int), EX finished : (List Int), EX before : (List Int), EX ks_2 : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= (Znth (top - 1) ks (0 : Int))) ” &&
  “ ((Znth (top - 1) ks (0 : Int)) <= n_pre) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= (c1 + 1)) ” &&
  “ ((c0 + (c1 + 1)) <= n_pre) ” &&
  “ ((-1) <= (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int))) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top - 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top - 1))) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks_2)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top - 1)) (ks_2)) (Znth (top - 1) ks (0 : Int)) (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) c0 (c1 + 1)) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks_2))
  ||
  (EX hs_2 : (List Int), EX finished : (List Int), EX before : (List Int), EX ks_2 : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= (Znth (top - 1) ks (0 : Int))) ” &&
  “ ((Znth (top - 1) ks (0 : Int)) <= n_pre) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= (top - 1)) ” &&
  “ ((top - 1) <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= (c1 + 1)) ” &&
  “ ((c0 + (c1 + 1)) <= n_pre) ” &&
  “ ((-1) <= (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int))) ” &&
  “ ((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top - 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top - 1))) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks_2)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top - 1)) (ks_2)) (Znth (top - 1) ks (0 : Int)) (Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int)) c0 (c1 + 1)) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs_2 ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs_2 ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks_2))

noncomputable def solver_entail_wit_10_1 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs_2 : (List Int), EX ws_2 : (List Int), EX ts_2 : (List Int), EX ns : (List Int), EX hs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((0 : Int) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ (1 <= (Znth e ts (0 : Int))) ” &&
  “ ((Znth e ts (0 : Int)) <= n_pre) ” &&
  “ ((0 : Int) <= (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) ” &&
  “ ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))) <= 1) ” &&
  “ (Spec n_pre comments (-1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  TT && emp 
|--
  “ (Spec n_pre comments (-1)) ” &&
  “ ((Z.lxor (0 : Int) (Znth e ws (0 : Int))) <= 1) ” &&
  “ ((0 : Int) <= (Z.lxor (0 : Int) (Znth e ws (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_1_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  (Spec n_pre comments (-1))

noncomputable def solver_entail_wit_10_1_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  ((Z.lxor (0 : Int) (Znth e ws (0 : Int))) <= 1)

noncomputable def solver_entail_wit_10_1_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  ((0 : Int) <= (Z.lxor (0 : Int) (Znth e ws (0 : Int))))

noncomputable def solver_entail_wit_10_2 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs_2 : (List Int), EX ws_2 : (List Int), EX ts_2 : (List Int), EX ns : (List Int), EX hs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((0 : Int) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ (1 <= (Znth e ts (0 : Int))) ” &&
  “ ((Znth e ts (0 : Int)) <= n_pre) ” &&
  “ ((0 : Int) <= (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) ” &&
  “ ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))) <= 1) ” &&
  “ (Spec n_pre comments (-1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  TT && emp 
|--
  “ (Spec n_pre comments (-1)) ” &&
  “ ((Z.lxor 1 (Znth e ws (0 : Int))) <= 1) ” &&
  “ ((0 : Int) <= (Z.lxor 1 (Znth e ws (0 : Int)))) ”
  &&  emp
)

noncomputable def solver_entail_wit_10_2_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  (Spec n_pre comments (-1))

noncomputable def solver_entail_wit_10_2_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  ((Z.lxor 1 (Znth e ws (0 : Int))) <= 1)

noncomputable def solver_entail_wit_10_2_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished : (List Int)) (before : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) ≠ (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before cs finished (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts ws)) ,
  ((0 : Int) <= (Z.lxor 1 (Znth e ws (0 : Int))))

noncomputable def solver_entail_wit_11_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs_2 (0 : Int)) = (0 : Int))) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before_2)) = (n_pre + 1))) (PreH30 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before_2)) (PreH32 : (ParityRespected comments before_2)) (PreH33 : (ColouredClosed comments before_2)) (PreH34 : (MaxImpostersOn n_pre comments before_2 total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH37 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts_2 (0 : Int))) (ks_2)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts_2 (0 : Int))) ((Z.lxor (Znth u cs_2 (0 : Int)) (Znth e ws_2 (0 : Int)))) (cs_2)))
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
|--
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top + 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top + 1))) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top + 1)) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))
  ||
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top + 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top + 1))) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top + 1)) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))

noncomputable def solver_entail_wit_11_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs_2 (0 : Int)) = 1)) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before_2)) = (n_pre + 1))) (PreH30 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before_2)) (PreH32 : (ParityRespected comments before_2)) (PreH33 : (ColouredClosed comments before_2)) (PreH34 : (MaxImpostersOn n_pre comments before_2 total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH37 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts_2 (0 : Int))) (ks_2)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts_2 (0 : Int))) ((Z.lxor (Znth u cs_2 (0 : Int)) (Znth e ws_2 (0 : Int)))) (cs_2)))
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
|--
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top + 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top + 1))) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top + 1)) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))
  ||
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= (top + 1)) ” &&
  “ ((top + 1) <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> ((top + 1) < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (top + 1))) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) ((top + 1)) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))

noncomputable def solver_entail_wit_11_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) = (Z.lxor (Znth u cs_2 (0 : Int)) (Znth e ws_2 (0 : Int))))) (PreH2 : ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs_2 (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before_2)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before_2)) (PreH33 : (ParityRespected comments before_2)) (PreH34 : (ColouredClosed comments before_2)) (PreH35 : (MaxImpostersOn n_pre comments before_2 total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH38 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))
  ||
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))

noncomputable def solver_entail_wit_11_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) = (Z.lxor (Znth u cs_2 (0 : Int)) (Znth e ws_2 (0 : Int))))) (PreH2 : ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs_2 (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before_2)) = (n_pre + 1))) (PreH31 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before_2)) (PreH33 : (ParityRespected comments before_2)) (PreH34 : (ColouredClosed comments before_2)) (PreH35 : (MaxImpostersOn n_pre comments before_2 total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH38 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))
  ||
  (EX hs : (List Int), EX finished : (List Int), EX before : (List Int), EX ks : (List Int), EX ns : (List Int), EX ws : (List Int), EX ts : (List Int), EX cs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= (Znth e ns_2 (0 : Int))) ” &&
  “ ((Znth e ns_2 (0 : Int)) < (2 * m_pre)) ” &&
  “ (((Znth e ns_2 (0 : Int)) ≠ (-1)) -> (((((1 <= (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) <= n_pre)) ∧ (((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = (0 : Int)) ∨ ((Znth (Znth e ns_2 (0 : Int)) ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)))) ∧ ((Znth (Znth e ns_2 (0 : Int)) ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ ((((Znth e ns_2 (0 : Int)) ≠ (-1)) ∧ ((Znth (Znth (Znth e ns_2 (0 : Int)) ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u (Znth e ns_2 (0 : Int)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks))

noncomputable def solver_entail_wit_12_1 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 (0 : Int))) ∧ ((Znth j_2 ks_2 (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before_2)) (PreH31 : (ParityRespected comments before_2)) (PreH32 : (ColouredClosed comments before_2)) (PreH33 : (MaxImpostersOn n_pre comments before_2 total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH36 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int), EX finished : (List Int), EX cs : (List Int), EX before : (List Int), EX ks : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 (0 : Int))) ∧ ((Znth j_2 ks_2 (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before_2)) (PreH31 : (ParityRespected comments before_2)) (PreH32 : (ColouredClosed comments before_2)) (PreH33 : (MaxImpostersOn n_pre comments before_2 total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH36 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  TT && emp 
|--
  EX finished : (List Int), EX before : (List Int),
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs_2 finished (sublist ((0 : Int)) (top) (ks_2)) c0 c1) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_2 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 (0 : Int))) ∧ ((Znth j_2 ks_2 (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before_2)) (PreH31 : (ParityRespected comments before_2)) (PreH32 : (ColouredClosed comments before_2)) (PreH33 : (MaxImpostersOn n_pre comments before_2 total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH36 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int), EX finished : (List Int), EX cs : (List Int), EX before : (List Int), EX ks : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (finished_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (ns_2 : (List Int)) (ws_2 : (List Int)) (ts_2 : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs_2 : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e = (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs_2 (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts_2 (0 : Int))) ∧ ((Znth e ts_2 (0 : Int)) <= n_pre)) ∧ (((Znth e ws_2 (0 : Int)) = (0 : Int)) ∨ ((Znth e ws_2 (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns_2 (0 : Int)))) ∧ ((Znth e ns_2 (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts_2 (0 : Int)) cs_2 (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < top)) -> ((1 <= (Znth j_2 ks_2 (0 : Int))) ∧ ((Znth j_2 ks_2 (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before_2)) = (n_pre + 1))) (PreH29 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before_2)) (PreH31 : (ParityRespected comments before_2)) (PreH32 : (ColouredClosed comments before_2)) (PreH33 : (MaxImpostersOn n_pre comments before_2 total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before_2 (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH36 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns_2 before_2 cs_2 finished_2 (sublist ((0 : Int)) (top) (ks_2)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  TT && emp 
|--
  EX finished : (List Int), EX before : (List Int),
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs_2 finished (sublist ((0 : Int)) (top) (ks_2)) c0 c1) ”
  &&  emp
)

noncomputable def solver_entail_wit_13 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (finished : (List Int)) (cs_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : ((0 : Int) <= top)) (PreH15 : (top <= n_pre)) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH20 : ((Zlength (before_2)) = (n_pre + 1))) (PreH21 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH22 : (ColourValues n_pre before_2)) (PreH23 : (ParityRespected comments before_2)) (PreH24 : (ColouredClosed comments before_2)) (PreH25 : (MaxImpostersOn n_pre comments before_2 total)) (PreH26 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before_2 (0 : Int)) ≠ (-1)))) (PreH27 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH28 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished (sublist ((0 : Int)) (top) (ks_2)) c0 c1)) (PreH30 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH31 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH32 : (top = (0 : Int))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int), EX vertices : (List Int), EX cs : (List Int), EX ks : (List Int), EX before : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (top = (0 : Int)) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentCompleteStrong n_pre comments before cs vertices c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (finished : (List Int)) (cs_2 : (List Int)) (before_2 : (List Int)) (ks_2 : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : ((0 : Int) <= top)) (PreH15 : (top <= n_pre)) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks_2 (0 : Int))) ∧ ((Znth j ks_2 (0 : Int)) <= n_pre)))) (PreH20 : ((Zlength (before_2)) = (n_pre + 1))) (PreH21 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH22 : (ColourValues n_pre before_2)) (PreH23 : (ParityRespected comments before_2)) (PreH24 : (ColouredClosed comments before_2)) (PreH25 : (MaxImpostersOn n_pre comments before_2 total)) (PreH26 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before_2 (0 : Int)) ≠ (-1)))) (PreH27 : ((Znth s before_2 (0 : Int)) = (-1))) (PreH28 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before_2 cs_2 finished (sublist ((0 : Int)) (top) (ks_2)) c0 c1)) (PreH30 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH31 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH32 : (top = (0 : Int))) ,
  TT && emp 
|--
  EX vertices : (List Int), EX before : (List Int),
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1) ”
  &&  emp
)

noncomputable def solver_entail_wit_14_1 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= (s + 1)) ” &&
  “ ((s + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (total + c0)) ” &&
  “ ((total + c0) <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs (total + c0)) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  TT && emp 
|--
  “ forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs_2 (0 : Int)) ≠ (-1))) ” &&
  “ (MaxImpostersOn n_pre comments cs_2 (total + c0)) ” &&
  “ (ColouredClosed comments cs_2) ” &&
  “ (ParityRespected comments cs_2) ” &&
  “ (ColourValues n_pre cs_2) ” &&
  “ ((total + c0) <= n_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_14_1_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))

noncomputable def solver_entail_wit_14_1_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (MaxImpostersOn n_pre comments cs_2 (total + c0))

noncomputable def solver_entail_wit_14_1_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (ColouredClosed comments cs_2)

noncomputable def solver_entail_wit_14_1_split_goal_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (ParityRespected comments cs_2)

noncomputable def solver_entail_wit_14_1_split_goal_5 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (ColourValues n_pre cs_2)

noncomputable def solver_entail_wit_14_1_split_goal_6 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  ((total + c0) <= n_pre)

noncomputable def solver_entail_wit_14_1_split_goal_7 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 > c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))

noncomputable def solver_entail_wit_14_2 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= (s + 1)) ” &&
  “ ((s + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (total + c1)) ” &&
  “ ((total + c1) <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs (total + c1)) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  TT && emp 
|--
  “ forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs_2 (0 : Int)) ≠ (-1))) ” &&
  “ (MaxImpostersOn n_pre comments cs_2 (total + c1)) ” &&
  “ (ColouredClosed comments cs_2) ” &&
  “ (ParityRespected comments cs_2) ” &&
  “ (ColourValues n_pre cs_2) ” &&
  “ ((total + c1) <= n_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_14_2_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))

noncomputable def solver_entail_wit_14_2_split_goal_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (MaxImpostersOn n_pre comments cs_2 (total + c1))

noncomputable def solver_entail_wit_14_2_split_goal_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (ColouredClosed comments cs_2)

noncomputable def solver_entail_wit_14_2_split_goal_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (ParityRespected comments cs_2)

noncomputable def solver_entail_wit_14_2_split_goal_5 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  (ColourValues n_pre cs_2)

noncomputable def solver_entail_wit_14_2_split_goal_6 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  ((total + c1) <= n_pre)

noncomputable def solver_entail_wit_14_2_split_goal_7 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (before : (List Int)) (cs_2 : (List Int)) (ks_2 : (List Int)) (vertices : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (c0 <= c1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q_2 : Int) , ((((0 : Int) <= q_2) ∧ (q_2 < m_pre)) -> (((((((((1 <= (Znth q_2 comment_sources (0 : Int))) ∧ ((Znth q_2 comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q_2 comment_targets (0 : Int)))) ∧ ((Znth q_2 comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q_2 comment_sources (0 : Int)) ≠ (Znth q_2 comment_targets (0 : Int)))) ∧ (((Znth q_2 comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q_2 comment_kinds (0 : Int)) = 1))) ∧ ((Znth q_2 comment_sources (0 : Int)) = (fst ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_targets (0 : Int)) = (snd ((fst ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q_2 comment_kinds (0 : Int)) = (snd ((Znth q_2 comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (top = (0 : Int))) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : ((Zlength (before)) = (n_pre + 1))) (PreH20 : ((Zlength (ks_2)) = (n_pre + 1))) (PreH21 : (ColourValues n_pre before)) (PreH22 : (ParityRespected comments before)) (PreH23 : (ColouredClosed comments before)) (PreH24 : (MaxImpostersOn n_pre comments before total)) (PreH25 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH26 : ((Znth s before (0 : Int)) = (-1))) (PreH27 : ((Znth s cs_2 (0 : Int)) ≠ (-1))) (PreH28 : (ComponentCompleteStrong n_pre comments before cs_2 vertices c0 c1)) (PreH29 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH30 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) ,
  forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))

noncomputable def solver_entail_wit_14_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs_2 (0 : Int)) >= (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH18 : (ColourValues n_pre cs_2)) (PreH19 : (ParityRespected comments cs_2)) (PreH20 : (ColouredClosed comments cs_2)) (PreH21 : (MaxImpostersOn n_pre comments cs_2 total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX hs : (List Int), EX ns : (List Int), EX ts : (List Int), EX ws : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= (s + 1)) ” &&
  “ ((s + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < (s + 1))) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_entail_wit_15 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (s > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1))) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH16 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH17 : (ColourValues n_pre cs_2)) (PreH18 : (ParityRespected comments cs_2)) (PreH19 : (ColouredClosed comments cs_2)) (PreH20 : (MaxImpostersOn n_pre comments cs_2 total)) (PreH21 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))) (PreH22 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs_2)
  ** (intArray.full nxt_pre (2 * m_pre) ns_2)
  ** (intArray.full to_pre (2 * m_pre) ts_2)
  ** (intArray.full wt_pre (2 * m_pre) ws_2)
  ** (intArray.full color_pre (n_pre + 1) cs_2)
  ** (intArray.full stack__pre (n_pre + 1) ks_2)
|--
  EX ks : (List Int), EX cs : (List Int), EX ws : (List Int), EX ts : (List Int), EX ns : (List Int), EX hs : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (Spec n_pre comments total) ”
  &&  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (s > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1))) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH16 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH17 : (ColourValues n_pre cs_2)) (PreH18 : (ParityRespected comments cs_2)) (PreH19 : (ColouredClosed comments cs_2)) (PreH20 : (MaxImpostersOn n_pre comments cs_2 total)) (PreH21 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))) (PreH22 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  TT && emp 
|--
  “ (Spec n_pre comments total) ”
  &&  emp
)

noncomputable def solver_entail_wit_15_split_goal_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (ks_2 : (List Int)) (cs_2 : (List Int)) (hs_2 : (List Int)) (ns_2 : (List Int)) (ts_2 : (List Int)) (ws_2 : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (s > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1))) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs_2 ns_2 ts_2 ws_2 comments)) (PreH16 : (ForwardStarRanges n_pre m_pre hs_2 ns_2 ts_2 ws_2)) (PreH17 : (ColourValues n_pre cs_2)) (PreH18 : (ParityRespected comments cs_2)) (PreH19 : (ColouredClosed comments cs_2)) (PreH20 : (MaxImpostersOn n_pre comments cs_2 total)) (PreH21 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs_2 (0 : Int)) ≠ (-1)))) (PreH22 : ((Zlength (ks_2)) = (n_pre + 1))) ,
  (Spec n_pre comments total)

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= n_pre)) (PreH8 : (Spec n_pre comments total)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (Spec n_pre comments total) ”
  &&  (intArray.full_shape comment_u_pre m_pre)
  ** (intArray.full_shape comment_v_pre m_pre)
  ** (intArray.full_shape comment_diff_pre m_pre)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= n_pre)) (PreH8 : (Spec n_pre comments total)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  (intArray.full_shape comment_u_pre m_pre)
  ** (intArray.full_shape comment_v_pre m_pre)
  ** (intArray.full_shape comment_diff_pre m_pre)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
)

noncomputable def solver_return_wit_1_split_goal_spatial : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (total : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((0 : Int) <= total)) (PreH7 : (total <= n_pre)) (PreH8 : (Spec n_pre comments total)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  (intArray.full_shape comment_u_pre m_pre)
  ** (intArray.full_shape comment_v_pre m_pre)
  ** (intArray.full_shape comment_diff_pre m_pre)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (e : Int) (u : Int) (v : Int) (want : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= n_pre)) (PreH12 : ((0 : Int) <= c0)) (PreH13 : ((0 : Int) <= c1)) (PreH14 : ((c0 + c1) <= n_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e < (2 * m_pre))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((0 : Int) <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (Spec n_pre comments (-1)) ”
  &&  (intArray.full_shape comment_u_pre m_pre)
  ** (intArray.full_shape comment_v_pre m_pre)
  ** (intArray.full_shape comment_diff_pre m_pre)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
) \/
(
forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (e : Int) (u : Int) (v : Int) (want : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= n_pre)) (PreH12 : ((0 : Int) <= c0)) (PreH13 : ((0 : Int) <= c1)) (PreH14 : ((c0 + c1) <= n_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e < (2 * m_pre))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((0 : Int) <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  (intArray.full_shape comment_u_pre m_pre)
  ** (intArray.full_shape comment_v_pre m_pre)
  ** (intArray.full_shape comment_diff_pre m_pre)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))
)

noncomputable def solver_return_wit_2_split_goal_spatial : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (cs : (List Int)) (ks : (List Int)) (s : Int) (total : Int) (top : Int) (c0 : Int) (c1 : Int) (e : Int) (u : Int) (v : Int) (want : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : (1 <= s)) (PreH7 : (s <= n_pre)) (PreH8 : ((0 : Int) <= total)) (PreH9 : (total <= n_pre)) (PreH10 : ((0 : Int) <= top)) (PreH11 : (top <= n_pre)) (PreH12 : ((0 : Int) <= c0)) (PreH13 : ((0 : Int) <= c1)) (PreH14 : ((c0 + c1) <= n_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e < (2 * m_pre))) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : (1 <= v)) (PreH20 : (v <= n_pre)) (PreH21 : ((0 : Int) <= want)) (PreH22 : (want <= 1)) (PreH23 : (Spec n_pre comments (-1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  (intArray.full_shape comment_u_pre m_pre)
  ** (intArray.full_shape comment_v_pre m_pre)
  ** (intArray.full_shape comment_diff_pre m_pre)
  ** (intArray.full_shape head_pre (n_pre + 1))
  ** (intArray.full_shape nxt_pre (2 * m_pre))
  ** (intArray.full_shape to_pre (2 * m_pre))
  ** (intArray.full_shape wt_pre (2 * m_pre))
  ** (intArray.full_shape color_pre (n_pre + 1))
  ** (intArray.full_shape stack__pre (n_pre + 1))

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (ws : (List Int)) (ts : (List Int)) (ns : (List Int)) (hs : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : ((Zlength (hs)) = (n_pre + 1))) (PreH14 : ((Zlength (ns)) = (2 * m_pre))) (PreH15 : ((Zlength (ts)) = (2 * m_pre))) (PreH16 : ((Zlength (ws)) = (2 * m_pre))) (PreH17 : ((Zlength (cs)) = (n_pre + 1))) (PreH18 : ((Zlength (ks)) = (n_pre + 1))) (PreH19 : (HeadsInitialised hs v)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (v <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < m_pre)) -> (((((((((1 <= (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ (1 <= (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) <= n_pre)) ∧ ((fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))) ≠ (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ (((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = (0 : Int)) ∨ ((snd ((Znth i comments __default__Prod__Prod_Z_Z_Z))) = 1))) ∧ ((Znth i comment_sources (0 : Int)) = (fst ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_targets (0 : Int)) = (snd ((fst ((Znth i comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth i comment_kinds (0 : Int)) = (snd ((Znth i comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= v) ” &&
  “ (v <= (n_pre + 1)) ” &&
  “ ((Zlength (hs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ns)) = (2 * m_pre)) ” &&
  “ ((Zlength (ts)) = (2 * m_pre)) ” &&
  “ ((Zlength (ws)) = (2 * m_pre)) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (HeadsInitialised hs v) ”
  &&  (((head_pre + (v * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i head_pre v (0 : Int) (n_pre + 1) hs)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((comment_v_pre + (i * sizeof(INT)))) # Int |-> ((Znth i comment_targets (0 : Int))))
  ** (intArray.missing_i comment_v_pre i (0 : Int) m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((comment_u_pre + (i * sizeof(INT)))) # Int |-> ((Znth i comment_sources (0 : Int))))
  ** (intArray.missing_i comment_u_pre i (0 : Int) m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((to_pre + ((2 * i) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i to_pre (2 * i) (0 : Int) (2 * m_pre) ts)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((comment_diff_pre + (i * sizeof(INT)))) # Int |-> ((Znth i comment_kinds (0 : Int))))
  ** (intArray.missing_i comment_diff_pre i (0 : Int) m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((wt_pre + ((2 * i) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i wt_pre (2 * i) (0 : Int) (2 * m_pre) ws)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_7 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((head_pre + ((Znth i comment_sources (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))))
  ** (intArray.missing_i head_pre (Znth i comment_sources (0 : Int)) (0 : Int) (n_pre + 1) hs)
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_8 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((nxt_pre + ((2 * i) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nxt_pre (2 * i) (0 : Int) (2 * m_pre) ns)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_9 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((head_pre + ((Znth i comment_sources (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i head_pre (Znth i comment_sources (0 : Int)) (0 : Int) (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_10 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((to_pre + (((2 * i) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i to_pre ((2 * i) + 1) (0 : Int) (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_11 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((comment_diff_pre + (i * sizeof(INT)))) # Int |-> ((Znth i comment_kinds (0 : Int))))
  ** (intArray.missing_i comment_diff_pre i (0 : Int) m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_12 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((wt_pre + (((2 * i) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i wt_pre ((2 * i) + 1) (0 : Int) (2 * m_pre) (replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_13 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((head_pre + ((Znth i comment_targets (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)) (0 : Int))))
  ** (intArray.missing_i head_pre (Znth i comment_targets (0 : Int)) (0 : Int) (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_14 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((nxt_pre + (((2 * i) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i nxt_pre ((2 * i) + 1) (0 : Int) (2 * m_pre) (replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_15 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (i : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (i < m_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= m_pre)) (PreH13 : ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1))))) (PreH14 : (ForwardStar n_pre m_pre i hs ns ts ws comments)) (PreH15 : (ForwardStarRanges n_pre i hs ns ts ws)) (PreH16 : ((Zlength (cs)) = (n_pre + 1))) (PreH17 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full nxt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))))
  ** (intArray.full head_pre (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (i < m_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= m_pre) ” &&
  “ ((i < m_pre) -> (((((1 <= (Znth i comment_sources (0 : Int))) ∧ ((Znth i comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth i comment_targets (0 : Int)))) ∧ ((Znth i comment_targets (0 : Int)) <= n_pre)) ∧ (((Znth i comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth i comment_kinds (0 : Int)) = 1)))) ” &&
  “ (ForwardStar n_pre m_pre i hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre i hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((head_pre + ((Znth i comment_targets (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i head_pre (Znth i comment_targets (0 : Int)) (0 : Int) (n_pre + 1) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)))
  ** (intArray.full nxt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth (Znth i comment_targets (0 : Int)) (replace_Znth ((Znth i comment_sources (0 : Int))) ((2 * i)) (hs)) (0 : Int))) ((replace_Znth ((2 * i)) ((Znth (Znth i comment_sources (0 : Int)) hs (0 : Int))) (ns)))))
  ** (intArray.full wt_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_kinds (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_kinds (0 : Int))) (ws)))))
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full to_pre (2 * m_pre) (replace_Znth (((2 * i) + 1)) ((Znth i comment_sources (0 : Int))) ((replace_Znth ((2 * i)) ((Znth i comment_targets (0 : Int))) (ts)))))
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_16 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (v : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (v <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= v)) (PreH12 : (v <= (n_pre + 1))) (PreH13 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH14 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH15 : ((Zlength (cs)) = (n_pre + 1))) (PreH16 : ((Zlength (ks)) = (n_pre + 1))) (PreH17 : (ColoursInitialised cs v)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (v <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= v) ” &&
  “ (v <= (n_pre + 1)) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ ((Zlength (cs)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColoursInitialised cs v) ”
  &&  (((color_pre + (v * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i color_pre v (0 : Int) (n_pre + 1) cs)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_17 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (s <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= (n_pre + 1))) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH16 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH17 : (ColourValues n_pre cs)) (PreH18 : (ParityRespected comments cs)) (PreH19 : (ColouredClosed comments cs)) (PreH20 : (MaxImpostersOn n_pre comments cs total)) (PreH21 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (s <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((color_pre + (s * sizeof(INT)))) # Int |-> ((Znth s cs (0 : Int))))
  ** (intArray.missing_i color_pre s (0 : Int) (n_pre + 1) cs)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_18 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth s cs (0 : Int)) < (0 : Int)) ” &&
  “ (s <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((color_pre + (s * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i color_pre s (0 : Int) (n_pre + 1) cs)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_19 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (ks : (List Int)) (cs : (List Int)) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth s cs (0 : Int)) < (0 : Int))) (PreH2 : (s <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= (n_pre + 1))) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH17 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH18 : (ColourValues n_pre cs)) (PreH19 : (ParityRespected comments cs)) (PreH20 : (ColouredClosed comments cs)) (PreH21 : (MaxImpostersOn n_pre comments cs total)) (PreH22 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1)))) (PreH23 : ((Zlength (ks)) = (n_pre + 1))) ,
  (intArray.full color_pre (n_pre + 1) (replace_Znth (s) ((0 : Int)) (cs)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth s cs (0 : Int)) < (0 : Int)) ” &&
  “ (s <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (ColourValues n_pre cs) ” &&
  “ (ParityRespected comments cs) ” &&
  “ (ColouredClosed comments cs) ” &&
  “ (MaxImpostersOn n_pre comments cs total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v cs (0 : Int)) ≠ (-1))) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ”
  &&  (((stack__pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i stack__pre (0 : Int) (0 : Int) (n_pre + 1) ks)
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth (s) ((0 : Int)) (cs)))
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)

noncomputable def solver_partial_solve_wit_20 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : ((0 : Int) <= top)) (PreH15 : (top <= n_pre)) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1))) (PreH21 : ((Zlength (ks)) = (n_pre + 1))) (PreH22 : (ColourValues n_pre before)) (PreH23 : (ParityRespected comments before)) (PreH24 : (ColouredClosed comments before)) (PreH25 : (MaxImpostersOn n_pre comments before total)) (PreH26 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH27 : ((Znth s before (0 : Int)) = (-1))) (PreH28 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH32 : (top ≠ (0 : Int))) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (top ≠ (0 : Int)) ”
  &&  (((stack__pre + ((top - 1) * sizeof(INT)))) # Int |-> ((Znth (top - 1) ks (0 : Int))))
  ** (intArray.missing_i stack__pre (top - 1) (0 : Int) (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)

noncomputable def solver_partial_solve_wit_21 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (m_pre <= 500000)) (PreH5 : (m_pre = (Zlength (comments)))) (PreH6 : ((Zlength (comment_sources)) = m_pre)) (PreH7 : ((Zlength (comment_targets)) = m_pre)) (PreH8 : ((Zlength (comment_kinds)) = m_pre)) (PreH9 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH10 : (1 <= s)) (PreH11 : (s <= n_pre)) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= n_pre)) (PreH14 : ((0 : Int) <= top)) (PreH15 : (top <= n_pre)) (PreH16 : ((0 : Int) <= c0)) (PreH17 : ((0 : Int) <= c1)) (PreH18 : ((c0 + c1) <= n_pre)) (PreH19 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH20 : ((Zlength (before)) = (n_pre + 1))) (PreH21 : ((Zlength (ks)) = (n_pre + 1))) (PreH22 : (ColourValues n_pre before)) (PreH23 : (ParityRespected comments before)) (PreH24 : (ColouredClosed comments before)) (PreH25 : (MaxImpostersOn n_pre comments before total)) (PreH26 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH27 : ((Znth s before (0 : Int)) = (-1))) (PreH28 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH29 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH30 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH31 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH32 : (top ≠ (0 : Int))) ,
  (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
|--
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (top ≠ (0 : Int)) ”
  &&  (((color_pre + ((Znth (top - 1) ks (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int))))
  ** (intArray.missing_i color_pre (Znth (top - 1) ks (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)

noncomputable def solver_partial_solve_wit_22 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : ((0 : Int) <= top)) (PreH16 : (top <= n_pre)) (PreH17 : ((0 : Int) <= c0)) (PreH18 : ((0 : Int) <= c1)) (PreH19 : ((c0 + c1) <= n_pre)) (PreH20 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) (PreH23 : (ColourValues n_pre before)) (PreH24 : (ParityRespected comments before)) (PreH25 : (ColouredClosed comments before)) (PreH26 : (MaxImpostersOn n_pre comments before total)) (PreH27 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH28 : ((Znth s before (0 : Int)) = (-1))) (PreH29 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH33 : (top ≠ (0 : Int))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) = (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (top ≠ (0 : Int)) ”
  &&  (((head_pre + ((Znth (top - 1) ks (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int))))
  ** (intArray.missing_i head_pre (Znth (top - 1) ks (0 : Int)) (0 : Int) (n_pre + 1) hs)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)

noncomputable def solver_partial_solve_wit_23 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (ns : (List Int)) (ts : (List Int)) (ws : (List Int)) (finished : (List Int)) (cs : (List Int)) (before : (List Int)) (ks : (List Int)) (c1 : Int) (c0 : Int) (top : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) ≠ (0 : Int))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : ((0 : Int) <= top)) (PreH16 : (top <= n_pre)) (PreH17 : ((0 : Int) <= c0)) (PreH18 : ((0 : Int) <= c1)) (PreH19 : ((c0 + c1) <= n_pre)) (PreH20 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH21 : ((Zlength (before)) = (n_pre + 1))) (PreH22 : ((Zlength (ks)) = (n_pre + 1))) (PreH23 : (ColourValues n_pre before)) (PreH24 : (ParityRespected comments before)) (PreH25 : (ColouredClosed comments before)) (PreH26 : (MaxImpostersOn n_pre comments before total)) (PreH27 : forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1)))) (PreH28 : ((Znth s before (0 : Int)) = (-1))) (PreH29 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH30 : (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1)) (PreH31 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH32 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) (PreH33 : (top ≠ (0 : Int))) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
|--
  “ ((Znth (Znth (top - 1) ks (0 : Int)) cs (0 : Int)) ≠ (0 : Int)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v : Int) , (((1 <= v) ∧ (v < s)) -> ((Znth v before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentFrontierStrong n_pre comments before cs finished (sublist ((0 : Int)) (top) (ks)) c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ” &&
  “ (top ≠ (0 : Int)) ”
  &&  (((head_pre + ((Znth (top - 1) ks (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth (top - 1) ks (0 : Int)) hs (0 : Int))))
  ** (intArray.missing_i head_pre (Znth (top - 1) ks (0 : Int)) (0 : Int) (n_pre + 1) hs)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)

noncomputable def solver_partial_solve_wit_24 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + (u * sizeof(INT)))) # Int |-> ((Znth u cs (0 : Int))))
  ** (intArray.missing_i color_pre u (0 : Int) (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_25 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((wt_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ws (0 : Int))))
  ** (intArray.missing_i wt_pre e (0 : Int) (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_26 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + (u * sizeof(INT)))) # Int |-> ((Znth u cs (0 : Int))))
  ** (intArray.missing_i color_pre u (0 : Int) (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_27 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((wt_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ws (0 : Int))))
  ** (intArray.missing_i wt_pre e (0 : Int) (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_28 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((to_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ts (0 : Int))))
  ** (intArray.missing_i to_pre e (0 : Int) (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_29 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((to_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ts (0 : Int))))
  ** (intArray.missing_i to_pre e (0 : Int) (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_30 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + ((Znth e ts (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth e ts (0 : Int)) cs (0 : Int))))
  ** (intArray.missing_i color_pre (Znth e ts (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_31 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : (e ≠ (-1))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (m_pre <= 500000)) (PreH6 : (m_pre = (Zlength (comments)))) (PreH7 : ((Zlength (comment_sources)) = m_pre)) (PreH8 : ((Zlength (comment_targets)) = m_pre)) (PreH9 : ((Zlength (comment_kinds)) = m_pre)) (PreH10 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH11 : (1 <= s)) (PreH12 : (s <= n_pre)) (PreH13 : ((0 : Int) <= total)) (PreH14 : (total <= n_pre)) (PreH15 : (1 <= u)) (PreH16 : (u <= n_pre)) (PreH17 : ((Znth u cs (0 : Int)) = 1)) (PreH18 : ((0 : Int) <= top)) (PreH19 : (top <= n_pre)) (PreH20 : ((0 : Int) <= c0)) (PreH21 : ((0 : Int) <= c1)) (PreH22 : ((c0 + c1) <= n_pre)) (PreH23 : ((-1) <= e)) (PreH24 : (e < (2 * m_pre))) (PreH25 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH26 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH27 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH28 : ((Zlength (before)) = (n_pre + 1))) (PreH29 : ((Zlength (ks)) = (n_pre + 1))) (PreH30 : (ColourValues n_pre before)) (PreH31 : (ParityRespected comments before)) (PreH32 : (ColouredClosed comments before)) (PreH33 : (MaxImpostersOn n_pre comments before total)) (PreH34 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH35 : ((Znth s before (0 : Int)) = (-1))) (PreH36 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH37 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH38 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH39 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + ((Znth e ts (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth e ts (0 : Int)) cs (0 : Int))))
  ** (intArray.missing_i color_pre (Znth e ts (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_32 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + ((Znth e ts (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i color_pre (Znth e ts (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_33 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = 1)) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + ((Znth e ts (0 : Int)) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i color_pre (Znth e ts (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_34 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((stack__pre + (top * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i stack__pre top (0 : Int) (n_pre + 1) ks)
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)

noncomputable def solver_partial_solve_wit_35 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = 1)) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((stack__pre + (top * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i stack__pre top (0 : Int) (n_pre + 1) ks)
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)

noncomputable def solver_partial_solve_wit_36 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + ((Znth e ts (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth e ts (0 : Int)) cs (0 : Int))))
  ** (intArray.missing_i color_pre (Znth e ts (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_37 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = 1)) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((color_pre + ((Znth e ts (0 : Int)) * sizeof(INT)))) # Int |-> ((Znth (Znth e ts (0 : Int)) cs (0 : Int))))
  ** (intArray.missing_i color_pre (Znth e ts (0 : Int)) (0 : Int) (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_38 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts (0 : Int))) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ns (0 : Int))))
  ** (intArray.missing_i nxt_pre e (0 : Int) (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts (0 : Int))) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)

noncomputable def solver_partial_solve_wit_39 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) (PreH2 : (e ≠ (-1))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (m_pre <= 500000)) (PreH7 : (m_pre = (Zlength (comments)))) (PreH8 : ((Zlength (comment_sources)) = m_pre)) (PreH9 : ((Zlength (comment_targets)) = m_pre)) (PreH10 : ((Zlength (comment_kinds)) = m_pre)) (PreH11 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH12 : (1 <= s)) (PreH13 : (s <= n_pre)) (PreH14 : ((0 : Int) <= total)) (PreH15 : (total <= n_pre)) (PreH16 : (1 <= u)) (PreH17 : (u <= n_pre)) (PreH18 : ((Znth u cs (0 : Int)) = 1)) (PreH19 : ((0 : Int) <= top)) (PreH20 : (top <= n_pre)) (PreH21 : ((0 : Int) <= c0)) (PreH22 : ((0 : Int) <= c1)) (PreH23 : ((c0 + c1) <= n_pre)) (PreH24 : ((-1) <= e)) (PreH25 : (e < (2 * m_pre))) (PreH26 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH27 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH28 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH29 : ((Zlength (before)) = (n_pre + 1))) (PreH30 : ((Zlength (ks)) = (n_pre + 1))) (PreH31 : (ColourValues n_pre before)) (PreH32 : (ParityRespected comments before)) (PreH33 : (ColouredClosed comments before)) (PreH34 : (MaxImpostersOn n_pre comments before total)) (PreH35 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH36 : ((Znth s before (0 : Int)) = (-1))) (PreH37 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH38 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH39 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH40 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts (0 : Int))) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ns (0 : Int))))
  ** (intArray.missing_i nxt_pre e (0 : Int) (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) (replace_Znth (top) ((Znth e ts (0 : Int))) (ks)))
  ** (intArray.full color_pre (n_pre + 1) (replace_Znth ((Znth e ts (0 : Int))) ((Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) (cs)))
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)

noncomputable def solver_partial_solve_wit_40 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) = (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = (0 : Int))) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) = (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) ” &&
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = (0 : Int)) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ns (0 : Int))))
  ** (intArray.missing_i nxt_pre e (0 : Int) (2 * m_pre) ns)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full stack__pre (n_pre + 1) ks)

noncomputable def solver_partial_solve_wit_41 : Prop :=
  forall (comment_kinds : (List Int)) (comment_targets : (List Int)) (comment_sources : (List Int)) (comments : (List ((Int × Int) × Int))) (n_pre : Int) (m_pre : Int) (comment_u_pre : Int) (comment_v_pre : Int) (comment_diff_pre : Int) (head_pre : Int) (nxt_pre : Int) (to_pre : Int) (wt_pre : Int) (color_pre : Int) (stack__pre : Int) (hs : (List Int)) (finished : (List Int)) (before : (List Int)) (ks : (List Int)) (ns : (List Int)) (ws : (List Int)) (ts : (List Int)) (e : Int) (c1 : Int) (c0 : Int) (top : Int) (cs : (List Int)) (u : Int) (total : Int) (s : Int) (__default__Prod__Prod_Z_Z_Z : _Prod__Prod_Z_Z_Z) (PreH1 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) = (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int))))) (PreH2 : ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int))) (PreH3 : (e ≠ (-1))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((0 : Int) <= m_pre)) (PreH7 : (m_pre <= 500000)) (PreH8 : (m_pre = (Zlength (comments)))) (PreH9 : ((Zlength (comment_sources)) = m_pre)) (PreH10 : ((Zlength (comment_targets)) = m_pre)) (PreH11 : ((Zlength (comment_kinds)) = m_pre)) (PreH12 : forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) (PreH13 : (1 <= s)) (PreH14 : (s <= n_pre)) (PreH15 : ((0 : Int) <= total)) (PreH16 : (total <= n_pre)) (PreH17 : (1 <= u)) (PreH18 : (u <= n_pre)) (PreH19 : ((Znth u cs (0 : Int)) = 1)) (PreH20 : ((0 : Int) <= top)) (PreH21 : (top <= n_pre)) (PreH22 : ((0 : Int) <= c0)) (PreH23 : ((0 : Int) <= c1)) (PreH24 : ((c0 + c1) <= n_pre)) (PreH25 : ((-1) <= e)) (PreH26 : (e < (2 * m_pre))) (PreH27 : ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre))))) (PreH28 : (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre))) (PreH29 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre)))) (PreH30 : ((Zlength (before)) = (n_pre + 1))) (PreH31 : ((Zlength (ks)) = (n_pre + 1))) (PreH32 : (ColourValues n_pre before)) (PreH33 : (ParityRespected comments before)) (PreH34 : (ColouredClosed comments before)) (PreH35 : (MaxImpostersOn n_pre comments before total)) (PreH36 : forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1)))) (PreH37 : ((Znth s before (0 : Int)) = (-1))) (PreH38 : ((Znth s cs (0 : Int)) ≠ (-1))) (PreH39 : (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1)) (PreH40 : (ForwardStar n_pre m_pre m_pre hs ns ts ws comments)) (PreH41 : (ForwardStarRanges n_pre m_pre hs ns ts ws)) ,
  (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full nxt_pre (2 * m_pre) ns)
  ** (intArray.full stack__pre (n_pre + 1) ks)
|--
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) = (Z.lxor (Znth u cs (0 : Int)) (Znth e ws (0 : Int)))) ” &&
  “ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) >= (0 : Int)) ” &&
  “ (e ≠ (-1)) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (m_pre <= 500000) ” &&
  “ (m_pre = (Zlength (comments))) ” &&
  “ ((Zlength (comment_sources)) = m_pre) ” &&
  “ ((Zlength (comment_targets)) = m_pre) ” &&
  “ ((Zlength (comment_kinds)) = m_pre) ” &&
  “ forall (q : Int) , ((((0 : Int) <= q) ∧ (q < m_pre)) -> (((((((((1 <= (Znth q comment_sources (0 : Int))) ∧ ((Znth q comment_sources (0 : Int)) <= n_pre)) ∧ (1 <= (Znth q comment_targets (0 : Int)))) ∧ ((Znth q comment_targets (0 : Int)) <= n_pre)) ∧ ((Znth q comment_sources (0 : Int)) ≠ (Znth q comment_targets (0 : Int)))) ∧ (((Znth q comment_kinds (0 : Int)) = (0 : Int)) ∨ ((Znth q comment_kinds (0 : Int)) = 1))) ∧ ((Znth q comment_sources (0 : Int)) = (fst ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_targets (0 : Int)) = (snd ((fst ((Znth q comments __default__Prod__Prod_Z_Z_Z))))))) ∧ ((Znth q comment_kinds (0 : Int)) = (snd ((Znth q comments __default__Prod__Prod_Z_Z_Z)))))) ” &&
  “ (1 <= s) ” &&
  “ (s <= n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= n_pre) ” &&
  “ (1 <= u) ” &&
  “ (u <= n_pre) ” &&
  “ ((Znth u cs (0 : Int)) = 1) ” &&
  “ ((0 : Int) <= top) ” &&
  “ (top <= n_pre) ” &&
  “ ((0 : Int) <= c0) ” &&
  “ ((0 : Int) <= c1) ” &&
  “ ((c0 + c1) <= n_pre) ” &&
  “ ((-1) <= e) ” &&
  “ (e < (2 * m_pre)) ” &&
  “ ((e ≠ (-1)) -> (((((1 <= (Znth e ts (0 : Int))) ∧ ((Znth e ts (0 : Int)) <= n_pre)) ∧ (((Znth e ws (0 : Int)) = (0 : Int)) ∨ ((Znth e ws (0 : Int)) = 1))) ∧ ((-1) <= (Znth e ns (0 : Int)))) ∧ ((Znth e ns (0 : Int)) < (2 * m_pre)))) ” &&
  “ (((e ≠ (-1)) ∧ ((Znth (Znth e ts (0 : Int)) cs (0 : Int)) < (0 : Int))) -> (top < n_pre)) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < top)) -> ((1 <= (Znth j ks (0 : Int))) ∧ ((Znth j ks (0 : Int)) <= n_pre))) ” &&
  “ ((Zlength (before)) = (n_pre + 1)) ” &&
  “ ((Zlength (ks)) = (n_pre + 1)) ” &&
  “ (ColourValues n_pre before) ” &&
  “ (ParityRespected comments before) ” &&
  “ (ColouredClosed comments before) ” &&
  “ (MaxImpostersOn n_pre comments before total) ” &&
  “ forall (v0 : Int) , (((1 <= v0) ∧ (v0 < s)) -> ((Znth v0 before (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth s before (0 : Int)) = (-1)) ” &&
  “ ((Znth s cs (0 : Int)) ≠ (-1)) ” &&
  “ (ComponentScanStrong n_pre comments ns before cs finished (sublist ((0 : Int)) (top) (ks)) u e c0 c1) ” &&
  “ (ForwardStar n_pre m_pre m_pre hs ns ts ws comments) ” &&
  “ (ForwardStarRanges n_pre m_pre hs ns ts ws) ”
  &&  (((nxt_pre + (e * sizeof(INT)))) # Int |-> ((Znth e ns (0 : Int))))
  ** (intArray.missing_i nxt_pre e (0 : Int) (2 * m_pre) ns)
  ** (intArray.full color_pre (n_pre + 1) cs)
  ** (intArray.full wt_pre (2 * m_pre) ws)
  ** (intArray.full to_pre (2 * m_pre) ts)
  ** (intArray.full comment_u_pre m_pre comment_sources)
  ** (intArray.full comment_v_pre m_pre comment_targets)
  ** (intArray.full comment_diff_pre m_pre comment_kinds)
  ** (intArray.full head_pre (n_pre + 1) hs)
  ** (intArray.full stack__pre (n_pre + 1) ks)


structure VC_Correct : Type where
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_safety_wit_21 : solver_safety_wit_21
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_23 : solver_safety_wit_23
  proof_of_solver_safety_wit_24 : solver_safety_wit_24
  proof_of_solver_safety_wit_25 : solver_safety_wit_25
  proof_of_solver_safety_wit_26 : solver_safety_wit_26
  proof_of_solver_safety_wit_27 : solver_safety_wit_27
  proof_of_solver_safety_wit_28 : solver_safety_wit_28
  proof_of_solver_safety_wit_29 : solver_safety_wit_29
  proof_of_solver_safety_wit_30 : solver_safety_wit_30
  proof_of_solver_safety_wit_31 : solver_safety_wit_31
  proof_of_solver_safety_wit_32 : solver_safety_wit_32
  proof_of_solver_safety_wit_33 : solver_safety_wit_33
  proof_of_solver_safety_wit_34 : solver_safety_wit_34
  proof_of_solver_safety_wit_35 : solver_safety_wit_35
  proof_of_solver_safety_wit_36 : solver_safety_wit_36
  proof_of_solver_safety_wit_37 : solver_safety_wit_37
  proof_of_solver_safety_wit_38 : solver_safety_wit_38
  proof_of_solver_safety_wit_39 : solver_safety_wit_39
  proof_of_solver_safety_wit_40 : solver_safety_wit_40
  proof_of_solver_safety_wit_41 : solver_safety_wit_41
  proof_of_solver_safety_wit_42 : solver_safety_wit_42
  proof_of_solver_safety_wit_43 : solver_safety_wit_43
  proof_of_solver_safety_wit_44 : solver_safety_wit_44
  proof_of_solver_safety_wit_45 : solver_safety_wit_45
  proof_of_solver_safety_wit_46 : solver_safety_wit_46
  proof_of_solver_safety_wit_47 : solver_safety_wit_47
  proof_of_solver_entail_wit_14_3 : solver_entail_wit_14_3
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8
  proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9
  proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10
  proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11
  proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12
  proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13
  proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14
  proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15
  proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16
  proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17
  proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18
  proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19
  proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20
  proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21
  proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22
  proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23
  proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24
  proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25
  proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26
  proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27
  proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28
  proof_of_solver_partial_solve_wit_29 : solver_partial_solve_wit_29
  proof_of_solver_partial_solve_wit_30 : solver_partial_solve_wit_30
  proof_of_solver_partial_solve_wit_31 : solver_partial_solve_wit_31
  proof_of_solver_partial_solve_wit_32 : solver_partial_solve_wit_32
  proof_of_solver_partial_solve_wit_33 : solver_partial_solve_wit_33
  proof_of_solver_partial_solve_wit_34 : solver_partial_solve_wit_34
  proof_of_solver_partial_solve_wit_35 : solver_partial_solve_wit_35
  proof_of_solver_partial_solve_wit_36 : solver_partial_solve_wit_36
  proof_of_solver_partial_solve_wit_37 : solver_partial_solve_wit_37
  proof_of_solver_partial_solve_wit_38 : solver_partial_solve_wit_38
  proof_of_solver_partial_solve_wit_39 : solver_partial_solve_wit_39
  proof_of_solver_partial_solve_wit_40 : solver_partial_solve_wit_40
  proof_of_solver_partial_solve_wit_41 : solver_partial_solve_wit_41
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_entail_wit_8 : solver_entail_wit_8
  proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1
  proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2
  proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1
  proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2
  proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1
  proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2
  proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3
  proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4
  proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1
  proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2
  proof_of_solver_entail_wit_13 : solver_entail_wit_13
  proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1
  proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2
  proof_of_solver_entail_wit_15 : solver_entail_wit_15
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_return_wit_2 : solver_return_wit_2

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_goal
