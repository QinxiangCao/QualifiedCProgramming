import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_goal
import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_proof_auto
import SimpleC.EE.LLM_bench.Algorithms.decimal_digits.decimal_digits_lib

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open concatenating_numbers_dp_goal concatenating_numbers_dp_lib
open scoped SimpleC.SL.SAC CoqZ
local instance : SacContext := ⟨naive_C_Rules⟩
open SimpleC.EE.LLM_bench.Algorithms.decimal_digits
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev array2 := naive_C_Rules.IntArray2
-- Keep array assertions symbolic during spatial tactic matching.
attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full



private theorem cell_upper (count width row col : Int) (hw : 0≤width) (hr : row<count) (hc : col<width) :
    row*width+col<count*width := by
  have hm := Int.mul_le_mul_of_nonneg_right (show row+1≤count by omega) hw
  have he : (row+1)*width=row*width+width := by grind
  rw [he] at hm
  omega

private theorem shift_pow (x n : Int) (hn : 0≤n) : Z.shiftl x n=x*Z.pow 2 n := by
  cases n with
  | ofNat n => simp [Z.shiftl,Z.pow,Int.shiftLeft_eq']
  | negSucc n => omega

private theorem pow_nat (n : Int) (hn : 0≤n) : Z.pow 2 n=Int.ofNat (2^n.toNat) := by
  cases n with
  | ofNat n => simp [Z.pow]
  | negSucc n => omega

private theorem shift_small (first count : Int) (hf : 0≤first) (hlt : first<count) (hc : count≤20) :
    signed_last_nbits (Z.shiftl 1 first) 32=Z.shiftl 1 first ∧
    (0≤Z.shiftl 1 first ∧ Z.shiftl 1 first<Z.pow 2 count) := by
  have hc0 : 0≤count := by omega
  have hpow : Z.pow 2 first=Int.ofNat (2^first.toNat) := pow_nat first hf
  have hpowc : Z.pow 2 count=Int.ofNat (2^count.toNat) := pow_nat count hc0
  have hs : Z.shiftl 1 first=Z.pow 2 first := by rw [shift_pow 1 first hf,Int.one_mul]
  have hnat := Nat.pow_lt_pow_of_lt (a:=2) (by decide) (show first.toNat<count.toNat by omega)
  have hmax : (2^first.toNat:Nat)≤2^20 := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : -2147483648≤Z.shiftl 1 first ∧ Z.shiftl 1 first<2147483648 := by
    rw [hs,hpow]
    change (2^first.toNat:Nat)≤1048576 at hmax
    constructor
    · exact Int.le_trans (by decide : (-2147483648:Int)≤0) (Int.natCast_nonneg _)
    · exact Int.lt_of_le_of_lt (Int.ofNat_le.mpr hmax) (by decide)
  refine ⟨signed_last_nbits_eq _ 32 (by decide) hr,?_⟩
  rw [hs,hpow,hpowc]
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hnat⟩

theorem aux_compare_concatenated_order_safety_wit_1_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (naive_C_Rules.IntArray.full lengths_pre count lens)
  ** ((( &( "right_length" ) )) # Int |-> ((Znth right_pre lens (0 : Int))))
  ** ((( &( "left_length" ) )) # Int |-> ((Znth left_pre lens (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (naive_C_Rules.IntArray.full numbers_pre (count * number_width_pre) flat)
|--
  “ (((Znth left_pre lens (0 : Int)) + (Znth right_pre lens (0 : Int))) <= INT_MAX) ”) := by

  intro right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  dump_pre_spatial
  change _≤2147483647
  omega

theorem aux_compare_concatenated_order_safety_wit_1_split_goal_2 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (lengths_pre : Int) (numbers_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  ((( &( "total_length" ) )) # Int |->_)
  ** (naive_C_Rules.IntArray.full lengths_pre count lens)
  ** ((( &( "right_length" ) )) # Int |-> ((Znth right_pre lens (0 : Int))))
  ** ((( &( "left_length" ) )) # Int |-> ((Znth left_pre lens (0 : Int))))
  ** ((( &( "numbers" ) )) # Ptr |-> (numbers_pre))
  ** ((( &( "lengths" ) )) # Ptr |-> (lengths_pre))
  ** ((( &( "number_width" ) )) # Int |-> (number_width_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** (naive_C_Rules.IntArray.full numbers_pre (count * number_width_pre) flat)
|--
  “ ((INT_MIN) <= ((Znth left_pre lens (0 : Int)) + (Znth right_pre lens (0 : Int)))) ”) := by

  intro right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  dump_pre_spatial
  change (-2147483648:Int)≤_
  omega

theorem aux_compare_concatenated_order_entail_wit_1_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  (ConcatCompareLoopState rows lens left_pre right_pre (Znth left_pre lens (0 : Int)) (Znth right_pre lens (0 : Int)) (0 : Int))) := by

  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  exact ⟨rfl,rfl,ConcatComparePrefix_zero__compare_bounds rows lens left_pre right_pre⟩

theorem aux_compare_concatenated_order_entail_wit_1_split_goal_2 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  ((0 : Int) <= ((Znth left_pre lens (0 : Int)) + (Znth right_pre lens (0 : Int))))) := by

  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem aux_compare_concatenated_order_entail_wit_1_split_goal_5 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  ((Znth right_pre lens (0 : Int)) <= number_width_pre)) := by

  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem aux_compare_concatenated_order_entail_wit_1_split_goal_6 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  (1 <= (Znth right_pre lens (0 : Int)))) := by

  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem aux_compare_concatenated_order_entail_wit_1_split_goal_7 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  ((Znth left_pre lens (0 : Int)) <= number_width_pre)) := by

  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem aux_compare_concatenated_order_entail_wit_1_split_goal_8 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : ((0 : Int) <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : ((0 : Int) <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre)) (PreH10 : (FlatRows flat rows count number_width_pre)) ,
  (1 <= (Znth left_pre lens (0 : Int)))) := by

  intro right_pre left_pre number_width_pre count flat lens rows PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := PreH9.2.2 left_pre ⟨by omega,by omega⟩
  have hr := PreH9.2.2 right_pre ⟨by omega,by omega⟩
  omega

theorem aux_compare_concatenated_order_entail_wit_3_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (position : Int) (total_length : Int) (right_length : Int) (left_length : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : ((0 : Int) <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (right_length <= INT_MAX)) (PreH9 : (left_length <= INT_MAX)) (PreH10 : (right_pre <= INT_MAX)) (PreH11 : (left_pre <= INT_MAX)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < left_length)) (PreH18 : (position < total_length)) (PreH19 : (1 <= count)) (PreH20 : (count <= 20)) (PreH21 : (1 <= number_width_pre)) (PreH22 : (number_width_pre <= 10)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < count)) (PreH25 : ((0 : Int) <= right_pre)) (PreH26 : (right_pre < count)) (PreH27 : (1 <= left_length)) (PreH28 : (left_length <= number_width_pre)) (PreH29 : (1 <= right_length)) (PreH30 : (right_length <= number_width_pre)) (PreH31 : (total_length = (left_length + right_length))) (PreH32 : (2 <= total_length)) (PreH33 : (total_length <= (2 * number_width_pre))) (PreH34 : ((0 : Int) <= position)) (PreH35 : (position <= total_length)) (PreH36 : (RowsWellFormed rows lens count number_width_pre)) (PreH37 : (FlatRows flat rows count number_width_pre)) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  (((left_pre * number_width_pre) + position) < (count * number_width_pre))) := by

  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre left_pre position (by omega) (by omega) (by omega)
  omega

theorem aux_compare_concatenated_order_entail_wit_5_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (position : Int) (total_length : Int) (right_length : Int) (left_length : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (left_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (left_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : ((0 : Int) <= (position - left_length))) (PreH8 : ((position - left_length) < number_width_pre)) (PreH9 : (total_length <= INT_MAX)) (PreH10 : (right_length <= INT_MAX)) (PreH11 : (right_pre <= INT_MAX)) (PreH12 : (left_pre <= INT_MAX)) (PreH13 : (total_length >= INT_MIN)) (PreH14 : (right_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position >= left_length)) (PreH18 : (position < total_length)) (PreH19 : (1 <= count)) (PreH20 : (count <= 20)) (PreH21 : (1 <= number_width_pre)) (PreH22 : (number_width_pre <= 10)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < count)) (PreH25 : ((0 : Int) <= right_pre)) (PreH26 : (right_pre < count)) (PreH27 : (1 <= left_length)) (PreH28 : (left_length <= number_width_pre)) (PreH29 : (1 <= right_length)) (PreH30 : (right_length <= number_width_pre)) (PreH31 : (total_length = (left_length + right_length))) (PreH32 : (2 <= total_length)) (PreH33 : (total_length <= (2 * number_width_pre))) (PreH34 : ((0 : Int) <= position)) (PreH35 : (position <= total_length)) (PreH36 : (RowsWellFormed rows lens count number_width_pre)) (PreH37 : (FlatRows flat rows count number_width_pre)) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  ((((right_pre * number_width_pre) + position) - left_length) < (count * number_width_pre))) := by

  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre right_pre (position-left_length) (by omega) (by omega) (by omega)
  omega

theorem aux_compare_concatenated_order_entail_wit_8_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (left_length : Int) (right_length : Int) (total_length : Int) (position : Int) (left_then_right : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : ((0 : Int) <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (left_then_right <= INT_MAX)) (PreH8 : (total_length <= INT_MAX)) (PreH9 : (right_length <= INT_MAX)) (PreH10 : (left_length <= INT_MAX)) (PreH11 : (right_pre <= INT_MAX)) (PreH12 : (left_pre <= INT_MAX)) (PreH13 : (left_then_right >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (right_length >= INT_MIN)) (PreH16 : (left_length >= INT_MIN)) (PreH17 : (right_pre >= INT_MIN)) (PreH18 : (left_pre >= INT_MIN)) (PreH19 : (position < right_length)) (PreH20 : (1 <= count)) (PreH21 : (count <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : ((0 : Int) <= left_pre)) (PreH25 : (left_pre < count)) (PreH26 : ((0 : Int) <= right_pre)) (PreH27 : (right_pre < count)) (PreH28 : (1 <= left_length)) (PreH29 : (left_length <= number_width_pre)) (PreH30 : (1 <= right_length)) (PreH31 : (right_length <= number_width_pre)) (PreH32 : (total_length = (left_length + right_length))) (PreH33 : ((0 : Int) <= position)) (PreH34 : (position < total_length)) (PreH35 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH36 : (RowsWellFormed rows lens count number_width_pre)) (PreH37 : (FlatRows flat rows count number_width_pre)) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  (((right_pre * number_width_pre) + position) < (count * number_width_pre))) := by

  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre right_pre position (by omega) (by omega) (by omega)
  omega

theorem aux_compare_concatenated_order_entail_wit_10_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (left_length : Int) (right_length : Int) (total_length : Int) (position : Int) (left_then_right : Int) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (right_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (right_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : ((0 : Int) <= (position - right_length))) (PreH8 : ((position - right_length) < number_width_pre)) (PreH9 : (left_then_right <= INT_MAX)) (PreH10 : (total_length <= INT_MAX)) (PreH11 : (left_length <= INT_MAX)) (PreH12 : (right_pre <= INT_MAX)) (PreH13 : (left_pre <= INT_MAX)) (PreH14 : (left_then_right >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (left_length >= INT_MIN)) (PreH17 : (right_pre >= INT_MIN)) (PreH18 : (left_pre >= INT_MIN)) (PreH19 : (position >= right_length)) (PreH20 : (1 <= count)) (PreH21 : (count <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : ((0 : Int) <= left_pre)) (PreH25 : (left_pre < count)) (PreH26 : ((0 : Int) <= right_pre)) (PreH27 : (right_pre < count)) (PreH28 : (1 <= left_length)) (PreH29 : (left_length <= number_width_pre)) (PreH30 : (1 <= right_length)) (PreH31 : (right_length <= number_width_pre)) (PreH32 : (total_length = (left_length + right_length))) (PreH33 : ((0 : Int) <= position)) (PreH34 : (position < total_length)) (PreH35 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH36 : (RowsWellFormed rows lens count number_width_pre)) (PreH37 : (FlatRows flat rows count number_width_pre)) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  ((((left_pre * number_width_pre) + position) - right_length) < (count * number_width_pre))) := by

  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have h := cell_upper count number_width_pre left_pre (position-right_length) (by omega) (by omega) (by omega)
  omega

theorem aux_compare_concatenated_order_entail_wit_12_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (left_length : Int) (right_length : Int) (total_length : Int) (position : Int) (left_then_right : Int) (right_then_left : Int) (PreH1 : (left_then_right >= right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : ((0 : Int) <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length))) (PreH16 : ((0 : Int) <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre)) (PreH21 : (FlatRows flat rows count number_width_pre)) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length (position + 1))) := by

  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply concat_compare_prefix_step__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position
  all_goals first | assumption | omega

theorem aux_compare_concatenated_order_return_wit_1_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (position : Int) (total_length : Int) (right_length : Int) (left_length : Int) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : ((0 : Int) <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length))) (PreH15 : (2 <= total_length)) (PreH16 : (total_length <= (2 * number_width_pre))) (PreH17 : ((0 : Int) <= position)) (PreH18 : (position <= total_length)) (PreH19 : (RowsWellFormed rows lens count number_width_pre)) (PreH20 : (FlatRows flat rows count number_width_pre)) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  (ConcatCompareSignOutcome rows lens left_pre right_pre (0 : Int))) := by

  intro right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply concat_compare_outcome_at_end__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position
  all_goals first | assumption | omega

theorem aux_compare_concatenated_order_return_wit_2_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (left_length : Int) (right_length : Int) (total_length : Int) (position : Int) (left_then_right : Int) (right_then_left : Int) (PreH1 : (left_then_right < right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : ((0 : Int) <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : ((0 : Int) <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length))) (PreH16 : ((0 : Int) <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre)) (PreH21 : (FlatRows flat rows count number_width_pre)) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  (ConcatCompareSignOutcome rows lens left_pre right_pre (-1))) := by

  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply concat_compare_outcome_at_difference__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position (-1)
  all_goals first | assumption | omega | exact Or.inl ⟨rfl,by omega⟩

theorem aux_compare_concatenated_order_return_wit_3_split_goal_1 : (forall (right_pre : Int) (left_pre : Int) (number_width_pre : Int) (count : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (left_length : Int) (right_length : Int) (total_length : Int) (position : Int) (left_then_right : Int) (right_then_left : Int) (PreH1 : (left_then_right > right_then_left)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : ((0 : Int) <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : ((0 : Int) <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length))) (PreH15 : ((0 : Int) <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (RowsWellFormed rows lens count number_width_pre)) (PreH20 : (FlatRows flat rows count number_width_pre)) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position)) ,
  (ConcatCompareSignOutcome rows lens left_pre right_pre 1)) := by

  intro right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply concat_compare_outcome_at_difference__compare_semantics rows lens count number_width_pre left_pre right_pre left_length right_length position 1
  all_goals first | assumption | omega | exact Or.inr ⟨rfl,by omega⟩

theorem aux_concatenating_numbers_dp_entail_wit_2_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (mask : Int) (state_count : Int) (PreH1 : (mask < state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH12 : (FlatRows flat rows count_pre number_width_pre)) (PreH13 : ((Zlength (choices_2)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices_2)) ,
  (BitScanState mask count_pre (0 : Int) 1)) := by

  intro number_width_pre count_pre flat lens rows choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  refine ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,rfl,?_⟩
  intro lower hl
  omega

theorem aux_concatenating_numbers_dp_entail_wit_3_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) = (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  (BitScanState mask count_pre (bit + 1) (signed_last_nbits ((Z.shiftl bit_value 1)) (32)))) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  rw [he]
  exact ⟨PreH19.1,⟨by omega,by omega⟩,ha.2.2.1,ha.2.2.2.2.2⟩

theorem aux_concatenating_numbers_dp_entail_wit_3_split_goal_2 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) = (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  ((signed_last_nbits ((Z.shiftl bit_value 1)) (32)) <= state_count)) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  rw [he]
  omega

theorem aux_concatenating_numbers_dp_entail_wit_3_split_goal_3 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) = (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  (1 <= (signed_last_nbits ((Z.shiftl bit_value 1)) (32)))) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  rw [he]
  omega

theorem aux_concatenating_numbers_dp_entail_wit_3_split_goal_4 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) = (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  ((bit + 1) <= count_pre)) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := bit_scan_advance__bit_scan mask count_pre bit bit_value PreH19 PreH1
  have hr := signed_last_nbits_double_power__bit_scan bit_value state_count count_pre PreH13 PreH14 PreH2 PreH4
  have he : signed_last_nbits (Z.shiftl bit_value 1) 32=bit_value*2 := by
    rw [shift_pow bit_value 1 (by decide)]
    exact signed_last_nbits_eq (bit_value*2) 32 (by decide) hr
  omega

theorem aux_concatenating_numbers_dp_entail_wit_4_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) ≠ (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  (SelectedBitState mask count_pre bit bit_value (Z.lxor mask bit_value))) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  exact ⟨PreH19,PreH1,⟨by omega,ha.1⟩,ha.2.1,rfl,ha.2.2.2.1⟩

theorem aux_concatenating_numbers_dp_entail_wit_4_split_goal_2 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) ≠ (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  ((Z.lxor mask bit_value) < mask)) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem aux_concatenating_numbers_dp_entail_wit_4_split_goal_3 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) ≠ (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  ((0 : Int) <= (Z.lxor mask bit_value))) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem aux_concatenating_numbers_dp_entail_wit_4_split_goal_4 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) ≠ (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  (bit_value < state_count)) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem aux_concatenating_numbers_dp_entail_wit_4_split_goal_5 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (bit_value : Int) (bit : Int) (mask : Int) (state_count : Int) (PreH1 : ((Z.land mask bit_value) ≠ (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH16 : (FlatRows flat rows count_pre number_width_pre)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH19 : (BitScanState mask count_pre bit bit_value)) ,
  (bit < count_pre)) := by

  intro number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have ha := selected_bit_state_from_scan__bit_scan mask count_pre bit bit_value PreH19 PreH1
  omega

theorem aux_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (state_count : Int) (mask : Int) (bit : Int) (rest : Int) (previous_best : Int) (bit_value : Int) (PreH1 : (previous_best < (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : ((0 : Int) <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices_2)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices_2) ((0 : Int))))) (PreH17 : (rest = (0 : Int))) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH20 : (FlatRows flat rows count_pre number_width_pre)) (PreH21 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest)) ,
  (DPTablePrefix rows lens count_pre (mask + 1) (choices_2 ++ (bit :: (@List.nil Int))))) := by

  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  apply dp_table_prefix_extend__dp_table_transition rows lens count_pre mask choices_2 _ PreH21 (by omega)
  exact best_index_singleton__dp_table_transition rows lens count_pre mask bit bit_value rest PreH22 PreH17

theorem aux_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (state_count : Int) (mask : Int) (bit : Int) (rest : Int) (previous_best : Int) (bit_value : Int) (PreH1 : (previous_best < (0 : Int))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((0 : Int) <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : ((0 : Int) <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices_2)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices_2) ((0 : Int))))) (PreH17 : (rest = (0 : Int))) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH20 : (FlatRows flat rows count_pre number_width_pre)) (PreH21 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest)) ,
  ((Zlength ((choices_2 ++ (bit :: (@List.nil Int))))) = (mask + 1))) := by

  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem aux_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (state_count : Int) (mask : Int) (bit : Int) (rest : Int) (previous_best : Int) (bit_value : Int) (retval : Int) (PreH1 : (retval > (0 : Int))) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval)) (PreH3 : (previous_best >= (0 : Int))) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : ((0 : Int) <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : ((0 : Int) <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) ((0 : Int))))) (PreH19 : (1 <= rest)) (PreH20 : ((0 : Int) <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best)) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH24 : (FlatRows flat rows count_pre number_width_pre)) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest)) ,
  (DPTablePrefix rows lens count_pre (mask + 1) (choices_2 ++ (bit :: (@List.nil Int))))) := by

  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply dp_table_prefix_extend__dp_table_transition rows lens count_pre mask choices_2 _ PreH25 (by omega)
  exact best_index_choose_bit__dp_table_transition rows lens count_pre number_width_pre mask bit bit_value rest previous_best retval PreH23 PreH26 PreH22 PreH1 PreH2

theorem aux_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (state_count : Int) (mask : Int) (bit : Int) (rest : Int) (previous_best : Int) (bit_value : Int) (retval : Int) (PreH1 : (retval > (0 : Int))) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval)) (PreH3 : (previous_best >= (0 : Int))) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : ((0 : Int) <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : ((0 : Int) <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) ((0 : Int))))) (PreH19 : (1 <= rest)) (PreH20 : ((0 : Int) <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best)) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH24 : (FlatRows flat rows count_pre number_width_pre)) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest)) ,
  ((Zlength ((choices_2 ++ (bit :: (@List.nil Int))))) = (mask + 1))) := by

  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem aux_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (state_count : Int) (mask : Int) (bit : Int) (rest : Int) (previous_best : Int) (bit_value : Int) (retval : Int) (PreH1 : (retval <= (0 : Int))) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval)) (PreH3 : (previous_best >= (0 : Int))) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : ((0 : Int) <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : ((0 : Int) <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) ((0 : Int))))) (PreH19 : (1 <= rest)) (PreH20 : ((0 : Int) <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best)) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH24 : (FlatRows flat rows count_pre number_width_pre)) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest)) ,
  (DPTablePrefix rows lens count_pre (mask + 1) (choices_2 ++ (previous_best :: (@List.nil Int))))) := by

  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  apply dp_table_prefix_extend__dp_table_transition rows lens count_pre mask choices_2 _ PreH25 (by omega)
  exact best_index_keep_previous__dp_table_transition rows lens count_pre mask bit bit_value rest previous_best retval PreH26 PreH22 PreH1 PreH2

theorem aux_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (choices_2 : (List Int)) (state_count : Int) (mask : Int) (bit : Int) (rest : Int) (previous_best : Int) (bit_value : Int) (retval : Int) (PreH1 : (retval <= (0 : Int))) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval)) (PreH3 : (previous_best >= (0 : Int))) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : ((0 : Int) <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : ((0 : Int) <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) ((0 : Int))))) (PreH19 : (1 <= rest)) (PreH20 : ((0 : Int) <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best)) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH24 : (FlatRows flat rows count_pre number_width_pre)) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2)) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest)) ,
  ((Zlength ((choices_2 ++ (previous_best :: (@List.nil Int))))) = (mask + 1))) := by

  intro number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  simp only [Zlength_app,Zlength_cons,Zlength_nil]
  omega

theorem aux_concatenating_numbers_dp_entail_wit_11_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (prior : (List Int)) (output : (List Int)) (result_length : Int) (position : Int) (first : Int) (choices : (List Int)) (mask : Int) (state_count : Int) (PreH1 : (result_length <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (first <= INT_MAX)) (PreH4 : (mask <= INT_MAX)) (PreH5 : (state_count <= INT_MAX)) (PreH6 : (number_width_pre <= INT_MAX)) (PreH7 : (count_pre <= INT_MAX)) (PreH8 : (result_length >= INT_MIN)) (PreH9 : (position >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (mask >= INT_MIN)) (PreH12 : (state_count >= INT_MIN)) (PreH13 : (number_width_pre >= INT_MIN)) (PreH14 : (count_pre >= INT_MIN)) (PreH15 : (position < (Znth first lens (0 : Int)))) (PreH16 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH17 : (1 <= count_pre)) (PreH18 : (count_pre <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (1 <= (sum (lens)))) (PreH22 : ((sum (lens)) <= 200)) (PreH23 : (1 <= mask)) (PreH24 : (mask < state_count)) (PreH25 : ((Zlength (choices)) = state_count)) (PreH26 : (first = (Znth (mask) (choices) ((0 : Int))))) (PreH27 : ((0 : Int) <= first)) (PreH28 : (first < count_pre)) (PreH29 : ((0 : Int) <= position)) (PreH30 : (position <= (Znth (first) (lens) ((0 : Int))))) (PreH31 : (1 <= (Znth (first) (lens) ((0 : Int))))) (PreH32 : ((Znth (first) (lens) ((0 : Int))) <= number_width_pre)) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : ((0 : Int) <= result_length)) (PreH35 : ((result_length + ((Znth (first) (lens) ((0 : Int))) - position)) <= (sum (lens)))) (PreH36 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH37 : (FlatRows flat rows count_pre number_width_pre)) (PreH38 : (DPTablePrefix rows lens count_pre state_count choices)) (PreH39 : (BestIndexForMask rows lens count_pre mask first)) (PreH40 : (GreedyOutputPrefix rows lens count_pre mask prior)) (PreH41 : (AppendRowPrefix rows lens prior first position output)) ,
  (((first * number_width_pre) + position) < (count_pre * number_width_pre))) := by

  intro number_width_pre count_pre flat lens rows prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  exact cell_upper count_pre number_width_pre first position (by omega) (by omega) (by omega)

theorem aux_concatenating_numbers_dp_entail_wit_14_split_goal_1 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (prior : (List Int)) (output_2 : (List Int)) (result_length : Int) (position : Int) (first : Int) (choices_2 : (List Int)) (mask : Int) (state_count : Int) (PreH1 : (position >= (Znth first lens (0 : Int)))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) ((0 : Int))))) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < count_pre)) (PreH15 : ((0 : Int) <= position)) (PreH16 : (position <= (Znth (first) (lens) ((0 : Int))))) (PreH17 : (1 <= (Znth (first) (lens) ((0 : Int))))) (PreH18 : ((Znth (first) (lens) ((0 : Int))) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) ((0 : Int))) - position)) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2)) (PreH25 : (BestIndexForMask rows lens count_pre mask first)) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior)) (PreH27 : (AppendRowPrefix rows lens prior first position output_2)) ,
  (GreedyOutputPrefix rows lens count_pre (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) output_2)) := by

  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := shift_small first count_pre PreH13 PreH14 PreH4
  rw [hs.1]
  exact greedy_output_consume_best__output_finalization rows lens count_pre number_width_pre mask first prior output_2 position PreH22 PreH25 PreH26 PreH27 PreH1 PreH16

theorem aux_concatenating_numbers_dp_entail_wit_14_split_goal_2 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (prior : (List Int)) (output_2 : (List Int)) (result_length : Int) (position : Int) (first : Int) (choices_2 : (List Int)) (mask : Int) (state_count : Int) (PreH1 : (position >= (Znth first lens (0 : Int)))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) ((0 : Int))))) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < count_pre)) (PreH15 : ((0 : Int) <= position)) (PreH16 : (position <= (Znth (first) (lens) ((0 : Int))))) (PreH17 : (1 <= (Znth (first) (lens) ((0 : Int))))) (PreH18 : ((Znth (first) (lens) ((0 : Int))) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) ((0 : Int))) - position)) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2)) (PreH25 : (BestIndexForMask rows lens count_pre mask first)) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior)) (PreH27 : (AppendRowPrefix rows lens prior first position output_2)) ,
  ((Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) < state_count)) := by

  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := shift_small first count_pre PreH13 PreH14 PreH4
  rw [hs.1]
  have he : Z.shiftl 1 count_pre=Z.pow 2 count_pre := by rw [shift_pow 1 count_pre (by omega),Int.one_mul]
  have hm : 0≤mask ∧ mask<Z.pow 2 count_pre := by rw [←he];omega
  have hx := lxor_lt_pow2__output_finalization mask (Z.shiftl 1 first) count_pre hm hs.2 (by omega)
  omega

theorem aux_concatenating_numbers_dp_entail_wit_14_split_goal_3 : (forall (number_width_pre : Int) (count_pre : Int) (flat : (List Int)) (lens : (List Int)) (rows : (List (List Int))) (prior : (List Int)) (output_2 : (List Int)) (result_length : Int) (position : Int) (first : Int) (choices_2 : (List Int)) (mask : Int) (state_count : Int) (PreH1 : (position >= (Znth first lens (0 : Int)))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) ((0 : Int))))) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < count_pre)) (PreH15 : ((0 : Int) <= position)) (PreH16 : (position <= (Znth (first) (lens) ((0 : Int))))) (PreH17 : (1 <= (Znth (first) (lens) ((0 : Int))))) (PreH18 : ((Znth (first) (lens) ((0 : Int))) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : ((0 : Int) <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) ((0 : Int))) - position)) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre)) (PreH23 : (FlatRows flat rows count_pre number_width_pre)) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2)) (PreH25 : (BestIndexForMask rows lens count_pre mask first)) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior)) (PreH27 : (AppendRowPrefix rows lens prior first position output_2)) ,
  ((0 : Int) <= (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))))) := by

  intro number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := shift_small first count_pre PreH13 PreH14 PreH4
  rw [hs.1]
  have he : Z.shiftl 1 count_pre=Z.pow 2 count_pre := by rw [shift_pow 1 count_pre (by omega),Int.one_mul]
  have hm : 0≤mask ∧ mask<Z.pow 2 count_pre := by rw [←he];omega
  have hx := lxor_lt_pow2__output_finalization mask (Z.shiftl 1 first) count_pre hm hs.2 (by omega)
  omega

private theorem indexed_Forall {A : Type} (P : A → Prop) (l : List A) (d : A) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
    have hm := h l[i.toNat] (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm
  · intro h v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength l := by change 0 ≤ (n : Int) ∧ (n : Int) < (l.length : Int); omega
    have hh := h n hi
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh


private theorem nth_mem {A : Type} (l : List A) (i : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
  have hm := List.getElem_mem (l := l) hn
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm

private theorem rows_from_annotation (rows : List (List Int)) (lens : List Int) (count width : Int)
    (hr : Zlength rows = count) (hl : Zlength lens = count)
    (hw : Forall (Eq width) (rows.map Zlength))
    (hl0 : Forall (LE.le (1 : Int)) lens) (hlu : Forall (GE.ge width) lens)
    (hh0 : Forall (LE.le (1 : Int)) (rows.map (hd (0 : Int))))
    (hhu : Forall (GE.ge (9 : Int)) (rows.map (hd (0 : Int))))
    (hd0 : Forall (LE.le (0 : Int)) (concatenate_indices rows lens (all_indices (Zlength rows))))
    (hdu : Forall (GE.ge (9 : Int)) (concatenate_indices rows lens (all_indices (Zlength rows)))) :
    RowsWellFormed rows lens count width := by
  refine ⟨hr, hl, ?_⟩
  intro i hi
  have hrowmem := nth_mem rows i [] (by rw [hr]; exact hi)
  have hwidth : Zlength (Znth i rows []) = width :=
    (hw.mem (List.mem_map.mpr ⟨Znth i rows [], hrowmem, rfl⟩)).symm
  have hlen0 := (indexed_Forall _ lens 0).mp hl0 i (by rw [hl]; exact hi)
  have hlenu := (indexed_Forall _ lens 0).mp hlu i (by rw [hl]; exact hi)
  have hhead : Znth 0 (Znth i rows []) 0 = hd 0 (Znth i rows []) := by
    cases Znth i rows [] <;> rfl
  refine ⟨hwidth, ⟨hlen0, hlenu⟩, ?_, ?_⟩
  · rw [hhead]
    exact ⟨hh0.mem (List.mem_map.mpr ⟨Znth i rows [], hrowmem, rfl⟩),
      hhu.mem (List.mem_map.mpr ⟨Znth i rows [], hrowmem, rfl⟩)⟩
  · intro j hj
    have hidx : i ∈ all_indices (Zlength rows) :=
      (all_indices_spec__output_initialization _ i (by rw [hr]; omega)).mpr (by rw [hr]; exact hi)
    have hsubLen : Zlength (sublist 0 (Znth i lens 0) (Znth i rows [])) = Znth i lens 0 := by
      simpa only [Int.sub_zero] using ListLib.Zlength_sublist 0 (Znth i lens 0) (Znth i rows [])
        ⟨by omega, by omega⟩ (by change Znth i lens 0 ≤ Zlength (Znth i rows []); rw [hwidth]; exact hlenu)
    have hmember := nth_mem (sublist 0 (Znth i lens 0) (Znth i rows [])) j 0 (by rw [hsubLen]; exact hj)
    have hz := Znth_sublist 0 0 j (Znth i lens 0) (Znth i rows []) (by omega) (by simpa only [Int.sub_zero] using hj)
    simp only [Int.add_zero] at hz
    rw [hz] at hmember
    have hall : Znth j (Znth i rows []) 0 ∈ concatenate_indices rows lens (all_indices (Zlength rows)) := by
      exact List.mem_flatten.mpr ⟨item_digits (item_at rows lens i),
        List.mem_map.mpr ⟨i, hidx, rfl⟩, hmember⟩
    exact ⟨hd0.mem hall, hdu.mem hall⟩


theorem proof_of_compare_concatenated_order_safety_wit_1_split_goal_1 : compare_concatenated_order_safety_wit_1_split_goal_1 := by
  unfold compare_concatenated_order_safety_wit_1_split_goal_1
  intro count flat lens rows numbers_pre lengths_pre number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_safety_wit_1_split_goal_1 right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_safety_wit_1_split_goal_2 : compare_concatenated_order_safety_wit_1_split_goal_2 := by
  unfold compare_concatenated_order_safety_wit_1_split_goal_2
  intro count flat lens rows numbers_pre lengths_pre number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_safety_wit_1_split_goal_2 right_pre left_pre number_width_pre lengths_pre numbers_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 : compare_concatenated_order_entail_wit_1_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_entail_wit_1_split_goal_1 right_pre left_pre number_width_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 : compare_concatenated_order_entail_wit_1_split_goal_2 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_2
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_entail_wit_1_split_goal_2 right_pre left_pre number_width_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_3 : compare_concatenated_order_entail_wit_1_split_goal_3 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_3
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_entail_wit_1_split_goal_5 right_pre left_pre number_width_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 : compare_concatenated_order_entail_wit_1_split_goal_4 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_4
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_entail_wit_1_split_goal_6 right_pre left_pre number_width_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 : compare_concatenated_order_entail_wit_1_split_goal_5 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_5
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_entail_wit_1_split_goal_7 right_pre left_pre number_width_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 : compare_concatenated_order_entail_wit_1_split_goal_6 := by
  unfold compare_concatenated_order_entail_wit_1_split_goal_6
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply aux_compare_concatenated_order_entail_wit_1_split_goal_8 right_pre left_pre number_width_pre count flat lens rows
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_2_split_goal_1 : compare_concatenated_order_entail_wit_2_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_2_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  apply aux_compare_concatenated_order_entail_wit_3_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 : compare_concatenated_order_entail_wit_3_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_3_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  apply aux_compare_concatenated_order_entail_wit_5_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_4_1_split_goal_1 : compare_concatenated_order_entail_wit_4_1_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_4_1_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position hWF PreH39 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH40.1 PreH40.2.1).1 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_4_2_split_goal_1 : compare_concatenated_order_entail_wit_4_2_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_4_2_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position hWF PreH37 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH38.1 PreH38.2.1).2.1 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 : compare_concatenated_order_entail_wit_5_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_5_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  apply aux_compare_concatenated_order_entail_wit_8_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_6_split_goal_1 : compare_concatenated_order_entail_wit_6_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_6_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  apply aux_compare_concatenated_order_entail_wit_10_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_entail_wit_7_1_split_goal_1 : compare_concatenated_order_entail_wit_7_1_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_7_1_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position hWF PreH41 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH42.1 PreH42.2.1).2.2.1 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_7_2_split_goal_1 : compare_concatenated_order_entail_wit_7_2_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_7_2_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  exact (concat_digit_lookup__compare_digits flat rows lens count number_width_pre left_pre right_pre left_length right_length position hWF PreH39 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ PreH40.1 PreH40.2.1).2.2.2 ⟨by omega,by omega⟩

theorem proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 : compare_concatenated_order_entail_wit_8_split_goal_1 := by
  unfold compare_concatenated_order_entail_wit_8_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  apply aux_compare_concatenated_order_entail_wit_12_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_return_wit_1_split_goal_1 : compare_concatenated_order_return_wit_1_split_goal_1 := by
  unfold compare_concatenated_order_return_wit_1_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  apply aux_compare_concatenated_order_return_wit_1_split_goal_1 right_pre left_pre number_width_pre count flat lens rows position total_length right_length left_length
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_return_wit_2_split_goal_1 : compare_concatenated_order_return_wit_2_split_goal_1 := by
  unfold compare_concatenated_order_return_wit_2_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  apply aux_compare_concatenated_order_return_wit_2_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_return_wit_3_split_goal_1 : compare_concatenated_order_return_wit_3_split_goal_1 := by
  unfold compare_concatenated_order_return_wit_3_split_goal_1
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hWF : RowsWellFormed rows lens count number_width_pre := rows_from_annotation rows lens count number_width_pre PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  apply aux_compare_concatenated_order_return_wit_3_split_goal_1 right_pre left_pre number_width_pre count flat lens rows left_length right_length total_length position left_then_right right_then_left
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 : concatenating_numbers_dp_entail_wit_2_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_2_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  apply aux_concatenating_numbers_dp_entail_wit_2_split_goal_1 number_width_pre count_pre flat lens rows choices_2 mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1 : concatenating_numbers_dp_entail_wit_3_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_3_split_goal_1 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 : concatenating_numbers_dp_entail_wit_3_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_2
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_3_split_goal_2 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 : concatenating_numbers_dp_entail_wit_3_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_3
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_3_split_goal_3 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4 : concatenating_numbers_dp_entail_wit_3_split_goal_4 := by
  unfold concatenating_numbers_dp_entail_wit_3_split_goal_4
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_3_split_goal_4 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 : concatenating_numbers_dp_entail_wit_4_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_4_split_goal_1 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 : concatenating_numbers_dp_entail_wit_4_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_2
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_4_split_goal_2 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 : concatenating_numbers_dp_entail_wit_4_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_3
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_4_split_goal_3 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 : concatenating_numbers_dp_entail_wit_4_split_goal_4 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_4
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_4_split_goal_4 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 : concatenating_numbers_dp_entail_wit_4_split_goal_5 := by
  unfold concatenating_numbers_dp_entail_wit_4_split_goal_5
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  apply aux_concatenating_numbers_dp_entail_wit_4_split_goal_5 number_width_pre count_pre flat lens rows choices_2 bit_value bit mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 : concatenating_numbers_dp_entail_wit_6_1_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_1_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  apply aux_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 : concatenating_numbers_dp_entail_wit_6_1_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_1_split_goal_2
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  apply aux_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 : concatenating_numbers_dp_entail_wit_6_2_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_2_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  apply aux_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 : concatenating_numbers_dp_entail_wit_6_2_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_2_split_goal_2
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  apply aux_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 : concatenating_numbers_dp_entail_wit_6_3_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_3_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  apply aux_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 : concatenating_numbers_dp_entail_wit_6_3_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_3_split_goal_2
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  apply aux_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 number_width_pre count_pre flat lens rows choices_2 state_count mask bit rest previous_best bit_value retval
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_10_split_goal_1 : concatenating_numbers_dp_entail_wit_10_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_10_split_goal_1
  intro flat lens rows count_pre number_width_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  apply aux_concatenating_numbers_dp_entail_wit_11_split_goal_1 number_width_pre count_pre flat lens rows prior output result_length position first choices mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_1 : concatenating_numbers_dp_entail_wit_12_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_12_split_goal_1
  intro flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  apply aux_concatenating_numbers_dp_entail_wit_14_split_goal_1 number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_2 : concatenating_numbers_dp_entail_wit_12_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_12_split_goal_2
  intro flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  apply aux_concatenating_numbers_dp_entail_wit_14_split_goal_2 number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count
  all_goals first | assumption | omega

theorem proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_3 : concatenating_numbers_dp_entail_wit_12_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_12_split_goal_3
  intro flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  apply aux_concatenating_numbers_dp_entail_wit_14_split_goal_3 number_width_pre count_pre flat lens rows prior output_2 result_length position first choices_2 mask state_count
  all_goals first | assumption | omega

theorem proof_of_compare_concatenated_order_safety_wit_1 : compare_concatenated_order_safety_wit_1 := by
  unfold compare_concatenated_order_safety_wit_1
  right
  intro count flat lens rows numbers_pre lengths_pre number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hWF := rows_from_annotation rows lens count number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hl := hWF.2.2 left_pre ⟨PreH5, PreH6⟩
  have hr := hWF.2.2 right_pre ⟨PreH7, PreH8⟩
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_compare_concatenated_order_entail_wit_1 : compare_concatenated_order_entail_wit_1 := by
  unfold compare_concatenated_order_entail_wit_1
  right
  intro count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_compare_concatenated_order_entail_wit_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_compare_concatenated_order_entail_wit_1_split_goal_2 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_3 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_compare_concatenated_order_entail_wit_1_split_goal_3 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_compare_concatenated_order_entail_wit_1_split_goal_4 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_compare_concatenated_order_entail_wit_1_split_goal_5 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | exact (proof_of_compare_concatenated_order_entail_wit_1_split_goal_6 count flat lens rows number_width_pre left_pre right_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_2 : compare_concatenated_order_entail_wit_2 := by
  unfold compare_concatenated_order_entail_wit_2
  right
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42))
    | exact (proof_of_compare_concatenated_order_entail_wit_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_3 : compare_concatenated_order_entail_wit_3 := by
  unfold compare_concatenated_order_entail_wit_3
  right
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42))
    | exact (proof_of_compare_concatenated_order_entail_wit_3_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_4_1 : compare_concatenated_order_entail_wit_4_1 := by
  unfold compare_concatenated_order_entail_wit_4_1
  right
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_4_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40))
    | exact (proof_of_compare_concatenated_order_entail_wit_4_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_4_2 : compare_concatenated_order_entail_wit_4_2 := by
  unfold compare_concatenated_order_entail_wit_4_2
  right
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_4_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38))
    | exact (proof_of_compare_concatenated_order_entail_wit_4_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_5 : compare_concatenated_order_entail_wit_5 := by
  unfold compare_concatenated_order_entail_wit_5
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44))
    | exact (proof_of_compare_concatenated_order_entail_wit_5_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_6 : compare_concatenated_order_entail_wit_6 := by
  unfold compare_concatenated_order_entail_wit_6
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_6_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44))
    | exact (proof_of_compare_concatenated_order_entail_wit_6_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_7_1 : compare_concatenated_order_entail_wit_7_1 := by
  unfold compare_concatenated_order_entail_wit_7_1
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_7_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42))
    | exact (proof_of_compare_concatenated_order_entail_wit_7_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_7_2 : compare_concatenated_order_entail_wit_7_2 := by
  unfold compare_concatenated_order_entail_wit_7_2
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_7_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40))
    | exact (proof_of_compare_concatenated_order_entail_wit_7_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_entail_wit_8 : compare_concatenated_order_entail_wit_8 := by
  unfold compare_concatenated_order_entail_wit_8
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | exact (proof_of_compare_concatenated_order_entail_wit_8_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_return_wit_1 : compare_concatenated_order_return_wit_1 := by
  unfold compare_concatenated_order_return_wit_1
  right
  intro count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_return_wit_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_compare_concatenated_order_return_wit_1_split_goal_1 count flat lens rows number_width_pre left_pre right_pre position total_length right_length left_length PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_return_wit_2 : compare_concatenated_order_return_wit_2 := by
  unfold compare_concatenated_order_return_wit_2
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_return_wit_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | exact (proof_of_compare_concatenated_order_return_wit_2_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_compare_concatenated_order_return_wit_3 : compare_concatenated_order_return_wit_3 := by
  unfold compare_concatenated_order_return_wit_3
  right
  intro count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_compare_concatenated_order_return_wit_3_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | exact (proof_of_compare_concatenated_order_return_wit_3_split_goal_1 count flat lens rows number_width_pre left_pre right_pre left_length right_length total_length position left_then_right right_then_left PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_2 : concatenating_numbers_dp_entail_wit_2 := by
  unfold concatenating_numbers_dp_entail_wit_2
  right
  intro flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_2_split_goal_1 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_3 : concatenating_numbers_dp_entail_wit_3 := by
  unfold concatenating_numbers_dp_entail_wit_3
  right
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_1 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_2 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_3 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_3_split_goal_4 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_4 : concatenating_numbers_dp_entail_wit_4 := by
  unfold concatenating_numbers_dp_entail_wit_4
  right
  intro flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_1 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_2 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_3 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_4 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_4_split_goal_5 flat lens rows count_pre number_width_pre choices_2 bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_6_1 : concatenating_numbers_dp_entail_wit_6_1 := by
  unfold concatenating_numbers_dp_entail_wit_6_1
  right
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_1 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_6_1_split_goal_2 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_6_2 : concatenating_numbers_dp_entail_wit_6_2 := by
  unfold concatenating_numbers_dp_entail_wit_6_2
  right
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_1 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_6_2_split_goal_2 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_6_3 : concatenating_numbers_dp_entail_wit_6_3 := by
  unfold concatenating_numbers_dp_entail_wit_6_3
  right
  intro flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_1 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_6_3_split_goal_2 flat lens rows count_pre number_width_pre choices_2 state_count mask bit rest previous_best bit_value retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_10 : concatenating_numbers_dp_entail_wit_10 := by
  unfold concatenating_numbers_dp_entail_wit_10
  right
  intro flat lens rows count_pre number_width_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_10_split_goal_1 flat lens rows count_pre number_width_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_10_split_goal_1 flat lens rows count_pre number_width_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_12 : concatenating_numbers_dp_entail_wit_12 := by
  unfold concatenating_numbers_dp_entail_wit_12
  right
  intro flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_1 flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_1 flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_2 flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_2 flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_3 flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_12_split_goal_3 flat lens rows count_pre number_width_pre prior output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35)
    | assumption
    | omega
    | rfl
    | trivial

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_1 : concatenating_numbers_dp_safety_wit_1_split_goal_1 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_1
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hr := signed_Lastnbits_range (1*Z.pow 2 count_pre) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 count_pre) 32 ∧ signed_last_nbits (1*Z.pow 2 count_pre) 32<2147483648 at hr
  dump_pre_spatial
  change signed_last_nbits (1*Z.pow 2 count_pre) 32≤2147483647
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_2 : concatenating_numbers_dp_safety_wit_1_split_goal_2 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_2
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hr := signed_Lastnbits_range (1*Z.pow 2 count_pre) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 count_pre) 32 ∧ signed_last_nbits (1*Z.pow 2 count_pre) 32<2147483648 at hr
  dump_pre_spatial
  change (-2147483648:Int)≤signed_last_nbits (1*Z.pow 2 count_pre) 32
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_3 : concatenating_numbers_dp_safety_wit_1_split_goal_3 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_3
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_1_split_goal_4 : concatenating_numbers_dp_safety_wit_1_split_goal_4 := by
  unfold concatenating_numbers_dp_safety_wit_1_split_goal_4
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_1 : concatenating_numbers_dp_safety_wit_11_split_goal_1 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_1
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hr := signed_Lastnbits_range (bit_value*Z.pow 2 1) 32 (by decide)
  change -2147483648≤signed_last_nbits (bit_value*Z.pow 2 1) 32 ∧ signed_last_nbits (bit_value*Z.pow 2 1) 32<2147483648 at hr
  dump_pre_spatial
  change signed_last_nbits (bit_value*Z.pow 2 1) 32≤2147483647
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_2 : concatenating_numbers_dp_safety_wit_11_split_goal_2 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_2
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have hr := signed_Lastnbits_range (bit_value*Z.pow 2 1) 32 (by decide)
  change -2147483648≤signed_last_nbits (bit_value*Z.pow 2 1) 32 ∧ signed_last_nbits (bit_value*Z.pow 2 1) 32<2147483648 at hr
  dump_pre_spatial
  change (-2147483648:Int)≤signed_last_nbits (bit_value*Z.pow 2 1) 32
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_3 : concatenating_numbers_dp_safety_wit_11_split_goal_3 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_3
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_11_split_goal_4 : concatenating_numbers_dp_safety_wit_11_split_goal_4 := by
  unfold concatenating_numbers_dp_safety_wit_11_split_goal_4
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_1 : concatenating_numbers_dp_safety_wit_28_split_goal_1 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_1
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := signed_Lastnbits_range (1*Z.pow 2 first) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 first) 32 ∧ signed_last_nbits (1*Z.pow 2 first) 32<2147483648 at hr
  dump_pre_spatial
  change signed_last_nbits (1*Z.pow 2 first) 32≤2147483647
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_2 : concatenating_numbers_dp_safety_wit_28_split_goal_2 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_2
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hr := signed_Lastnbits_range (1*Z.pow 2 first) 32 (by decide)
  change -2147483648≤signed_last_nbits (1*Z.pow 2 first) 32 ∧ signed_last_nbits (1*Z.pow 2 first) 32<2147483648 at hr
  dump_pre_spatial
  change (-2147483648:Int)≤signed_last_nbits (1*Z.pow 2 first) 32
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_3 : concatenating_numbers_dp_safety_wit_28_split_goal_3 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_3
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_safety_wit_28_split_goal_4 : concatenating_numbers_dp_safety_wit_28_split_goal_4 := by
  unfold concatenating_numbers_dp_safety_wit_28_split_goal_4
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  dump_pre_spatial
  omega

theorem proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_1 : concatenating_numbers_dp_entail_wit_8_split_goal_1 := by
  unfold concatenating_numbers_dp_entail_wit_8_split_goal_1
  intro flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hg := greedy_output_full_mask__output_initialization rows lens count_pre PreH11 (by omega)
  simpa only [← PreH2] using hg

theorem proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_2 : concatenating_numbers_dp_entail_wit_8_split_goal_2 := by
  unfold concatenating_numbers_dp_entail_wit_8_split_goal_2
  intro flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : mask = state_count := by omega
  simpa only [he] using PreH22

theorem proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_3 : concatenating_numbers_dp_entail_wit_8_split_goal_3 := by
  unfold concatenating_numbers_dp_entail_wit_8_split_goal_3
  intro flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rfl

theorem proof_of_concatenating_numbers_dp_safety_wit_1 : concatenating_numbers_dp_safety_wit_1 := by
  unfold concatenating_numbers_dp_safety_wit_1
  right
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pures <;> dump_pre_spatial
  all_goals first
    | assumption
    | omega
    | trivial
    | (solve |
        have hr := signed_Lastnbits_range (1*Z.pow 2 count_pre) 32 (by decide)
        change -2147483648≤signed_last_nbits (1*Z.pow 2 count_pre) 32 ∧ signed_last_nbits (1*Z.pow 2 count_pre) 32<2147483648 at hr
        change signed_last_nbits (1*Z.pow 2 count_pre) 32≤2147483647
        omega
      )
    | (solve |
        have hr := signed_Lastnbits_range (1*Z.pow 2 count_pre) 32 (by decide)
        change -2147483648≤signed_last_nbits (1*Z.pow 2 count_pre) 32 ∧ signed_last_nbits (1*Z.pow 2 count_pre) 32<2147483648 at hr
        change (-2147483648:Int)≤signed_last_nbits (1*Z.pow 2 count_pre) 32
        omega
      )
    | (solve |
        omega
      )
    | (solve |
        omega
      )

theorem proof_of_concatenating_numbers_dp_safety_wit_11 : concatenating_numbers_dp_safety_wit_11 := by
  unfold concatenating_numbers_dp_safety_wit_11
  right
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices bit_value bit mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  split_pures <;> dump_pre_spatial
  all_goals first
    | assumption
    | omega
    | trivial
    | (solve |
        have hr := signed_Lastnbits_range (bit_value*Z.pow 2 1) 32 (by decide)
        change -2147483648≤signed_last_nbits (bit_value*Z.pow 2 1) 32 ∧ signed_last_nbits (bit_value*Z.pow 2 1) 32<2147483648 at hr
        change signed_last_nbits (bit_value*Z.pow 2 1) 32≤2147483647
        omega
      )
    | (solve |
        have hr := signed_Lastnbits_range (bit_value*Z.pow 2 1) 32 (by decide)
        change -2147483648≤signed_last_nbits (bit_value*Z.pow 2 1) 32 ∧ signed_last_nbits (bit_value*Z.pow 2 1) 32<2147483648 at hr
        change (-2147483648:Int)≤signed_last_nbits (bit_value*Z.pow 2 1) 32
        omega
      )
    | (solve |
        omega
      )
    | (solve |
        omega
      )

theorem proof_of_concatenating_numbers_dp_safety_wit_28 : concatenating_numbers_dp_safety_wit_28 := by
  unfold concatenating_numbers_dp_safety_wit_28
  right
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre prior output result_length position first choices mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF : RowsWellFormed rows lens count_pre number_width_pre := rows_from_annotation rows lens count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  split_pures <;> dump_pre_spatial
  all_goals first
    | assumption
    | omega
    | trivial
    | (solve |
        have hr := signed_Lastnbits_range (1*Z.pow 2 first) 32 (by decide)
        change -2147483648≤signed_last_nbits (1*Z.pow 2 first) 32 ∧ signed_last_nbits (1*Z.pow 2 first) 32<2147483648 at hr
        change signed_last_nbits (1*Z.pow 2 first) 32≤2147483647
        omega
      )
    | (solve |
        have hr := signed_Lastnbits_range (1*Z.pow 2 first) 32 (by decide)
        change -2147483648≤signed_last_nbits (1*Z.pow 2 first) 32 ∧ signed_last_nbits (1*Z.pow 2 first) 32<2147483648 at hr
        change (-2147483648:Int)≤signed_last_nbits (1*Z.pow 2 first) 32
        omega
      )
    | (solve |
        omega
      )
    | (solve |
        omega
      )

theorem proof_of_concatenating_numbers_dp_entail_wit_8 : concatenating_numbers_dp_entail_wit_8 := by
  unfold concatenating_numbers_dp_entail_wit_8
  right
  intro flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_1 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_1 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_2 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_2 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | (solve | Goal_apply (proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_3 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | exact (proof_of_concatenating_numbers_dp_entail_wit_8_split_goal_3 flat lens rows count_pre number_width_pre choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22)
    | assumption
    | omega
    | rfl
    | trivial

attribute [local irreducible]
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_array_rec
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_undef_array_rec
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_array
  SimpleC.SL.CommonAssertion.DerivedPredSig.store_undef_array

theorem proof_of_concatenating_numbers_dp_entail_wit_1 : concatenating_numbers_dp_entail_wit_1 := by
  unfold concatenating_numbers_dp_entail_wit_1
  left
  intro flat lens rows numbers count width lengths result hn hnmax hw hwmax hshift hshiftmax hsum hsummax hr hl hmap hlb hlu hhb hhu hdb hdu heq hvalues
  have hrows := decimal_rows_lengths_from_map rows width hmap
  have hflat : FlatRows flat rows count width := by
    refine ⟨?_, hr, ?_⟩
    · rw [heq, decimal_rows_flat_length rows width hrows, hr]
    · intro i hi
      rw [heq]
      exact decimal_rows_flat_row rows width i (by omega) hrows (by rw [hr]; exact hi)
  have hcast : signed_last_nbits (Z.shiftl 1 count) 32 = Z.shiftl 1 count := by
    apply signed_last_nbits_eq _ 32 (by decide)
    change -2147483648 ≤ Z.shiftl 1 count ∧ Z.shiftl 1 count < 2147483648
    omega
  rw [hcast]
  have hsingle : ((&("best_first")) # Int |-> (-1 : Int)) |-- intArray.seg (&("best_first")) 0 1 [-1] := by
    have hs := intArray.seg_single (&("best_first")) 0 (-1 : Int)
    change (((&("best_first"))+0*sizeof(INT)) # Int |-> (-1 : Int)) |-- intArray.seg (&("best_first")) 0 1 [-1] at hs
    simpa only [Int.zero_mul, Int.add_zero] using hs
  simp only [Int.zero_mul, Int.add_zero]
  have hframe := naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
    (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
      (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ hsingle
          (naive_C_Rules.toContext.derivable1_refl (intArray.undef_seg (&("best_first")) 1 1048576)))
        (naive_C_Rules.toContext.derivable1_refl (array2.full numbers count width rows)))
      (naive_C_Rules.toContext.derivable1_refl (intArray.full lengths count lens)))
    (naive_C_Rules.toContext.derivable1_refl (intArray.undef_full result (sum lens)))
  refine naive_C_Rules.toContext.derivable1_trans _ _ _ hframe ?_
  sep_apply (intArray.undef_seg_split_to_undef_seg (&("best_first")) 1 (Z.shiftl 1 count) 1048576 ⟨by omega, hshiftmax⟩)
  sep_apply (decimal_rows_flatten rows numbers count width (by omega))
  Exists ([-1] : List Int)
  have hprefix := dp_table_prefix_singleton__dp_initialization rows lens count (by omega)
  simp only [heq] at hflat ⊢
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | rfl | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_5 : concatenating_numbers_dp_entail_wit_5 := by
  unfold concatenating_numbers_dp_entail_wit_5
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices state_count mask bit bit_value rest PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  simp only [Int.sub_zero]
  by_cases hz : rest = 0
  · Left
    Exists choices
    have hzero : Znth rest choices 0 = -1 := by
      rw [hz]
      exact PreH27.2.2.1
    split_pure_spatial
    · cancel
      try exact naive_C_Rules.toContext.derivable1_refl _
    · split_pures <;> dump_pre_spatial <;> first | assumption | omega | rfl | trivial
  · have hbest := PreH27.2.2.2 rest (show 1 ≤ rest ∧ rest < mask by omega)
    have hindex := hbest.1
    have hbit := hbest.2.1
    Right
    Exists choices
    split_pure_spatial
    · cancel
      try exact naive_C_Rules.toContext.derivable1_refl _
    · split_pures <;> dump_pre_spatial <;> first | assumption | omega | rfl | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_9 : concatenating_numbers_dp_entail_wit_9 := by
  unfold concatenating_numbers_dp_entail_wit_9
  left
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hWF := rows_from_annotation rows lens count_pre number_width_pre
    PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hbest := PreH25.2.2.2 mask (show 1 ≤ mask ∧ mask < state_count by omega)
  have hindex := hbest.1
  have hbit := hbest.2.1
  have hlength := (hWF.2.2 (Znth mask choices 0) hindex).2.1
  have hremaining := greedy_output_remaining_length__output_initialization
    rows lens count_pre number_width_pre mask output_2 (Znth mask choices 0)
    hWF PreH26 hindex hbit
  have happ : AppendRowPrefix rows lens output_2 (Znth mask choices 0) 0 output_2 := by
    simp [AppendRowPrefix, sublist]
  Exists output_2 output_2 choices
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | rfl | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_11 : concatenating_numbers_dp_entail_wit_11 := by
  unfold concatenating_numbers_dp_entail_wit_11
  left
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre prior_2 output_2 result_length position first choices_2 mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hWF := rows_from_annotation rows lens count_pre number_width_pre
    PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have happ := append_row_prefix_step__output_row_copy flat rows lens count_pre
    number_width_pre prior_2 output_2 first position hWF PreH39
    ⟨PreH21, PreH22⟩ ⟨PreH23, PreH9⟩ PreH43
  have hlen : result_length + 1 = Zlength (output_2 ++ [Znth (first * number_width_pre + position) flat 0]) := by
    simp only [Zlength_app, Zlength_cons, Zlength_nil]
    omega
  Exists prior_2 (output_2 ++ [Znth (first * number_width_pre + position) flat 0]) choices_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | rfl | trivial

theorem proof_of_concatenating_numbers_dp_entail_wit_13 : concatenating_numbers_dp_entail_wit_13 := by
  unfold concatenating_numbers_dp_entail_wit_13
  left
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre choices output_2 result_length mask state_count PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hWF := rows_from_annotation rows lens count_pre number_width_pre
    PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hg : GreedyOutputPrefix rows lens count_pre 0 output_2 := by
    simpa only [PreH1] using PreH26
  obtain ⟨hlargest, hout⟩ := greedy_output_empty_mask__output_finalization
    rows lens count_pre number_width_pre output_2 hWF hg
  have hresult : result_length = sum lens := by omega
  have hwidth := decimal_rows_lengths_from_map rows number_width_pre PreH16
  have hdata := decimal_rows_concat_unique rows flat count_pre number_width_pre
    (by omega) hwidth PreH14 PreH23.1 PreH23.2.2
  asrt_simpl
  Intros
  rename_i hs hm hres
  rcases hs with ⟨hsvalid, hsu, hsl⟩
  rcases hm with ⟨hmvalid, hmu, hml⟩
  rcases hres with ⟨hrvalid, hru, hrl⟩
  Exists output_2
  split_pure_spatial
  · rw [hresult]
    sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (intArray.undef_seg_empty result_pre (sum lens))).1)
    sep_apply (intArray.seg_to_full result_pre 0 (sum lens) output_2)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    rw [←PreH2, hdata]
    sep_apply (decimal_rows_unflatten rows numbers_pre count_pre number_width_pre
      (by omega) hwidth PreH14)
    prop_apply (intArray.undef_seg_valid (&("best_first")) state_count 1048576)
    Intros_p hcapacity
    sep_apply (intArray.full_to_undef_full (&("best_first")) state_count choices)
    sep_apply (intArray.undef_full_to_undef_seg (&("best_first")) state_count)
    sep_apply (intArray.undef_seg_merge_to_undef_full (&("best_first")) 0 state_count 1048576 (by omega))
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    sep_apply (store_int_undef_store_int naive_C_Rules (&("state_count")) state_count)
    sep_apply (store_int_undef_store_int naive_C_Rules (&("mask")) mask)
    sep_apply (store_int_undef_store_int naive_C_Rules (&("result_length")) (sum lens))
    asrt_simpl
    Intros
    cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
    all_goals first | assumption | (solve | constructor <;> first | assumption | omega)
  · split_pures <;> dump_pre_spatial <;> first | assumption | exact hlargest

end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_proof_manual
