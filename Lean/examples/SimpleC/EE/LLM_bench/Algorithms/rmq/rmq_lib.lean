import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib
open AUXLib


open MaxMinLib

def Power2 (j : Int) : Int := Z.pow 2 j

def RMQSizeSafe (n K : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100000 ∧ 1 ≤ K ∧ K ≤ 30 ∧ n * K ≤ 1000000 ∧ n < Power2 K

def RMQInputValues (l : List Int) (n : Int) : Prop :=
  Zlength l = n ∧ ∀ i, (0 ≤ i ∧ i < n) → (-2147483648 ≤ Znth i l 0 ∧ Znth i l 0 ≤ 2147483647)

def STTableShape (st_ls : List Int) (K n : Int) : Prop := Zlength st_ls = n * K

def STCellBounds (st_ls : List Int) (K i j : Int) : Prop :=
  0 < K ∧ 0 ≤ i ∧ 0 ≤ j ∧ j < K ∧ (0 ≤ i * K + j ∧ i * K + j < Zlength st_ls)

def STZeroPrefixBounds (st_ls : List Int) (upto : Int) : Prop := 0 ≤ upto ∧ upto ≤ Zlength st_ls
def STBasePrefixBounds (n upto : Int) : Prop := 0 ≤ upto ∧ upto ≤ n
def STBuiltBeforeLevelBounds (K level : Int) : Prop := 0 ≤ level ∧ level ≤ K
def STLevelPrefixBounds (K n j upto : Int) : Prop := 0 ≤ j ∧ j < K ∧ 0 ≤ upto ∧ upto ≤ n

def RangeMaxValue (l : List Int) (lo hi ans : Int) : Prop :=
  0 ≤ lo ∧ lo < hi ∧ hi ≤ Zlength l ∧
    max_value_of_subset (· ≤ ·) (fun k => lo ≤ k ∧ k < hi) (fun k => Znth k l 0) ans

def STCellRangeMax (l st_ls : List Int) (K i j : Int) : Prop :=
  RangeMaxValue l i (i + Power2 j) (Znth (i * K + j) st_ls 0)

def STZeroPrefix (st_ls : List Int) (upto : Int) : Prop :=
  ∀ p, (0 ≤ p ∧ p < upto) → Znth p st_ls 0 = 0

def STBasePrefix (l st_ls : List Int) (K n upto : Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < upto) → STCellRangeMax l st_ls K i 0

def STBuiltBeforeLevel (l st_ls : List Int) (K n level : Int) : Prop :=
  ∀ i j, (0 ≤ i ∧ 0 ≤ j ∧ j < level ∧ i + Power2 j ≤ n) → STCellRangeMax l st_ls K i j

def STLevelPrefix (l st_ls : List Int) (K n j upto : Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < upto ∧ i + Power2 j ≤ n) → STCellRangeMax l st_ls K i j

def STBuilt (l st_ls : List Int) (K n : Int) : Prop := STBuiltBeforeLevel l st_ls K n K

def QueryIntervalBounds (n left right : Int) : Prop := 0 ≤ left ∧ left ≤ right ∧ right < n

def QueryLogBounds (K n len k pow : Int) : Prop :=
  1 ≤ len ∧ len ≤ n ∧ 1 ≤ K ∧ n < Power2 K ∧ 0 ≤ k ∧ k < K ∧ 1 ≤ pow

def QueryLogLoopState (len k pow : Int) : Prop := 0 ≤ k ∧ pow = Power2 k ∧ Power2 k ≤ len

def QueryLogFinalState (len k pow : Int) : Prop := QueryLogLoopState len k pow ∧ len < Power2 (k + 1)

private theorem power_nat (j : Int) (hj : 0 ≤ j) : Power2 j = (2 : Int)^j.toNat := by
  cases j with
  | ofNat j => rfl
  | negSucc j => omega

theorem worker_Power2_nonneg (j : Int) : 0 ≤ Power2 j := by
  cases j with
  | ofNat j => exact pow_nonneg (by omega) j
  | negSucc j => exact le_refl _

theorem worker_Power2_bound_lt_30 (j K : Int) (hK : K ≤ 30) (hj : j < K) : Power2 j ≤ 536870912 := by
  by_cases hn : 0 ≤ j
  · rw [power_nat j hn]
    have h := pow_le_pow_right₀ (show (1 : Int) ≤ 2 by omega) (show j.toNat ≤ 29 by omega)
    have he : (2 : Int)^29 = 536870912 := by decide
    rw [he] at h
    exact h
  · cases j with
    | ofNat j => exact False.elim (hn (Int.natCast_nonneg j))
    | negSucc j => change (0 : Int) ≤ 536870912; omega

theorem worker_Power2_double_int_bound_30 (j K : Int) (hK : K ≤ 30) (hj : j < K) : Power2 j*2 ≤ 2147483647 := by
  have := worker_Power2_bound_lt_30 j K hK hj; omega

theorem worker_Power2_plus_n_int_bound_30 (j K n i : Int) (hK : K ≤ 30) (hj : j < K)
    (hn : n ≤ 100000) (hi : i ≤ n) : i+Power2 j ≤ 2147483647 := by
  have := worker_Power2_bound_lt_30 j K hK hj; omega

theorem STZeroPrefix_replace_zero_step (st_ls : List Int) (idx : Int)
    (hz : STZeroPrefix st_ls idx) (hi : idx < Zlength st_ls) :
    STZeroPrefix (replace_Znth idx 0 st_ls) (idx+1) := by
  intro p hp
  by_cases he : p = idx
  · rw [he,Znth_replace_Znth_Same 0 st_ls idx 0 ⟨by omega,hi⟩]
  · by_cases hidx : 0 ≤ idx
    · rw [Znth_replace_Znth_Diff 0 st_ls idx p 0 ⟨hidx,hi⟩ ⟨hp.1,by omega⟩ (Ne.symm he)]
      exact hz p ⟨hp.1,by omega⟩
    · omega

theorem worker_Power2_0_1 : Power2 0 = 1 := rfl

theorem worker_STBasePrefix_write_base_step (l st_ls : List Int) (K n i : Int)
    (hl : Zlength l = n) (hs : Zlength st_ls = n*K) (hK : 0 < K) (hi : 0 ≤ i) (hin : i < n)
    (hiK : 0 ≤ i*K) (hiKn : i*K < n*K) (hb : STBasePrefix l st_ls K n i) :
    STBasePrefix l (replace_Znth (i*K) (Znth i l 0) st_ls) K n (i+1) := by
  intro p hp
  unfold STCellRangeMax
  simp only [Int.add_zero]
  by_cases he : p = i
  · rw [he,Znth_replace_Znth_Same 0 st_ls (i*K) _ ⟨hiK,by omega⟩]
    refine ⟨hi,by rw [worker_Power2_0_1]; omega,by rw [worker_Power2_0_1]; omega,i,⟨?_,?_⟩,rfl⟩
    · rw [worker_Power2_0_1]; omega
    · intro k hk
      have he : k = i := by rw [worker_Power2_0_1] at hk; omega
      subst k; exact le_refl _
  · have hpi : p < i := by omega
    rw [Znth_replace_Znth_Diff 0 st_ls (i*K) (p*K) _ ⟨hiK,by omega⟩ ⟨by nlinarith [hp.1],by nlinarith [hp.1]⟩ (by nlinarith)]
    simpa only [STCellRangeMax,Int.add_zero] using hb p ⟨hp.1,by omega⟩

theorem worker_STBasePrefix_complete_level1 (l st_ls : List Int) (K n i : Int)
    (hg : i ≥ n) (hle : i ≤ n) (hb : STBasePrefix l st_ls K n i) : STBuiltBeforeLevel l st_ls K n 1 := by
  intro p j hj
  have he : j = 0 := by omega
  subst j
  have hh : p+1 ≤ n := by simpa only [worker_Power2_0_1] using hj.2.2.2
  exact hb p ⟨hj.1,by omega⟩

theorem Power2_pos (k : Int) (hk : 0 ≤ k) : 0 < Power2 k := by
  rw [power_nat k hk]; positivity

theorem Power2_step (j : Int) (hj : 0 ≤ j) : Power2 j*2 = Power2 (j+1) := by
  rw [power_nat j hj,power_nat (j+1) (by omega),show (j+1).toNat = j.toNat+1 by omega,pow_succ]

theorem Power2_sub1_double (j : Int) (hj : 1 ≤ j) : Power2 j = Power2 (j-1)+Power2 (j-1) := by
  have h := Power2_step (j-1) (by omega)
  rw [show j-1+1 = j by omega] at h
  omega

theorem cell_index_mod (row K col : Int) (hK : 0 < K) (hc : 0 ≤ col ∧ col < K) :
    (row*K+col) % K = col := by
  rw [Int.add_comm,Int.add_mul_emod_self_right,Int.emod_eq_of_lt hc.1 hc.2]

theorem cell_index_col_eq (row1 row2 K col1 col2 : Int) (hK : 0 < K)
    (hc1 : 0 ≤ col1 ∧ col1 < K) (hc2 : 0 ≤ col2 ∧ col2 < K)
    (he : row1*K+col1 = row2*K+col2) : col1 = col2 := by
  have h := congrArg (fun z : Int => z % K) he
  simpa only [cell_index_mod row1 K col1 hK hc1,cell_index_mod row2 K col2 hK hc2] using h

theorem cell_index_diff_col_neq (row1 row2 K col1 col2 : Int) (hK : 0 < K)
    (hc1 : 0 ≤ col1 ∧ col1 < K) (hc2 : 0 ≤ col2 ∧ col2 < K) (hn : col1 ≠ col2) :
    row1*K+col1 ≠ row2*K+col2 := fun he => hn (cell_index_col_eq row1 row2 K col1 col2 hK hc1 hc2 he)

theorem cell_index_same_col_eq (row1 row2 K col : Int) (hK : 0 < K)
    (he : row1*K+col = row2*K+col) : row1 = row2 := by nlinarith

theorem cell_index_same_col_neq (row1 row2 K col : Int) (hK : 0 < K) (hn : row1 ≠ row2) :
    row1*K+col ≠ row2*K+col := fun he => hn (cell_index_same_col_eq row1 row2 K col hK he)

theorem STCellRangeMax_replace_other (l st : List Int) (K row col idx v : Int)
    (hc : STCellRangeMax l st K row col) (hi : 0 ≤ idx ∧ idx < Zlength st)
    (hcell : 0 ≤ row*K+col ∧ row*K+col < Zlength st) (hne : idx ≠ row*K+col) :
    STCellRangeMax l (replace_Znth idx v st) K row col := by
  unfold STCellRangeMax
  rw [Znth_replace_Znth_Diff 0 st idx (row*K+col) v hi hcell hne]
  exact hc

theorem STBuiltBeforeLevel_replace_level_cell (l st : List Int) (K n level row v : Int)
    (hb : STBuiltBeforeLevel l st K n level) (hl : level < K)
    (hi : 0 ≤ row*K+level ∧ row*K+level < Zlength st)
    (hr : ∀ row0 col, (0 ≤ row0 ∧ 0 ≤ col ∧ col < level ∧ row0+Power2 col ≤ n) →
      0 ≤ row0*K+col ∧ row0*K+col < Zlength st) :
    STBuiltBeforeLevel l (replace_Znth (row*K+level) v st) K n level := by
  intro row0 col hc
  exact STCellRangeMax_replace_other l st K row0 col (row*K+level) v (hb row0 col hc) hi (hr row0 col hc)
    (cell_index_diff_col_neq row row0 K level col (by omega) ⟨by omega,hl⟩ ⟨hc.2.1,by omega⟩ (by omega))

private theorem max_union_cover {P Q R : Int → Prop} (f : Int → Int) (a b : Int)
    (ha : max_value_of_subset (· ≤ ·) P f a) (hb : max_value_of_subset (· ≤ ·) Q f b)
    (hc : ∀ x, (P x ∨ Q x) ↔ R x) : max_value_of_subset (· ≤ ·) R f (max a b) := by
  obtain ⟨x,⟨hxp,hxm⟩,hx⟩ := ha
  obtain ⟨y,⟨hyq,hym⟩,hy⟩ := hb
  by_cases he : b ≤ a
  · rw [max_eq_left he]
    refine ⟨x,⟨(hc x).mp (Or.inl hxp),?_⟩,hx⟩
    intro z hz
    rcases (hc z).mpr hz with hp | hq
    · exact hxm z hp
    · have hh := hym z hq; dsimp only at hh ⊢; omega
  · rw [max_eq_right (by omega : a ≤ b)]
    refine ⟨y,⟨(hc y).mp (Or.inr hyq),?_⟩,hy⟩
    intro z hz
    rcases (hc z).mpr hz with hp | hq
    · have hh := hxm z hp; dsimp only at hh ⊢; omega
    · exact hym z hq

theorem RangeMaxValue_join_max (l : List Int) (i j half a b : Int) (hj : 1 ≤ j)
    (hh : half = Power2 (j-1)) (hl : RangeMaxValue l i (i+Power2 (j-1)) a)
    (hr : RangeMaxValue l (i+half) (i+half+Power2 (j-1)) b) :
    RangeMaxValue l i (i+Power2 j) (max a b) := by
  have hd := Power2_sub1_double j hj
  have hp := Power2_pos j (by omega)
  refine ⟨hl.1,by omega,by have := hr.2.2.1; omega,?_⟩
  apply max_union_cover (fun k => Znth k l 0) a b hl.2.2.2 hr.2.2.2
  intro x
  constructor
  · intro hx; rcases hx with hx | hx <;> omega
  · intro hx
    by_cases hlt : x < i+half
    · left; omega
    · right; omega

theorem RangeMaxValue_join_left (l : List Int) (i j half a b : Int) (hj : 1 ≤ j)
    (hh : half = Power2 (j-1)) (hab : a ≥ b) (hl : RangeMaxValue l i (i+Power2 (j-1)) a)
    (hr : RangeMaxValue l (i+half) (i+half+Power2 (j-1)) b) : RangeMaxValue l i (i+Power2 j) a := by
  simpa only [max_eq_left hab] using RangeMaxValue_join_max l i j half a b hj hh hl hr

theorem RangeMaxValue_join_right (l : List Int) (i j half a b : Int) (hj : 1 ≤ j)
    (hh : half = Power2 (j-1)) (hab : a < b) (hl : RangeMaxValue l i (i+Power2 (j-1)) a)
    (hr : RangeMaxValue l (i+half) (i+half+Power2 (j-1)) b) : RangeMaxValue l i (i+Power2 j) b := by
  simpa only [max_eq_right (le_of_lt hab)] using RangeMaxValue_join_max l i j half a b hj hh hl hr

theorem STCellRangeMax_extend_by_left_max (l st : List Int) (K i j half a b : Int)
    (hj : 1 ≤ j) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a ≥ b) (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STCellRangeMax l (replace_Znth (i*K+j) a st) K i j := by
  unfold STCellRangeMax at hl hr ⊢
  rw [← ha] at hl
  rw [← hb] at hr
  rw [Znth_replace_Znth_Same 0 st (i*K+j) a hi]
  exact RangeMaxValue_join_left l i j half a b hj hh hab hl hr

theorem STLevelPrefix_extend_by_left_max (l st : List Int) (K n j i half a b : Int)
    (hj : 1 ≤ j) (hjK : j < K) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a ≥ b) (hpref : STLevelPrefix l st K n j i)
    (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STLevelPrefix l (replace_Znth (i*K+j) a st) K n j (i+1) := by
  intro row hrow
  by_cases he : row = i
  · rw [he]
    exact STCellRangeMax_extend_by_left_max l st K i j half a b hj hh hi ha hb hab hl hr
  · have hri : row < i := by omega
    exact STCellRangeMax_replace_other l st K row j (i*K+j) a
      (hpref row ⟨hrow.1,hri,hrow.2.2⟩) hi ⟨by nlinarith [hrow.1],by nlinarith⟩
      (cell_index_same_col_neq i row K j (by omega) (Ne.symm he))

theorem STCellRangeMax_extend_by_right_max (l st : List Int) (K i j half a b : Int)
    (hj : 1 ≤ j) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a < b) (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STCellRangeMax l (replace_Znth (i*K+j) b st) K i j := by
  unfold STCellRangeMax at hl hr ⊢
  rw [← ha] at hl
  rw [← hb] at hr
  rw [Znth_replace_Znth_Same 0 st (i*K+j) b hi]
  exact RangeMaxValue_join_right l i j half a b hj hh hab hl hr

theorem STLevelPrefix_extend_by_right_max (l st : List Int) (K n j i half a b : Int)
    (hj : 1 ≤ j) (hjK : j < K) (hh : half = Power2 (j-1)) (hi : 0 ≤ i*K+j ∧ i*K+j < Zlength st)
    (ha : a = Znth (i*K+(j-1)) st 0) (hb : b = Znth ((i+half)*K+(j-1)) st 0)
    (hab : a < b) (hpref : STLevelPrefix l st K n j i)
    (hl : STCellRangeMax l st K i (j-1)) (hr : STCellRangeMax l st K (i+half) (j-1)) :
    STLevelPrefix l (replace_Znth (i*K+j) b st) K n j (i+1) := by
  intro row hrow
  by_cases he : row = i
  · rw [he]
    exact STCellRangeMax_extend_by_right_max l st K i j half a b hj hh hi ha hb hab hl hr
  · have hri : row < i := by omega
    exact STCellRangeMax_replace_other l st K row j (i*K+j) b
      (hpref row ⟨hrow.1,hri,hrow.2.2⟩) hi ⟨by nlinarith [hrow.1],by nlinarith⟩
      (cell_index_same_col_neq i row K j (by omega) (Ne.symm he))

theorem STLevelPrefix_exit_to_built_step (l st_ls : List Int) (K n j upto len : Int)
    (hb : STBuiltBeforeLevel l st_ls K n j) (hp : STLevelPrefix l st_ls K n j upto)
    (he : len = Power2 j) (hex : upto+len > n) : STBuiltBeforeLevel l st_ls K n (j+1) := by
  intro p q hc
  by_cases hq : q < j
  · exact hb p q ⟨hc.1,hc.2.1,hq,hc.2.2.2⟩
  · have heq : q = j := by omega
    subst q
    exact hp p ⟨hc.1,by omega,hc.2.2.2⟩

theorem Power2_step_query (k : Int) (hk : 0 ≤ k) : Power2 (k+1) = Power2 k*2 :=
  (Power2_step k hk).symm

theorem QueryLogBounds_init (K n left right : Int) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hp : n < Power2 K) (hl : 0 ≤ left) (hlr : left ≤ right) (hr : right < n) :
    QueryLogBounds K n (right-left+1) 0 1 := ⟨by omega,by omega,hK,hp,by omega,by omega,by omega⟩

theorem QueryLogLoopState_init (left right : Int) (hl : 0 ≤ left) (hlr : left ≤ right) :
    QueryLogLoopState (right-left+1) 0 1 := ⟨by omega,rfl,by rw [worker_Power2_0_1]; omega⟩

theorem QueryLogBounds_step (K n len k pow : Int) (hp : pow*2 ≤ len)
    (hb : QueryLogBounds K n len k pow) (hs : QueryLogLoopState len k pow) :
    QueryLogBounds K n len (k+1) (pow*2) := by
  obtain ⟨hln,hll,hK,hn,hk,hkK,hpow⟩ := hb
  have hnext : Power2 (k+1) ≤ len := by rw [Power2_step_query k hk,← hs.2.1]; exact hp
  have hknew : k+1 < K := by
    by_contra hnot
    have he : k+1 = K := by omega
    rw [he] at hnext; omega
  exact ⟨hln,hll,hK,hn,by omega,hknew,by omega⟩

theorem QueryLogLoopState_step (len k pow : Int) (hp : pow*2 ≤ len)
    (hs : QueryLogLoopState len k pow) : QueryLogLoopState len (k+1) (pow*2) := by
  exact ⟨by have := hs.1; omega,by rw [Power2_step_query k hs.1,← hs.2.1],
    by rw [Power2_step_query k hs.1,← hs.2.1]; exact hp⟩

theorem RangeMaxValue_sparse_query_max (l st_l : List Int) (K n len left right j pow a b : Int)
    (hlen : len = right-left+1) (ha : a = Znth (left*K+j) st_l 0)
    (hb : b = Znth ((right-pow+1)*K+j) st_l 0) (hq : QueryLogFinalState len j pow)
    (hcl : STCellRangeMax l st_l K left j) (hcr : STCellRangeMax l st_l K (right-pow+1) j) :
    RangeMaxValue l left (right+1) (max a b) := by
  obtain ⟨⟨hj,hpow,hpowle⟩,hnext⟩ := hq
  have hd : Power2 (j+1) = 2*pow := by rw [Power2_step_query j hj,← hpow]; ring
  unfold STCellRangeMax at hcl hcr
  rw [← ha,← hpow] at hcl
  rw [← hb,← hpow] at hcr
  have hright : right-pow+1+pow = right+1 := by omega
  rw [hright] at hcr
  refine ⟨hcl.1,by have := hcl.2.1; omega,hcr.2.2.1,?_⟩
  apply max_union_cover (fun k => Znth k l 0) a b hcl.2.2.2 hcr.2.2.2
  intro x
  constructor
  · intro hx; rcases hx with hx | hx <;> omega
  · intro hx
    by_cases hlt : x < left+pow
    · left; omega
    · right; omega

theorem RangeMaxValue_sparse_query_left (l st_l : List Int) (K n len left right j pow a b : Int)
    (hlen : len = right-left+1) (ha : a = Znth (left*K+j) st_l 0)
    (hb : b = Znth ((right-pow+1)*K+j) st_l 0) (hq : QueryLogFinalState len j pow)
    (hcl : STCellRangeMax l st_l K left j) (hcr : STCellRangeMax l st_l K (right-pow+1) j) (hab : a ≥ b) :
    RangeMaxValue l left (right+1) a := by
  simpa only [max_eq_left hab] using RangeMaxValue_sparse_query_max l st_l K n len left right j pow a b hlen ha hb hq hcl hcr

theorem RangeMaxValue_sparse_query_right (l st_l : List Int) (K n len left right j pow a b : Int)
    (hlen : len = right-left+1) (ha : a = Znth (left*K+j) st_l 0)
    (hb : b = Znth ((right-pow+1)*K+j) st_l 0) (hq : QueryLogFinalState len j pow)
    (hcl : STCellRangeMax l st_l K left j) (hcr : STCellRangeMax l st_l K (right-pow+1) j) (hab : a < b) :
    RangeMaxValue l left (right+1) b := by
  simpa only [max_eq_right (le_of_lt hab)] using RangeMaxValue_sparse_query_max l st_l K n len left right j pow a b hlen ha hb hq hcl hcr

end SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib
