import SetsClass.RelsDomain
import MaxMinLib.Interface
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length
import Init.Data.List.Nat.Range

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib
open AUXLib

def edit_zrange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

def edit_zrange_between (lo hi : Int) : List Int :=
  (List.range (hi-lo).toNat).map (fun off => lo+Int.ofNat off)

def EditBinaryList (xs : List Int) (n : Int) : Prop :=
  Zlength xs=n ∧ ∀ idx, (0 ≤ idx ∧ idx<n) → Znth idx xs 0=0 ∨ Znth idx xs 0=1

def edit_edge_open (t : List Int) (idx : Int) : Prop :=
  Znth (idx-1) t 0=1 ∧ Znth idx t 0=1

def edit_edge_openb (t : List Int) (idx : Int) : Bool :=
  decide (Znth (idx-1) t 0=1) && decide (Znth idx t 0=1)

def edit_all_edges_openb (t : List Int) (lo hi : Int) : Bool :=
  (edit_zrange_between lo hi).all (edit_edge_openb t)

def EditBlockStart (t : List Int) (idx start : Int) : Prop :=
  (0 ≤ start ∧ start ≤ idx) ∧ (∀ k, (start<k ∧ k≤idx) → edit_edge_open t k) ∧
    (start=0 ∨ ¬edit_edge_open t start)

def edit_block_startb (t : List Int) (idx start : Int) : Bool :=
  decide (0 ≤ start) && decide (start ≤ idx) && edit_all_edges_openb t (start+1) (idx+1) &&
    (decide (start=0) || !(edit_edge_openb t start))

def edit_bit_atb (xs : List Int) (idx bit : Int) : Bool := decide (Znth idx xs 0=bit)

def edit_count_bit_in_block_prefix (s t : List Int) (limit block bit : Int) : Int :=
  Int.ofNat ((edit_zrange (Zlength s)).filter (fun idx =>
    decide (idx<limit) && edit_block_startb t idx block && edit_bit_atb s idx bit)).length

def EditZeroPrefix (xs : List Int) (written : Int) : Prop :=
  Zlength xs=written ∧ ∀ idx, (0 ≤ idx ∧ idx<written) → Znth idx xs 0=0

def EditZeroFull (n : Int) (xs : List Int) : Prop :=
  Zlength xs=n ∧ ∀ idx, (0 ≤ idx ∧ idx<n) → Znth idx xs 0=0

def EditSegmentPrefix (t : List Int) (upto : Int) (seg : List Int) : Prop :=
  Zlength seg=upto ∧ ∀ idx, (0 ≤ idx ∧ idx<upto) → EditBlockStart t idx (Znth idx seg 0)

def EditCountsForPrefix (s t : List Int) (n upto : Int) (cnt0 cnt1 : List Int) : Prop :=
  Zlength cnt0=n ∧ Zlength cnt1=n ∧
  (∀ block, (0 ≤ block ∧ block<n) → Znth block cnt0 0=edit_count_bit_in_block_prefix s t upto block 0) ∧
  ∀ block, (0 ≤ block ∧ block<n) → Znth block cnt1 0=edit_count_bit_in_block_prefix s t upto block 1

def EditBuildState (s t : List Int) (n upto : Int) (seg cnt0 cnt1 : List Int) : Prop :=
  (0 ≤ upto ∧ upto ≤ n) ∧ EditBinaryList s n ∧ EditBinaryList t n ∧
    EditSegmentPrefix t upto seg ∧ EditCountsForPrefix s t n upto cnt0 cnt1

def EditCountBounds (n : Int) (cnt : List Int) : Prop :=
  Zlength cnt=n ∧ ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx cnt 0 ∧ Znth idx cnt 0 ≤ n

def EditScratchCountsBound (n : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  EditCountBounds n cnt10 ∧ EditCountBounds n cnt11 ∧ EditCountBounds n cnt20 ∧ EditCountBounds n cnt21

def edit_count_positions_in_seg_prefix (seg : List Int) (limit block : Int) : Int :=
  Int.ofNat ((edit_zrange (Zlength seg)).filter (fun idx => decide (idx<limit) && decide (Znth idx seg 0=block))).length

def EditGreedyRemainingTotals (seg1 seg2 : List Int) (i : Int)
    (full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  (∀ block, (0 ≤ block ∧ block<Zlength seg1) →
    Znth block cnt10 0+Znth block cnt11 0=Znth block full10 0+Znth block full11 0-edit_count_positions_in_seg_prefix seg1 i block) ∧
  ∀ block, (0 ≤ block ∧ block<Zlength seg2) →
    Znth block cnt20 0+Znth block cnt21 0=Znth block full20 0+Znth block full21 0-edit_count_positions_in_seg_prefix seg2 i block

def EditReachableString (s t out : List Int) (n : Int) : Prop :=
  EditBinaryList s n ∧ EditBinaryList t n ∧ EditBinaryList out n ∧
  ∀ block bit, (0 ≤ block ∧ block<n) → (bit=0 ∨ bit=1) →
    edit_count_bit_in_block_prefix out t n block bit=edit_count_bit_in_block_prefix s t n block bit

def edit_match_count (s1 s2 : List Int) (n : Int) : Int :=
  Int.ofNat ((edit_zrange n).filter (fun idx => decide (Znth idx s1 0=Znth idx s2 0))).length

def EditStringsFeasibleMatchCount (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  ∃ out1 out2, EditReachableString s1 t1 out1 n ∧ EditReachableString s2 t2 out2 n ∧ answer=edit_match_count out1 out2 n

def EditStringsMatchUpperBound (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  ∀ cand1 cand2 cand, EditReachableString s1 t1 cand1 n → EditReachableString s2 t2 cand2 n →
    cand=edit_match_count cand1 cand2 n → cand≤answer

def EditStringsMaximum (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  EditBinaryList s1 n ∧ EditBinaryList s2 n ∧ EditBinaryList t1 n ∧ EditBinaryList t2 n ∧
    EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer ∧ EditStringsMatchUpperBound s1 s2 t1 t2 n answer

inductive EditGreedyConsumedPrefix (seg1 seg2 full10 full11 full20 full21 : List Int) :
    Int → Int → List Int → List Int → List Int → List Int → Prop where
  | EditGreedyConsumedPrefix_start : EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21
      0 0 full10 full11 full20 full21
  | EditGreedyConsumedPrefix_common_zero (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      0<Znth a cnt10 0 → 0<Znth b cnt20 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) (ans+1)
        (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21
  | EditGreedyConsumedPrefix_common_one (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0) → 0<Znth a cnt11 0 → 0<Znth b cnt21 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) (ans+1)
        cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21)
  | EditGreedyConsumedPrefix_s1_zero_s2_one (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0) → ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0) →
      0<Znth a cnt10 0 → 0<Znth b cnt21 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) ans
        (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21)
  | EditGreedyConsumedPrefix_s1_one_s2_zero (i ans : Int) (cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int) :
      (0 ≤ i ∧ i<Zlength seg1) → Zlength seg2=Zlength seg1 → a=Znth i seg1 0 → b=Znth i seg2 0 →
      ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0) → ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0) →
      ¬(0<Znth a cnt10 0) → 0<Znth a cnt11 0 → 0<Znth b cnt20 0 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 →
      EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 (i+1) ans
        cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21

@[match_pattern] abbrev EditGreedyConsumedPrefix_start (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_start seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_common_zero (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_common_zero seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_common_one (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_common_one seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_s1_zero_s2_one (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_s1_zero_s2_one seg1 seg2 full10 full11 full20 full21
@[match_pattern] abbrev EditGreedyConsumedPrefix_s1_one_s2_zero (seg1 seg2 full10 full11 full20 full21 : List Int) :=
  @EditGreedyConsumedPrefix.EditGreedyConsumedPrefix_s1_one_s2_zero seg1 seg2 full10 full11 full20 full21

def EditGreedyFinalOptimality (s1 s2 t1 t2 : List Int) (n answer : Int) : Prop :=
  EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer ∧ EditStringsMatchUpperBound s1 s2 t1 t2 n answer

def EditGreedyPrefixState (s1 s2 t1 t2 : List Int) (n i answer : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  (0 ≤ i ∧ i≤n) ∧ (0 ≤ answer ∧ answer≤i) ∧ ∃ full10 full11 full20 full21,
    EditBuildState s1 t1 n n seg1 full10 full11 ∧ EditBuildState s2 t2 n n seg2 full20 full21 ∧
    EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 ∧
    EditGreedyRemainingTotals seg1 seg2 i full10 full11 full20 full21 cnt10 cnt11 cnt20 cnt21 ∧
    EditGreedyConsumedPrefix seg1 seg2 full10 full11 full20 full21 i answer cnt10 cnt11 cnt20 cnt21

def EditGreedyCurrentAvailability (n i : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  (0 ≤ i ∧ i<n) → (0 ≤ Znth i seg1 0 ∧ Znth i seg1 0<n) ∧ (0 ≤ Znth i seg2 0 ∧ Znth i seg2 0<n) ∧
    0<Znth (Znth i seg1 0) cnt10 0+Znth (Znth i seg1 0) cnt11 0 ∧
    0<Znth (Znth i seg2 0) cnt20 0+Znth (Znth i seg2 0) cnt21 0

def EditGreedyCompletedMaximumFacts (s1 s2 t1 t2 : List Int) (n : Int) : Prop :=
  ∀ answer seg1 seg2 cnt10 cnt11 cnt20 cnt21, EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 →
    EditGreedyFinalOptimality s1 s2 t1 t2 n answer

def EditGreedyCompletedStateFacts (s1 s2 t1 t2 : List Int) (n answer : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) : Prop :=
  EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 ∧ EditGreedyFinalOptimality s1 s2 t1 t2 n answer

theorem EditStringsMaximum_intro (s1 s2 t1 t2 : List Int) (n answer : Int)
    (hs1 : EditBinaryList s1 n) (hs2 : EditBinaryList s2 n) (ht1 : EditBinaryList t1 n) (ht2 : EditBinaryList t2 n)
    (hf : EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer) (hu : EditStringsMatchUpperBound s1 s2 t1 t2 n answer) :
    EditStringsMaximum s1 s2 t1 t2 n answer := ⟨hs1, hs2, ht1, ht2, hf, hu⟩

theorem EditStringsMaximum_feasible (s1 s2 t1 t2 : List Int) (n answer : Int)
    (h : EditStringsMaximum s1 s2 t1 t2 n answer) : EditStringsFeasibleMatchCount s1 s2 t1 t2 n answer := h.2.2.2.2.1

theorem EditStringsMaximum_upper_bound (s1 s2 t1 t2 : List Int) (n answer : Int)
    (h : EditStringsMaximum s1 s2 t1 t2 n answer) : EditStringsMatchUpperBound s1 s2 t1 t2 n answer := h.2.2.2.2.2

theorem EditGreedyPrefixState_final_optimality (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditGreedyFinalOptimality s1 s2 t1 t2 n answer := hf answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs

theorem EditGreedyPrefixState_completed_maximum (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n) : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n := hf

theorem EditGreedyPrefixState_completed_state_facts (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditGreedyCompletedStateFacts s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 :=
  ⟨hs, hf answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs⟩

theorem EditGreedyCompletedStateFacts_to_Maximum (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hf : EditGreedyCompletedStateFacts s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditStringsMaximum s1 s2 t1 t2 n answer := by
  obtain ⟨_, _, _, _, hb1, hb2, _⟩ := hf.1.2.2
  exact ⟨hb1.2.1, hb2.2.1, hb1.2.2.1, hb2.2.2.1, hf.2.1, hf.2.2⟩

theorem EditGreedyCompletedMaximumFacts_to_Maximum (s1 s2 t1 t2 : List Int) (n answer : Int)
    (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (hf : EditGreedyCompletedMaximumFacts s1 s2 t1 t2 n)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditStringsMaximum s1 s2 t1 t2 n answer :=
  EditGreedyCompletedStateFacts_to_Maximum s1 s2 t1 t2 n answer seg1 seg2 cnt10 cnt11 cnt20 cnt21
    ⟨hs, hf answer seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs⟩

theorem edit_zrange_between_in__build_s1_segments_counts (lo hi k : Int) (hh : lo ≤ hi) :
    k ∈ edit_zrange_between lo hi ↔ lo ≤ k ∧ k<hi := by
  simp only [edit_zrange_between, List.mem_map]
  constructor
  · rintro ⟨off, hoff, he⟩
    have ho := List.mem_range.mp hoff
    simp only [Int.ofNat_eq_coe] at he
    omega
  · intro hk
    refine ⟨(k-lo).toNat, List.mem_range.mpr (by omega), ?_⟩
    simp only [Int.ofNat_eq_coe]
    omega

theorem edit_edge_openb_true_iff__build_s1_segments_counts (t : List Int) (idx : Int) :
    edit_edge_openb t idx=true ↔ edit_edge_open t idx := by simp [edit_edge_openb, edit_edge_open]

theorem edit_all_edges_openb_true_iff__build_s1_segments_counts (t : List Int) (lo hi : Int) (hh : lo ≤ hi) :
    edit_all_edges_openb t lo hi=true ↔ ∀ k, (lo ≤ k ∧ k<hi) → edit_edge_open t k := by
  simp only [edit_all_edges_openb, List.all_eq_true]
  constructor
  · intro h k hk
    exact (edit_edge_openb_true_iff__build_s1_segments_counts t k).mp (h k ((edit_zrange_between_in__build_s1_segments_counts lo hi k hh).mpr hk))
  · intro h k hk
    exact (edit_edge_openb_true_iff__build_s1_segments_counts t k).mpr (h k ((edit_zrange_between_in__build_s1_segments_counts lo hi k hh).mp hk))

theorem edit_block_startb_true_iff__build_s1_segments_counts (t : List Int) (idx start : Int) :
    edit_block_startb t idx start=true ↔ EditBlockStart t idx start := by
  simp only [edit_block_startb, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨hs0, hsi⟩, hall⟩, hend⟩
    refine ⟨⟨hs0,hsi⟩, ?_, ?_⟩
    · intro k hk
      exact (edit_all_edges_openb_true_iff__build_s1_segments_counts t (start+1) (idx+1) (by omega)).mp hall k (by omega)
    · rcases hend with hz|hn
      · exact Or.inl hz
      · right; intro ho
        have := (edit_edge_openb_true_iff__build_s1_segments_counts t start).mpr ho
        simp_all
  · rintro ⟨hs, hall, hend⟩
    refine ⟨⟨⟨hs.1, hs.2⟩, ?_⟩, ?_⟩
    · apply (edit_all_edges_openb_true_iff__build_s1_segments_counts t (start+1) (idx+1) (by omega)).mpr
      intro k hk; exact hall k (by omega)
    · rcases hend with hz|hn
      · exact Or.inl hz
      · right
        cases he : edit_edge_openb t start with
        | false => rfl
        | true => exact False.elim (hn ((edit_edge_openb_true_iff__build_s1_segments_counts t start).mp he))

theorem EditBlockStart_unique__build_s1_segments_counts (t : List Int) (idx a b : Int)
    (ha : EditBlockStart t idx a) (hb : EditBlockStart t idx b) : a=b := by
  obtain ⟨ha0, haedge, haend⟩ := ha
  obtain ⟨hb0, hbedge, hbend⟩ := hb
  by_cases hab : a<b
  · have he := haedge b (by omega)
    rcases hbend with hz|hn <;> first | omega | exact False.elim (hn he)
  · by_cases hba : b<a
    · have he := hbedge a (by omega)
      rcases haend with hz|hn <;> first | omega | exact False.elim (hn he)
    · omega

theorem edit_zrange_in__build_s1_segments_counts (n k : Int) (hn : 0 ≤ n) :
    k ∈ edit_zrange n ↔ 0 ≤ k ∧ k<n := by
  simp only [edit_zrange, List.mem_map]
  constructor
  · rintro ⟨off, hoff, he⟩
    have ho := List.mem_range.mp hoff
    simp only [Int.ofNat_eq_coe] at he
    omega
  · intro hk
    exact ⟨k.toNat, List.mem_range.mpr (by omega), by simp only [Int.ofNat_eq_coe]; omega⟩

theorem edit_NoDup_map_inj__greedy_common_and_mismatch_steps {A B : Type} (f : A → B) (l : List A)
    (hinj : ∀ x y, x ∈ l → y ∈ l → f x=f y → x=y) (hn : NoDup l) : NoDup (l.map f) := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    have hnc := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (fun a b ha hb he => hinj a b (by simp [ha]) (by simp [hb]) he) hnc.2⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    have hxy := hinj y x (by simp [hy]) (by simp) he
    exact hnc.1 (hxy ▸ hy)

theorem edit_zrange_NoDup__build_s1_segments_counts (n : Int) : NoDup (edit_zrange n) :=
  edit_NoDup_map_inj__greedy_common_and_mismatch_steps Int.ofNat (List.range n.toNat)
    (by intro x y hx hy he; exact Int.ofNat.inj he) (List.nodup_range)

theorem NoDup_filter_bool__build_s1_segments_counts (A : Type) (p : A → Bool) (xs : List A)
    (hn : NoDup xs) : NoDup (xs.filter p) := List.filter_sublist.nodup hn

private theorem nodup_subset_length (xs ys : List Int) (hn : xs.Nodup)
    (hsub : ∀ x, x∈xs → x∈ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hnc := List.nodup_cons.mp hn
    have hxm := hsub x (by simp)
    have h := ih (ys.erase x) hnc.2 (by
      intro y hy
      exact (List.mem_erase_of_ne (by intro he; subst y; exact hnc.1 hy)).mpr (hsub y (by simp [hy])))
    rw [List.length_erase_of_mem hxm] at h
    simp only [List.length_cons]
    have hyn : 0<ys.length := List.length_pos_of_mem hxm
    omega

theorem NoDup_zlist_range_length__build_s1_segments_counts (limit : Int) (picks : List Int)
    (hl : 0 ≤ limit) (hn : NoDup picks) (hf : Forall (fun i => 0 ≤ i ∧ i<limit) picks) :
    Int.ofNat picks.length ≤ limit := by
  have h := nodup_subset_length picks (edit_zrange limit) hn (by
    intro x hx
    exact (edit_zrange_in__build_s1_segments_counts limit x hl).mpr (hf.mem hx))
  simp only [edit_zrange, List.length_map, List.length_range] at h
  simp only [Int.ofNat_eq_coe]
  omega

theorem edit_count_bit_in_block_prefix_bound__build_s1_segments_counts (s t : List Int) (limit block bit : Int)
    (hl : 0 ≤ limit ∧ limit ≤ Zlength s) :
    0 ≤ edit_count_bit_in_block_prefix s t limit block bit ∧ edit_count_bit_in_block_prefix s t limit block bit ≤ limit := by
  unfold edit_count_bit_in_block_prefix
  refine ⟨by simp only [Int.ofNat_eq_coe]; omega, NoDup_zlist_range_length__build_s1_segments_counts limit _ hl.1
    (NoDup_filter_bool__build_s1_segments_counts Int _ _ (edit_zrange_NoDup__build_s1_segments_counts _)) ?_⟩
  apply Forall.iff_forall_mem.mpr
  intro idx hi
  obtain ⟨hmem, hpred⟩ := List.mem_filter.mp hi
  have hr := (edit_zrange_in__build_s1_segments_counts (Zlength s) idx (Zlength_nonneg s)).mp hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  exact ⟨hr.1, hpred.1.1⟩

theorem filter_limit_succ_once__build_s1_segments_counts (xs : List Int) (i : Int) (Q : Int → Bool)
    (hn : NoDup xs) (him : i∈xs) (htr : ∀ x, x∈xs → x<i ∨ x=i ∨ i<x) :
    (xs.filter (fun idx => decide (idx<i+1) && Q idx)).length =
      (xs.filter (fun idx => decide (idx<i) && Q idx)).length + (if Q i then 1 else 0) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    have hnc := List.nodup_cons.mp hn
    by_cases hxi : x=i
    · subst x
      have hf : xs.filter (fun idx => decide (idx<i+1) && Q idx)=xs.filter (fun idx => decide (idx<i) && Q idx) := by
        apply List.filter_congr
        intro j hj
        have hji : j≠i := by intro he; subst j; exact hnc.1 hj
        have he : decide (j<i+1)=decide (j<i) := by
          by_cases hjlt : j<i
          · simp only [decide_eq_true (show j<i+1 by omega), decide_eq_true hjlt]
          · simp only [decide_eq_false (show ¬j<i+1 by omega), decide_eq_false hjlt]
        rw [he]
      simp only [List.filter_cons, decide_eq_true (show i<i+1 by omega), Bool.true_and,
        decide_eq_false (show ¬i<i by omega), Bool.false_and, Bool.false_eq_true, if_false, hf]
      cases hq : Q i <;> simp [hq, List.length_cons, Nat.add_comm]
    · have hit : i∈xs := by simpa only [List.mem_cons, show i≠x from Ne.symm hxi, false_or] using him
      have h := ih hnc.2 hit (fun a ha => htr a (by simp [ha]))
      have he : decide (x<i+1)=decide (x<i) := by
        by_cases hxlt : x<i
        · simp only [decide_eq_true (show x<i+1 by omega), decide_eq_true hxlt]
        · simp only [decide_eq_false (show ¬x<i+1 by omega), decide_eq_false hxlt]
      simp only [List.filter_cons, he]
      cases hb : (decide (x<i) && Q x) <;> simp only [hb, Bool.false_eq_true, Bool.true_eq, if_false, if_true, List.length_cons] <;> omega

theorem edit_count_bit_in_block_prefix_succ__build_s1_segments_counts (s t : List Int) (i block bit : Int)
    (hi : 0 ≤ i ∧ i<Zlength s) :
    edit_count_bit_in_block_prefix s t (i+1) block bit=edit_count_bit_in_block_prefix s t i block bit+
      (if edit_block_startb t i block && edit_bit_atb s i bit then 1 else 0) := by
  have h := filter_limit_succ_once__build_s1_segments_counts (edit_zrange (Zlength s)) i
    (fun idx => edit_block_startb t idx block && edit_bit_atb s idx bit)
    (edit_zrange_NoDup__build_s1_segments_counts _) ((edit_zrange_in__build_s1_segments_counts _ i (Zlength_nonneg s)).mpr hi)
    (by intros; omega)
  unfold edit_count_bit_in_block_prefix
  simp only [Bool.and_assoc] at h ⊢
  rw [h]
  simp only [Int.ofNat_eq_coe, Int.natCast_add]
  split <;> rfl

private theorem edit_count_zero (s t : List Int) (block bit : Int) :
    edit_count_bit_in_block_prefix s t 0 block bit=0 := by
  unfold edit_count_bit_in_block_prefix
  have he : (edit_zrange (Zlength s)).filter (fun idx => decide (idx<0) && edit_block_startb t idx block && edit_bit_atb s idx bit)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro idx hi
    have hr := (edit_zrange_in__build_s1_segments_counts _ idx (Zlength_nonneg s)).mp hi
    simp [show ¬idx<0 by omega]
  rw [he]
  rfl

theorem EditZeroPrefix_snoc_zero__zeroing_and_base_build (xs : List Int) (i : Int)
    (hp : EditZeroPrefix xs i) : EditZeroPrefix (xs++[0]) (i+1) := by
  refine ⟨by simp only [Zlength_app, Zlength_cons, Zlength_nil, hp.1]; omega, ?_⟩
  intro idx hi
  by_cases hlt : idx<i
  · have he : Znth idx (xs++[0]) 0=Znth idx xs 0 := ListLib.app_Znth1 0 xs [0] idx (by
      change 0 ≤ idx ∧ idx<Zlength xs
      have := hp.1
      omega)
    rw [he]
    exact hp.2 idx (by omega)
  · have he : idx=Zlength xs := by have := hp.1; omega
    rw [he, app_Znth2 0 xs [0] (Zlength xs) (Int.le_refl _), Int.sub_self]
    rfl

theorem EditZeroPrefix_to_full_at_bound__zeroing_and_base_build (n : Int) (xs : List Int) (i : Int)
    (hi : i≥n) (hin : i≤n) (hp : EditZeroPrefix xs i) : EditZeroFull n xs := by
  have : i=n := by omega
  subst i
  exact hp

theorem EditZeroFull_count_bound__zeroing_and_base_build (n : Int) (xs : List Int)
    (hn : 0 ≤ n) (hz : EditZeroFull n xs) : EditCountBounds n xs := by
  refine ⟨hz.1, ?_⟩
  intro idx hi
  rw [hz.2 idx hi]
  exact ⟨Int.le_refl _, hn⟩

theorem EditZeroFull_scratch_bound__zeroing_and_base_build (n : Int) (cnt10 cnt11 cnt20 cnt21 : List Int)
    (hn : 0 ≤ n) (h10 : EditZeroFull n cnt10) (h11 : EditZeroFull n cnt11)
    (h20 : EditZeroFull n cnt20) (h21 : EditZeroFull n cnt21) : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21 :=
  ⟨EditZeroFull_count_bound__zeroing_and_base_build n cnt10 hn h10, EditZeroFull_count_bound__zeroing_and_base_build n cnt11 hn h11,
    EditZeroFull_count_bound__zeroing_and_base_build n cnt20 hn h20, EditZeroFull_count_bound__zeroing_and_base_build n cnt21 hn h21⟩

theorem edit_filter_ltb_one_seq_from__zeroing_and_base_build (start len : Nat) (pred1 pred2 : Int → Bool)
    (hs : 1 ≤ Int.ofNat start) :
    ((List.range' start len).map Int.ofNat).filter (fun idx => (decide (idx<1) && pred1 idx) && pred2 idx)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro idx hi
  obtain ⟨off, hoff, he⟩ := List.mem_map.mp hi
  have ho := List.mem_range'.mp hoff
  simp only [Int.ofNat_eq_coe] at hs he
  simp [show ¬idx<1 by omega]

theorem edit_count_bit_in_block_prefix_one__zeroing_and_base_build (s t : List Int) (n block bit : Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hb : 0 ≤ block ∧ block<n) :
    edit_count_bit_in_block_prefix s t 1 block bit =
      if block=0 then if Znth 0 s 0=bit then 1 else 0 else 0 := by
  have h := edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t 0 block bit (by omega)
  simp only [edit_count_zero, Int.zero_add] at h
  rw [h]
  by_cases hz : block=0
  · subst block
    simp only [edit_block_startb, edit_all_edges_openb, edit_zrange_between, edit_bit_atb]
    simp
  · have hbpos : ¬block≤0 := by omega
    simp only [edit_block_startb, decide_eq_false hbpos, Bool.and_false, Bool.false_and, if_neg hz]
    rfl

private theorem replace_read (xs : List Int) (i j v : Int)
    (hi : 0 ≤ i ∧ i<Zlength xs) (hj : 0 ≤ j ∧ j<Zlength xs) :
    Znth j (replace_Znth i v xs) 0=if j=i then v else Znth j xs 0 := by
  by_cases h : j=i
  · subst j; simp [Znth_replace_Znth_Same 0 xs i v hi]
  · rw [if_neg h, Znth_replace_Znth_Diff 0 xs i j v hi hj (Ne.symm h)]

private theorem bounds_update (n : Int) (xs : List Int) (idx v : Int)
    (hb : EditCountBounds n xs) (hi : 0 ≤ idx ∧ idx<n) (hv : 0 ≤ v ∧ v≤n) :
    EditCountBounds n (replace_Znth idx v xs) := by
  refine ⟨by simpa only [Zlength_replace_Znth] using hb.1, ?_⟩
  intro j hj
  rw [replace_read xs idx j v (by simpa only [hb.1] using hi) (by simpa only [hb.1] using hj)]
  split
  · exact hv
  · exact hb.2 j hj

theorem EditCountBounds_replace_zero_inc__zeroing_and_base_build (n : Int) (xs : List Int)
    (hn : 1 ≤ n) (hz : EditZeroFull n xs) : EditCountBounds n (replace_Znth 0 (Znth 0 xs 0+1) xs) := by
  apply bounds_update n xs 0 _ (EditZeroFull_count_bound__zeroing_and_base_build n xs (by omega) hz) (by omega)
  rw [hz.2 0 (by omega)]
  omega

theorem EditScratchCountsBound_replace_c11_zero_inc__zeroing_and_base_build (n : Int) (c10 c11 c20 c21 : List Int)
    (hn : 1 ≤ n) (hs : EditScratchCountsBound n c10 c11 c20 c21) (hz : EditZeroFull n c11) :
    EditScratchCountsBound n c10 (replace_Znth 0 (Znth 0 c11 0+1) c11) c20 c21 :=
  ⟨hs.1, EditCountBounds_replace_zero_inc__zeroing_and_base_build n c11 hn hz, hs.2.2⟩

theorem EditScratchCountsBound_replace_c10_zero_inc__zeroing_and_base_build (n : Int) (c10 c11 c20 c21 : List Int)
    (hn : 1 ≤ n) (hs : EditScratchCountsBound n c10 c11 c20 c21) (hz : EditZeroFull n c10) :
    EditScratchCountsBound n (replace_Znth 0 (Znth 0 c10 0+1) c10) c11 c20 c21 :=
  ⟨EditCountBounds_replace_zero_inc__zeroing_and_base_build n c10 hn hz, hs.2⟩

theorem EditBinaryList_from_bounds__zeroing_and_base_build (xs : List Int) (n : Int)
    (hlen : Zlength xs=n) (hb : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0≤1) : EditBinaryList xs n := by
  refine ⟨hlen, ?_⟩
  intro idx hi
  have := hb idx hi
  omega

theorem EditSegmentPrefix_one_zero__zeroing_and_base_build (t sg : List Int)
    (hlen : Zlength sg=1) (hz : Znth 0 sg 0=0) : EditSegmentPrefix t 1 sg := by
  refine ⟨hlen, ?_⟩
  intro idx hi
  have : idx=0 := by omega
  subst idx
  rw [hz]
  exact ⟨⟨Int.le_refl _,Int.le_refl _⟩, (by intros; omega), Or.inl rfl⟩

private theorem count_initial (s t : List Int) (n : Int) (cnt0 cnt1 : List Int) (bit : Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hbit : bit=0 ∨ bit=1) (hv : Znth 0 s 0=bit)
    (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditCountsForPrefix s t n 1
      (if bit=0 then replace_Znth 0 (Znth 0 cnt0 0+1) cnt0 else cnt0)
      (if bit=1 then replace_Znth 0 (Znth 0 cnt1 0+1) cnt1 else cnt1) := by
  have hn0 : 0 ≤ (0:Int) ∧ 0<n := by omega
  rcases hbit with rfl|rfl <;>
    (try simp only [ite_true, ite_false]) <;>
    refine ⟨by simpa only [Zlength_replace_Znth] using h0.1, by simpa only [Zlength_replace_Znth] using h1.1, ?_, ?_⟩
  all_goals
    intro block hblock
    rw [edit_count_bit_in_block_prefix_one__zeroing_and_base_build s t n block _ hn hlen hblock]
  all_goals
    first
    | rw [replace_read _ 0 block _ (by simpa only [h0.1] using hn0) (by simpa only [h0.1] using hblock)]
    | rw [replace_read _ 0 block _ (by simpa only [h1.1] using hn0) (by simpa only [h1.1] using hblock)]
    | skip
  all_goals simp only [h0.2 _ hblock, h1.2 _ hblock, h0.2 0 hn0, h1.2 0 hn0, hv]; split <;> simp_all
  all_goals first | exact h0.2 block hblock | exact h1.2 block hblock

theorem EditCountsForPrefix_initial_one__zeroing_and_base_build (s t : List Int) (n : Int) (cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hb : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hv : Znth 0 s 0≠0) (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditCountsForPrefix s t n 1 cnt0 (replace_Znth 0 (Znth 0 cnt1 0+1) cnt1) := by
  have hz : Znth 0 s 0=1 := by have := hb 0 (by omega); omega
  simpa using count_initial s t n cnt0 cnt1 1 hn hlen (Or.inr rfl) hz h0 h1

theorem EditCountsForPrefix_initial_zero__zeroing_and_base_build (s t : List Int) (n : Int) (cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hlen : Zlength s=n) (hv : Znth 0 s 0=0) (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditCountsForPrefix s t n 1 (replace_Znth 0 (Znth 0 cnt0 0+1) cnt0) cnt1 := by
  simpa using count_initial s t n cnt0 cnt1 0 hn hlen (Or.inl rfl) hv h0 h1

theorem EditBuildState_initial_s1_one__zeroing_and_base_build (s t : List Int) (n : Int) (sg cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hv : Znth 0 s 0≠0) (hg : Zlength sg=1) (hgz : Znth 0 sg 0=0)
    (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditBuildState s t n 1 sg cnt0 (replace_Znth 0 (Znth 0 cnt1 0+1) cnt1) :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,
    EditSegmentPrefix_one_zero__zeroing_and_base_build t sg hg hgz,
    EditCountsForPrefix_initial_one__zeroing_and_base_build s t n cnt0 cnt1 hn hs hbs hv h0 h1⟩

theorem EditBuildState_initial_s1_zero__zeroing_and_base_build (s t : List Int) (n : Int) (sg cnt0 cnt1 : List Int)
    (hn : 1 ≤ n) (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hv : Znth 0 s 0=0) (hg : Zlength sg=1) (hgz : Znth 0 sg 0=0)
    (h0 : EditZeroFull n cnt0) (h1 : EditZeroFull n cnt1) :
    EditBuildState s t n 1 sg (replace_Znth 0 (Znth 0 cnt0 0+1) cnt0) cnt1 :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,
    EditSegmentPrefix_one_zero__zeroing_and_base_build t sg hg hgz,
    EditCountsForPrefix_initial_zero__zeroing_and_base_build s t n cnt0 cnt1 hn hs hv h0 h1⟩

private theorem snoc_last {A : Type} (xs : List A) (v d : A) (i : Int) (hi : Zlength xs=i) :
    Znth i (xs++[v]) d=v := by
  subst i
  rw [app_Znth2 d xs [v] (Zlength xs) (Int.le_refl _), Int.sub_self]
  rfl

theorem edit_snoc_Znth_last__build_s1_segments_counts (xs : List Int) (i x d : Int)
    (hi : Zlength xs=i) (hn : 0 ≤ i) : Znth i (xs++[x]) d=x := snoc_last xs x d i hi

private theorem segment_snoc (t : List Int) (i : Int) (sg : List Int) (v : Int)
    (hg : EditSegmentPrefix t i sg) (hi : 0 ≤ i) (hv : EditBlockStart t i v) :
    EditSegmentPrefix t (i+1) (sg++[v]) := by
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil,hg.1]; omega, ?_⟩
  intro idx hidx
  by_cases hlt : idx<i
  · have he : Znth idx (sg++[v]) 0=Znth idx sg 0 := ListLib.app_Znth1 0 sg [v] idx (by change 0≤idx∧idx<Zlength sg; rw[hg.1]; omega)
    rw [he]
    exact hg.2 idx (by omega)
  · have : idx=i := by omega
    subst idx
    rw [snoc_last sg v 0 i hg.1]
    exact hv

theorem EditSegmentPrefix_extend_new__build_s1_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 0 ≤ i) (he : ¬edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[i]) :=
  segment_snoc t i sg i hg hi ⟨⟨hi,Int.le_refl _⟩,(by intros; omega),Or.inr he⟩

theorem EditSegmentPrefix_extend_open__build_s1_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 1 ≤ i) (he : edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[Znth (i-1) sg 0]) := by
  have hb := hg.2 (i-1) (by omega)
  apply segment_snoc t i sg _ hg (by omega)
  refine ⟨⟨hb.1.1,by have := hb.1.2; omega⟩,?_,hb.2.2⟩
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using he
  · exact hb.2.1 k (by omega)

theorem EditSegmentPrefix_last_block_bounds__build_s1_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 1 ≤ i) : 0 ≤ Znth (i-1) sg 0 ∧ Znth (i-1) sg 0<i := by
  have hb := (hg.2 (i-1) (by omega)).1
  omega

private theorem block_bool_at (t : List Int) (i block k : Int) (hb : EditBlockStart t i block) :
    edit_block_startb t i k=decide (k=block) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, edit_block_startb_true_iff__build_s1_segments_counts]
  constructor
  · intro hk; exact EditBlockStart_unique__build_s1_segments_counts t i k block hk hb
  · intro hk; simpa only [hk] using hb

private theorem count_extend_single (s t : List Int) (n i block bit : Int) (cnt : List Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hb : EditBlockStart t i block)
    (hc : Zlength cnt=n) (hv : ∀ k, (0 ≤ k ∧ k<n) → Znth k cnt 0=edit_count_bit_in_block_prefix s t i k bit) :
    ∀ k, (0 ≤ k ∧ k<n) →
      Znth k (if Znth i s 0=bit then replace_Znth block (Znth block cnt 0+1) cnt else cnt) 0=
        edit_count_bit_in_block_prefix s t (i+1) k bit := by
  intro k hk
  have hblock : 0 ≤ block ∧ block<n := by have := hb.1; omega
  rw [edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t i k bit (by simpa only [hs] using hi),
    block_bool_at t i block k hb]
  unfold edit_bit_atb
  by_cases hbit : Znth i s 0=bit
  · rw [if_pos hbit, replace_read cnt block k _ (by simpa only [hc] using hblock) (by simpa only [hc] using hk)]
    by_cases he : k=block
    · subst k; simp [hv block hblock,hbit]
    · simp [he,hbit,hv k hk]
  · simp [hbit,hv k hk]

private theorem counts_extend (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block bit : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hblock : block=Znth i sg 0)
    (hbit : bit=0 ∨ bit=1) (hv : Znth i s 0=bit) :
    EditCountsForPrefix s t n (i+1)
      (if bit=0 then replace_Znth block (Znth block cnt0 0+1) cnt0 else cnt0)
      (if bit=1 then replace_Znth block (Znth block cnt1 0+1) cnt1 else cnt1) := by
  have hb : EditBlockStart t i block := by rw [hblock]; exact hg.2 i (by omega)
  have h0 := count_extend_single s t n i block 0 cnt0 hs hi hb hc.1 hc.2.2.1
  have h1 := count_extend_single s t n i block 1 cnt1 hs hi hb hc.2.1 hc.2.2.2
  rcases hbit with rfl|rfl <;> simp only [hv,ite_true,ite_false] at h0 h1 ⊢ <;>
    exact ⟨by simpa only [Zlength_replace_Znth] using hc.1, by simpa only [Zlength_replace_Znth] using hc.2.1,h0,h1⟩

theorem EditCountsForPrefix_extend_one__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i sg 0) (hv : Znth i s 0≠0)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1) :
    EditCountsForPrefix s t n (i+1) cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) := by
  have hbit : Znth i s 0=1 := by have := hbs i hi; omega
  simpa using counts_extend s t n i sg cnt0 cnt1 block 1 hs hi hg hc hb (Or.inr rfl) hbit

theorem EditCountsForPrefix_extend_zero__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i sg 0) (hv : Znth i s 0=0) :
    EditCountsForPrefix s t n (i+1) (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 := by
  simpa using counts_extend s t n i sg cnt0 cnt1 block 0 hs hi hg hc hb (Or.inl rfl) hv

private theorem bound_inc (s t : List Int) (n i : Int) (cnt : List Int) (block bit : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hb : 0 ≤ block ∧ block<n)
    (hc : Znth block cnt 0=edit_count_bit_in_block_prefix s t i block bit) (hbound : EditCountBounds n cnt) :
    EditCountBounds n (replace_Znth block (Znth block cnt 0+1) cnt) := by
  apply bounds_update n cnt block _ hbound hb
  have h := edit_count_bit_in_block_prefix_bound__build_s1_segments_counts s t i block bit (by omega)
  omega

theorem EditScratchCountsBound_inc_second__build_s1_segments_counts (s t : List Int) (n i : Int) (cnt0 cnt1 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : 0 ≤ block ∧ block<n) (hbound : EditScratchCountsBound n cnt0 cnt1 cnt20 cnt21) :
    EditScratchCountsBound n cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) cnt20 cnt21 :=
  ⟨hbound.1,bound_inc s t n i cnt1 block 1 hs hi hb (hc.2.2.2 block hb) hbound.2.1,hbound.2.2⟩

theorem EditScratchCountsBound_inc_first__build_s1_segments_counts (s t : List Int) (n i : Int) (cnt0 cnt1 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0 ≤ i ∧ i<n) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : 0 ≤ block ∧ block<n) (hbound : EditScratchCountsBound n cnt0 cnt1 cnt20 cnt21) :
    EditScratchCountsBound n (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 cnt20 cnt21 :=
  ⟨bound_inc s t n i cnt0 block 0 hs hi hb (hc.2.2.1 block hb) hbound.1,hbound.2⟩

theorem EditBuildState_extend_one__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : block=Znth i sg 0) (hv : Znth i s 0≠0) :
    EditBuildState s t n (i+1) sg cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,hg,
    EditCountsForPrefix_extend_one__build_s1_segments_counts s t n i sg cnt0 cnt1 block hs hi hg hc hb hv hbs⟩

theorem EditBuildState_extend_zero__build_s1_segments_counts (s t : List Int) (n i : Int) (sg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (ht : Zlength t=n)
    (hbs : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx s 0 ∧ Znth idx s 0≤1)
    (hbt : ∀ idx, (0 ≤ idx ∧ idx<n) → 0 ≤ Znth idx t 0 ∧ Znth idx t 0≤1)
    (hi : 0 ≤ i ∧ i<n) (hg : EditSegmentPrefix t (i+1) sg) (hc : EditCountsForPrefix s t n i cnt0 cnt1)
    (hb : block=Znth i sg 0) (hv : Znth i s 0=0) :
    EditBuildState s t n (i+1) sg (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 :=
  ⟨by omega, EditBinaryList_from_bounds__zeroing_and_base_build s n hs hbs,
    EditBinaryList_from_bounds__zeroing_and_base_build t n ht hbt,hg,
    EditCountsForPrefix_extend_zero__build_s1_segments_counts s t n i sg cnt0 cnt1 block hs hi hg hc hb hv⟩

theorem edit_seq_add__build_s2_segments_counts (start len : Nat) :
    List.range' start len=(List.range' 0 len).map (fun off => start+off) := by
  simpa only [←List.range_eq_range'] using (List.range'_eq_map_range (s:=start) (n:=len))

theorem edit_zrange_between_cons__build_s2_segments_counts (lo hi : Int) (hh : lo<hi) :
    edit_zrange_between lo hi=lo::edit_zrange_between (lo+1) hi := by
  have hlen : (hi-lo).toNat=(hi-(lo+1)).toNat+1 := by omega
  unfold edit_zrange_between
  rw [hlen,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro off _
    simp only [Function.comp_apply,Int.ofNat_eq_coe,Int.natCast_add,Int.natCast_one]
    omega

private theorem between_split (lo mid hi : Int) (hm : lo≤mid) (hh : mid≤hi) :
    edit_zrange_between lo hi=edit_zrange_between lo mid++edit_zrange_between mid hi := by
  have hlen : (hi-lo).toNat=(mid-lo).toNat+(hi-mid).toNat := by omega
  unfold edit_zrange_between
  rw [hlen,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro off _
  simp only [Function.comp_apply,Int.ofNat_eq_coe,Int.natCast_add]
  omega

theorem edit_zrange_split__build_s2_segments_counts (n i : Int) (hi : 0≤i ∧ i<n) :
    edit_zrange n=edit_zrange i++i::edit_zrange_between (i+1) n := by
  have hn : edit_zrange n=edit_zrange_between 0 n := by simp [edit_zrange,edit_zrange_between]
  have he : edit_zrange_between 0 i=edit_zrange i := by simp [edit_zrange,edit_zrange_between]
  rw [hn,between_split 0 i n hi.1 (by omega),he,edit_zrange_between_cons__build_s2_segments_counts i n hi.2]

theorem edit_zrange_In__build_s2_segments_counts (n idx : Int) (hi : idx∈edit_zrange n) : 0≤idx ∧ idx<n := by
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hi
  have hh := List.mem_range.mp hk
  simp only [Int.ofNat_eq_coe] at he
  omega

theorem edit_zrange_between_In__build_s2_segments_counts (lo hi idx : Int) (hm : idx∈edit_zrange_between lo hi) : lo≤idx ∧ idx<hi := by
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
  have hh := List.mem_range.mp hk
  simp only [Int.ofNat_eq_coe] at he
  omega

theorem edit_filter_all_false__build_s2_segments_counts {A : Type} (f : A→Bool) (xs : List A)
    (h : ∀ x, x∈xs → f x=false) : xs.filter f=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  simp only [h x hx,Bool.false_eq_true,not_false_eq_true]

theorem edit_count_bit_in_block_prefix_succ__build_s2_segments_counts (s t : List Int) (n i block bit : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) :
    edit_count_bit_in_block_prefix s t (i+1) block bit=edit_count_bit_in_block_prefix s t i block bit+
      (if edit_block_startb t i block && edit_bit_atb s i bit then 1 else 0) :=
  edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t i block bit (by omega)

theorem edit_block_startb_zero__build_s2_segments_counts (t : List Int) (block : Int) :
    edit_block_startb t 0 block=decide (block=0) :=
  block_bool_at t 0 0 block ⟨⟨by omega,by omega⟩,(by intros;omega),Or.inl rfl⟩

private theorem count_one_all (s t : List Int) (n block bit : Int) (hs : Zlength s=n) (hn : 1≤n) :
    edit_count_bit_in_block_prefix s t 1 block bit=if block=0 then if Znth 0 s 0=bit then 1 else 0 else 0 := by
  have h := edit_count_bit_in_block_prefix_succ__build_s1_segments_counts s t 0 block bit (by omega)
  simp only [Int.zero_add,edit_count_zero,edit_block_startb_zero__build_s2_segments_counts,edit_bit_atb] at h
  rw [h]
  by_cases hb : block=0 <;> by_cases hv : Znth 0 s 0=bit <;> simp [hb,hv]

theorem edit_count_prefix_one_nonzero_zero_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0≠0)
    (hb : ∀ idx, (0≤idx ∧ idx<n) → 0≤Znth idx s 0 ∧ Znth idx s 0≤1) :
    edit_count_bit_in_block_prefix s t 1 block 0=0 := by
  rw [count_one_all s t n block 0 hs hn]
  simp [hz]

theorem edit_count_prefix_one_nonzero_one_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0≠0)
    (hb : ∀ idx, (0≤idx ∧ idx<n) → 0≤Znth idx s 0 ∧ Znth idx s 0≤1) :
    edit_count_bit_in_block_prefix s t 1 block 1=(if decide (block=0) then 1 else 0) := by
  have hv : Znth 0 s 0=1 := by have := hb 0 (by omega); omega
  rw [count_one_all s t n block 1 hs hn]
  simp [hv]

theorem edit_count_prefix_one_zero_zero_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0=0) :
    edit_count_bit_in_block_prefix s t 1 block 0=(if decide (block=0) then 1 else 0) := by
  rw [count_one_all s t n block 0 hs hn]
  simp [hz]

theorem edit_count_prefix_one_zero_one_bit__build_s2_segments_counts (s t : List Int) (n block : Int)
    (hs : Zlength s=n) (hn : 1≤n) (hz : Znth 0 s 0=0) :
    edit_count_bit_in_block_prefix s t 1 block 1=0 := by
  rw [count_one_all s t n block 1 hs hn]
  simp [hz]

theorem edit_zrange_between_In_iff__build_s2_segments_counts (lo hi idx : Int) :
    idx∈edit_zrange_between lo hi ↔ lo≤idx ∧ idx<hi := by
  constructor
  · exact edit_zrange_between_In__build_s2_segments_counts lo hi idx
  · intro h
    exact (edit_zrange_between_in__build_s1_segments_counts lo hi idx (by omega)).mpr h

theorem edit_edge_openb_true_iff__build_s2_segments_counts (t : List Int) (idx : Int) :
    edit_edge_openb t idx=true ↔ edit_edge_open t idx := edit_edge_openb_true_iff__build_s1_segments_counts t idx

theorem edit_all_edges_openb_true_iff__build_s2_segments_counts (t : List Int) (lo hi : Int) :
    edit_all_edges_openb t lo hi=true ↔ ∀ k, (lo≤k ∧ k<hi) → edit_edge_open t k := by
  simp only [edit_all_edges_openb,List.all_eq_true,edit_edge_openb_true_iff__build_s1_segments_counts,
    edit_zrange_between_In_iff__build_s2_segments_counts]

theorem edit_block_startb_true_iff__build_s2_segments_counts (t : List Int) (idx start : Int) :
    edit_block_startb t idx start=true ↔ EditBlockStart t idx start := edit_block_startb_true_iff__build_s1_segments_counts t idx start

theorem edit_block_start_unique__build_s2_segments_counts (t : List Int) (idx start1 start2 : Int)
    (h1 : EditBlockStart t idx start1) (h2 : EditBlockStart t idx start2) : start1=start2 :=
  EditBlockStart_unique__build_s1_segments_counts t idx start1 start2 h1 h2

theorem edit_block_startb_unique__build_s2_segments_counts (t : List Int) (idx start block : Int)
    (hs : EditBlockStart t idx start) (hb : edit_block_startb t idx block=true) : block=start :=
  EditBlockStart_unique__build_s1_segments_counts t idx block start ((edit_block_startb_true_iff__build_s1_segments_counts t idx block).mp hb) hs

theorem edit_Znth_app_last__build_s2_segments_counts {A : Type} (xs : List A) (v d : A) (i : Int)
    (hi : Zlength xs=i) : Znth i (xs++[v]) d=v := snoc_last xs v d i hi

theorem edit_segment_prefix_append_new__build_s2_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 0≤i) (he : ¬edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[i]) := EditSegmentPrefix_extend_new__build_s1_segments_counts t i sg hg hi he

theorem edit_segment_prefix_append_same__build_s2_segments_counts (t : List Int) (i : Int) (sg : List Int)
    (hg : EditSegmentPrefix t i sg) (hi : 1≤i) (he : edit_edge_open t i) :
    EditSegmentPrefix t (i+1) (sg++[Znth (i-1) sg 0]) := EditSegmentPrefix_extend_open__build_s1_segments_counts t i sg hg hi he

theorem edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts (s t : List Int) (n upto block bit : Int)
    (hs : Zlength s=n) (hn : 0≤n) : 0≤edit_count_bit_in_block_prefix s t upto block bit ∧ edit_count_bit_in_block_prefix s t upto block bit≤n := by
  have hl := List.length_filter_le (fun idx => decide (idx<upto) && edit_block_startb t idx block && edit_bit_atb s idx bit) (edit_zrange (Zlength s))
  have he : Int.ofNat (edit_zrange (Zlength s)).length=n := by
    simp only [edit_zrange,List.length_map,List.length_range,Int.ofNat_eq_coe]
    omega
  unfold edit_count_bit_in_block_prefix
  simp only [Int.ofNat_eq_coe] at he ⊢
  omega

theorem edit_counts_prefix_extend_one__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i seg 0) (hv : Znth i s 0=1) :
    EditCountsForPrefix s t n (i+1) cnt0 (replace_Znth block (Znth block cnt1 0+1) cnt1) := by
  simpa using counts_extend s t n i seg cnt0 cnt1 block 1 hs hi hg hc hb (Or.inr rfl) hv

theorem edit_counts_prefix_extend_zero__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt0 cnt1 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt0 cnt1) (hb : block=Znth i seg 0) (hv : Znth i s 0=0) :
    EditCountsForPrefix s t n (i+1) (replace_Znth block (Znth block cnt0 0+1) cnt0) cnt1 :=
  EditCountsForPrefix_extend_zero__build_s1_segments_counts s t n i seg cnt0 cnt1 block hs hi hg hc hb hv

theorem edit_scratch_bound_update_one__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt10 cnt11 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt20 cnt21) (hbound : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21)
    (hb : block=Znth i seg 0) (hv : Znth i s 0=1) :
    EditScratchCountsBound n cnt10 cnt11 cnt20 (replace_Znth block (Znth block cnt21 0+1) cnt21) := by
  have hbnd : 0≤block ∧ block<n := by have := (hg.2 i (by omega)).1; omega
  exact ⟨hbound.1,hbound.2.1,hbound.2.2.1,bound_inc s t n i cnt21 block 1 hs hi hbnd (hc.2.2.2 block hbnd) hbound.2.2.2⟩

theorem edit_scratch_bound_update_zero__build_s2_segments_counts (s t : List Int) (n i : Int) (seg cnt10 cnt11 cnt20 cnt21 : List Int) (block : Int)
    (hs : Zlength s=n) (hi : 0≤i ∧ i<n) (hg : EditSegmentPrefix t (i+1) seg)
    (hc : EditCountsForPrefix s t n i cnt20 cnt21) (hbound : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21)
    (hb : block=Znth i seg 0) (hv : Znth i s 0=0) :
    EditScratchCountsBound n cnt10 cnt11 (replace_Znth block (Znth block cnt20 0+1) cnt20) cnt21 := by
  have hbnd : 0≤block ∧ block<n := by have := (hg.2 i (by omega)).1; omega
  exact ⟨hbound.1,hbound.2.1,bound_inc s t n i cnt20 block 0 hs hi hbnd (hc.2.2.1 block hbnd) hbound.2.2.1,hbound.2.2.2⟩

theorem edit_zrange_nodup__greedy_common_and_mismatch_steps (n : Int) : (edit_zrange n).Nodup :=
  edit_zrange_NoDup__build_s1_segments_counts n

theorem edit_zrange_in__greedy_common_and_mismatch_steps (n idx : Int) (hi : 0≤idx ∧ idx<n) : idx∈edit_zrange n :=
  (edit_zrange_in__build_s1_segments_counts n idx (by omega)).mpr hi

theorem edit_zrange_in_bounds__greedy_common_and_mismatch_steps (n idx : Int) (hi : idx∈edit_zrange n) : 0≤idx ∧ idx<n :=
  edit_zrange_In__build_s2_segments_counts n idx hi

theorem edit_edge_openb_true_iff__greedy_common_and_mismatch_steps (t : List Int) (idx : Int) :
    edit_edge_openb t idx=true ↔ edit_edge_open t idx := edit_edge_openb_true_iff__build_s1_segments_counts t idx

theorem edit_all_edges_openb_true__greedy_common_and_mismatch_steps (t : List Int) (lo hi : Int)
    (h : ∀ k, (lo≤k ∧ k<hi) → edit_edge_open t k) : edit_all_edges_openb t lo hi=true :=
  (edit_all_edges_openb_true_iff__build_s2_segments_counts t lo hi).mpr h

theorem edit_block_startb_true__greedy_common_and_mismatch_steps (t : List Int) (idx start : Int)
    (h : EditBlockStart t idx start) : edit_block_startb t idx start=true :=
  (edit_block_startb_true_iff__build_s1_segments_counts t idx start).mpr h

theorem edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps
    (s t : List Int) (n : Int) (seg full0 full1 : List Int) (i : Int)
    (hb : EditBuildState s t n n seg full0 full1) (hi : 0≤i ∧ i<n) :
    edit_count_positions_in_seg_prefix seg i (Znth i seg 0)<Znth (Znth i seg 0) full0 0+Znth (Znth i seg 0) full1 0 := by
  let block := Znth i seg 0
  have hg := hb.2.2.2.1
  have hs := hb.2.1
  have hc := hb.2.2.2.2
  have hblock : 0≤block ∧ block<n := by have := (hg.2 i hi).1; dsimp [block]; omega
  rw [hc.2.2.1 block hblock,hc.2.2.2 block hblock]
  unfold edit_count_positions_in_seg_prefix edit_count_bit_in_block_prefix
  rw [hg.1,hs.1]
  let xs := edit_zrange n
  let P := fun idx => decide (idx<i) && decide (Znth idx seg 0=block)
  let Q0 := fun idx => decide (idx<n) && edit_block_startb t idx block && edit_bit_atb s idx 0
  let Q1 := fun idx => decide (idx<n) && edit_block_startb t idx block && edit_bit_atb s idx 1
  change Int.ofNat (xs.filter P).length<Int.ofNat (xs.filter Q0).length+Int.ofNat (xs.filter Q1).length
  have hin : i∈xs := edit_zrange_in__greedy_common_and_mismatch_steps n i hi
  have hnot : i∉xs.filter P := by
    intro h
    have := (List.mem_filter.mp h).2
    simp [P] at this
  have hnodup : (i::xs.filter P).Nodup := List.nodup_cons.mpr
    ⟨hnot,List.filter_sublist.nodup (edit_zrange_NoDup__build_s1_segments_counts n)⟩
  have hsub : ∀ x, x∈i::xs.filter P → x∈xs.filter Q0++xs.filter Q1 := by
    intro x hx
    have hxdata : x∈xs ∧ Znth x seg 0=block := by
      rcases List.mem_cons.mp hx with he|hm
      · subst x; exact ⟨hin,rfl⟩
      · have hm := List.mem_filter.mp hm
        refine ⟨hm.1,?_⟩
        have ht := hm.2
        simp only [P,Bool.and_eq_true,decide_eq_true_eq] at ht
        exact ht.2
    have hxr := edit_zrange_In__build_s2_segments_counts n x hxdata.1
    have hstart := hg.2 x hxr
    rw [hxdata.2] at hstart
    have hopen := edit_block_startb_true__greedy_common_and_mismatch_steps t x block hstart
    rcases hs.2 x hxr with hz|ho
    · apply List.mem_append.mpr; left
      apply List.mem_filter.mpr
      exact ⟨hxdata.1,by simp [Q0,hxr.2,hopen,edit_bit_atb,hz]⟩
    · apply List.mem_append.mpr; right
      apply List.mem_filter.mpr
      exact ⟨hxdata.1,by simp [Q1,hxr.2,hopen,edit_bit_atb,ho]⟩
  have hlen := nodup_subset_length (i::xs.filter P) (xs.filter Q0++xs.filter Q1) hnodup hsub
  simp only [List.length_cons,List.length_append,Int.ofNat_eq_coe] at hlen ⊢
  omega

theorem edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21) :
    EditGreedyCurrentAvailability n i seg1 seg2 cnt10 cnt11 cnt20 cnt21 := by
  intro hi
  obtain ⟨full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs.2.2
  have hg1 := hb1.2.2.2.1
  have hg2 := hb2.2.2.2.1
  have ha : 0≤Znth i seg1 0 ∧ Znth i seg1 0<n := by have := (hg1.2 i hi).1; omega
  have hb : 0≤Znth i seg2 0 ∧ Znth i seg2 0<n := by have := (hg2.2 i hi).1; omega
  have hlt1 := edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps s1 t1 n seg1 full10 full11 i hb1 hi
  have hlt2 := edit_count_positions_prefix_lt_full_counts_current__greedy_common_and_mismatch_steps s2 t2 n seg2 full20 full21 i hb2 hi
  have hr1 := hr.1 (Znth i seg1 0) (by simpa only [hg1.1] using ha)
  have hr2 := hr.2 (Znth i seg2 0) (by simpa only [hg2.1] using hb)
  exact ⟨ha,hb,by omega,by omega⟩

theorem edit_count_positions_in_seg_prefix_zero__greedy_common_and_mismatch_steps (seg : List Int) (block : Int) :
    edit_count_positions_in_seg_prefix seg 0 block=0 := by
  unfold edit_count_positions_in_seg_prefix
  have he : (edit_zrange (Zlength seg)).filter (fun idx => decide (idx<0) && decide (Znth idx seg 0=block))=[] := by
    apply edit_filter_all_false__build_s2_segments_counts
    intro idx hi
    have hr := edit_zrange_In__build_s2_segments_counts _ idx hi
    simp [show ¬idx<0 by omega]
  rw [he]
  rfl

private theorem positions_step (seg : List Int) (i block : Int) (hi : 0≤i ∧ i<Zlength seg) :
    edit_count_positions_in_seg_prefix seg (i+1) block=edit_count_positions_in_seg_prefix seg i block+
      (if Znth i seg 0=block then 1 else 0) := by
  have h := filter_limit_succ_once__build_s1_segments_counts (edit_zrange (Zlength seg)) i
    (fun idx => decide (Znth idx seg 0=block)) (edit_zrange_NoDup__build_s1_segments_counts _)
    (edit_zrange_in__greedy_common_and_mismatch_steps _ i hi) (by intros;omega)
  unfold edit_count_positions_in_seg_prefix
  rw [h]
  simp only [Int.ofNat_eq_coe,Int.natCast_add]
  by_cases he : Znth i seg 0=block <;> simp [he]

theorem edit_count_positions_step_same__greedy_common_and_mismatch_steps (seg : List Int) (i block : Int)
    (hi : 0≤i ∧ i<Zlength seg) (hb : block=Znth i seg 0) :
    edit_count_positions_in_seg_prefix seg (i+1) block=edit_count_positions_in_seg_prefix seg i block+1 := by
  rw [positions_step seg i block hi,if_pos hb.symm]

theorem edit_count_positions_step_diff__greedy_common_and_mismatch_steps (seg : List Int) (i block : Int)
    (hi : 0≤i ∧ i<Zlength seg) (hb : Znth i seg 0≠block) :
    edit_count_positions_in_seg_prefix seg (i+1) block=edit_count_positions_in_seg_prefix seg i block := by
  rw [positions_step seg i block hi,if_neg hb,Int.add_zero]

theorem edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps
    (seg : List Int) (i : Int) (full0 full1 cnt0 cnt1 : List Int) (idx : Int)
    (hi : 0≤i ∧ i<Zlength seg) (he : idx=Znth i seg 0) (hidx : 0≤idx ∧ idx<Zlength seg)
    (hlen : Zlength cnt0=Zlength seg)
    (hr : ∀ block, (0≤block ∧ block<Zlength seg) → Znth block cnt0 0+Znth block cnt1 0=
      Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg i block) :
    ∀ block, (0≤block ∧ block<Zlength seg) →
      Znth block (replace_Znth idx (Znth idx cnt0 0-1) cnt0) 0+Znth block cnt1 0=
        Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg (i+1) block := by
  intro block hb
  rw [replace_read cnt0 idx block _ (by simpa only [hlen] using hidx) (by simpa only [hlen] using hb),positions_step seg i block hi]
  have h := hr block hb
  by_cases hx : block=idx
  · rcases hx with rfl; simp only [ite_true,if_pos he.symm]; omega
  · rw [if_neg hx,if_neg (by omega)]
    omega

theorem edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps
    (seg : List Int) (i : Int) (full0 full1 cnt0 cnt1 : List Int) (idx : Int)
    (hi : 0≤i ∧ i<Zlength seg) (he : idx=Znth i seg 0) (hidx : 0≤idx ∧ idx<Zlength seg)
    (hlen : Zlength cnt1=Zlength seg)
    (hr : ∀ block, (0≤block ∧ block<Zlength seg) → Znth block cnt0 0+Znth block cnt1 0=
      Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg i block) :
    ∀ block, (0≤block ∧ block<Zlength seg) →
      Znth block cnt0 0+Znth block (replace_Znth idx (Znth idx cnt1 0-1) cnt1) 0=
        Znth block full0 0+Znth block full1 0-edit_count_positions_in_seg_prefix seg (i+1) block := by
  intro block hb
  rw [replace_read cnt1 idx block _ (by simpa only [hlen] using hidx) (by simpa only [hlen] using hb),positions_step seg i block hi]
  have h := hr block hb
  by_cases hx : block=idx
  · rcases hx with rfl; simp only [ite_true,if_pos he.symm]; omega
  · rw [if_neg hx,if_neg (by omega)]
    omega

theorem edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps (n : Int) (cnt : List Int) (idx : Int)
    (hb : EditCountBounds n cnt) (hi : 0≤idx ∧ idx<n) (hp : 0<Znth idx cnt 0) :
    EditCountBounds n (replace_Znth idx (Znth idx cnt 0-1) cnt) := by
  apply bounds_update n cnt idx _ hb hi
  have := hb.2 idx hi
  omega

theorem edit_greedy_prefix_state_start__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hb1 : EditBuildState s1 t1 n n seg1 cnt10 cnt11) (hb2 : EditBuildState s2 t2 n n seg2 cnt20 cnt21)
    (hsc : EditScratchCountsBound n cnt10 cnt11 cnt20 cnt21) :
    EditGreedyPrefixState s1 s2 t1 t2 n 0 0 seg1 seg2 cnt10 cnt11 cnt20 cnt21 := by
  refine ⟨by have := hb1.1;omega,by omega,cnt10,cnt11,cnt20,cnt21,hb1,hb2,hsc,?_,?_⟩
  · constructor <;> intros <;> simp only [edit_count_positions_in_seg_prefix_zero__greedy_common_and_mismatch_steps,Int.sub_zero]
  · exact EditGreedyConsumedPrefix_start seg1 seg2 cnt10 cnt11 cnt20 cnt21

theorem edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21) (hi : 0≤i ∧ i<n) :
    (0≤Znth i seg1 0 ∧ Znth i seg1 0<n) ∧ (0≤Znth i seg2 0 ∧ Znth i seg2 0<n) ∧
    (0≤Znth (Znth i seg1 0) cnt10 0 ∧ Znth (Znth i seg1 0) cnt10 0≤n) ∧
    (0≤Znth (Znth i seg1 0) cnt11 0 ∧ Znth (Znth i seg1 0) cnt11 0≤n) ∧
    (0≤Znth (Znth i seg2 0) cnt20 0 ∧ Znth (Znth i seg2 0) cnt20 0≤n) ∧
    (0≤Znth (Znth i seg2 0) cnt21 0 ∧ Znth (Znth i seg2 0) cnt21 0≤n) := by
  have hav := edit_greedy_prefix_state_current_availability__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  obtain ⟨_,_,_,_,_,_,hsc,_⟩ := hs.2.2
  exact ⟨hav.1,hav.2.1,hsc.1.2 _ hav.1,hsc.2.1.2 _ hav.1,hsc.2.2.1.2 _ hav.2.1,hsc.2.2.2.2 _ hav.2.1⟩

theorem edit_greedy_common_zero_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hpa : 0<Znth a cnt10 0) (hpb : 0<Znth b cnt20 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) (ans+1) seg1 seg2 (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21 := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt10 a hsc.1 haRange hpa, hsc.2.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt20 b hsc.2.2.1 hbRange hpb, hsc.2.2.2⟩
  · constructor
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.1.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_common_zero seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb  hpa hpb hcon

theorem edit_greedy_common_one_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hn0 : ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0))
    (hpa : 0<Znth a cnt11 0) (hpb : 0<Znth b cnt21 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) (ans+1) seg1 seg2 cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21) := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨hsc.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt11 a hsc.2.1 haRange hpa, hsc.2.2.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt21 b hsc.2.2.2 hbRange hpb⟩
  · constructor
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.2.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.2.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_common_one seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb hn0 hpa hpb hcon

theorem edit_greedy_s1_zero_s2_one_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hn0 : ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0))
    (hn1 : ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0))
    (hpa : 0<Znth a cnt10 0) (hpb : 0<Znth b cnt21 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) ans seg1 seg2 (replace_Znth a (Znth a cnt10 0-1) cnt10) cnt11 cnt20 (replace_Znth b (Znth b cnt21 0-1) cnt21) := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt10 a hsc.1 haRange hpa, hsc.2.1, hsc.2.2.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt21 b hsc.2.2.2 hbRange hpb⟩
  · constructor
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.2.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_s1_zero_s2_one seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb hn0 hn1 hpa hpb hcon

theorem edit_greedy_s1_one_s2_zero_step__greedy_common_and_mismatch_steps
    (s1 s2 t1 t2 : List Int) (n i ans : Int) (seg1 seg2 cnt10 cnt11 cnt20 cnt21 : List Int) (a b : Int)
    (hs : EditGreedyPrefixState s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0)
    (hn0 : ¬(0<Znth a cnt10 0 ∧ 0<Znth b cnt20 0))
    (hn1 : ¬(0<Znth a cnt11 0 ∧ 0<Znth b cnt21 0))
    (hna : ¬(0<Znth a cnt10 0))
    (hpa : 0<Znth a cnt11 0) (hpb : 0<Znth b cnt20 0) :
    EditGreedyPrefixState s1 s2 t1 t2 n (i+1) ans seg1 seg2 cnt10 (replace_Znth a (Znth a cnt11 0-1) cnt11) (replace_Znth b (Znth b cnt20 0-1) cnt20) cnt21 := by
  have hrange := edit_greedy_prefix_state_read_bounds__greedy_common_and_mismatch_steps s1 s2 t1 t2 n i ans seg1 seg2 cnt10 cnt11 cnt20 cnt21 hs hi
  have haRange : 0≤a ∧ a<n := by simpa only [ha] using hrange.1
  have hbRange : 0≤b ∧ b<n := by simpa only [hb] using hrange.2.1
  obtain ⟨hib,hans,full10,full11,full20,full21,hb1,hb2,hsc,hr,hcon⟩ := hs
  have hlen1 := hb1.2.2.2.1.1
  have hlen2 := hb2.2.2.2.1.1
  have hi1 : 0≤i ∧ i<Zlength seg1 := by simpa only [hlen1] using hi
  have hi2 : 0≤i ∧ i<Zlength seg2 := by simpa only [hlen2] using hi
  have hlen : Zlength seg2=Zlength seg1 := by omega
  refine ⟨by omega,by omega,full10,full11,full20,full21,hb1,hb2,?_,?_,?_⟩
  · exact ⟨hsc.1, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt11 a hsc.2.1 haRange hpa, edit_count_bounds_replace_decr__greedy_common_and_mismatch_steps n cnt20 b hsc.2.2.1 hbRange hpb, hsc.2.2.2⟩
  · constructor
    · exact edit_remaining_totals_decr_right__greedy_common_and_mismatch_steps seg1 i full10 full11 cnt10 cnt11 a
        hi1 ha (by simpa only [hlen1] using haRange) (by rw [hsc.2.1.1,hlen1]) hr.1
    · exact edit_remaining_totals_decr_left__greedy_common_and_mismatch_steps seg2 i full20 full21 cnt20 cnt21 b
        hi2 hb (by simpa only [hlen2] using hbRange) (by rw [hsc.2.2.1.1,hlen2]) hr.2
  · exact EditGreedyConsumedPrefix_s1_one_s2_zero seg1 seg2 full10 full11 full20 full21 i ans cnt10 cnt11 cnt20 cnt21 a b
      hi1 hlen ha hb hn0 hn1 hna hpa hpb hcon

end SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib

namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings
export edit_strings_lib (edit_zrange edit_zrange_between EditBinaryList edit_edge_open edit_edge_openb edit_all_edges_openb EditBlockStart edit_block_startb edit_bit_atb edit_count_bit_in_block_prefix EditZeroPrefix EditZeroFull EditSegmentPrefix EditCountsForPrefix EditBuildState EditCountBounds EditScratchCountsBound edit_count_positions_in_seg_prefix EditGreedyRemainingTotals EditReachableString edit_match_count EditStringsFeasibleMatchCount EditStringsMatchUpperBound EditStringsMaximum EditGreedyConsumedPrefix EditGreedyFinalOptimality EditGreedyPrefixState EditGreedyCurrentAvailability EditGreedyCompletedMaximumFacts EditGreedyCompletedStateFacts)
end SimpleC.EE.LLM_bench.Algorithms.edit_strings

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib
open AUXLib

abbrev EditBlockBitCount := edit_count_bit_in_block_prefix
def EditSegmentMeaning (t : List Int) (upto : Int) (seg : List Int) : Prop :=
  ∀ idx : Int, (0 ≤ idx ∧ idx < upto) → EditBlockStart t idx (Znth idx seg 0)
def EditCountsMeaning (s t : List Int) (n upto : Int) (cnt0 cnt1 : List Int) : Prop :=
  (∀ block : Int, (0 ≤ block ∧ block < n) → Znth block cnt0 0 = EditBlockBitCount s t upto block 0) ∧
  (∀ block : Int, (0 ≤ block ∧ block < n) → Znth block cnt1 0 = EditBlockBitCount s t upto block 1)
def EditBuildMeaning (s t : List Int) (n upto : Int) (seg cnt0 cnt1 : List Int) : Prop :=
  EditSegmentMeaning t upto seg ∧ EditCountsMeaning s t n upto cnt0 cnt1

def EditSwapAt (xs : List Int) (i j : Int) : List Int :=
  replace_Znth j (Znth i xs 0) (replace_Znth i (Znth j xs 0) xs)
def EditLegalSwap (mask before after : List Int) : Prop :=
  ∃ i : Int, 0 ≤ i ∧ i + 1 < Zlength before ∧ Znth i mask 0 = 49 ∧
    Znth (i + 1) mask 0 = 49 ∧ after = EditSwapAt before i (i + 1)
def EditPairMatches (left right : List Int) : Int :=
  Zlength ((List.zip left right).filter (fun p => decide (p.1 = p.2)))
def EditStringsAnswer (s1 s2 t1 t2 : List Int) (answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (LE.le (α := Int))
    (fun outputs : List Int × List Int =>
      _root_.clos_refl_trans (EditLegalSwap t1) s1 outputs.1 ∧
      _root_.clos_refl_trans (EditLegalSwap t2) s2 outputs.2)
    (fun outputs => EditPairMatches outputs.1 outputs.2) answer
def EditInventoryCount (regions values : List Int) (block bit : Int) : Int :=
  Zlength ((List.zip regions values).filter (fun p => decide (p.1 = block) && decide (p.2 = bit)))
def EditSuffixInventory (regions : List Int) (i : Int) (zeroes ones values : List Int) : Prop :=
  Zlength values = Zlength regions - i ∧ Forall (fun bit => bit = 0 ∨ bit = 1) values ∧
  ∀ block : Int, (0 ≤ block ∧ block < Zlength regions) →
    EditInventoryCount (sublist i (Zlength regions) regions) values block 0 = Znth block zeroes 0 ∧
    EditInventoryCount (sublist i (Zlength regions) regions) values block 1 = Znth block ones 0
def EditCompletion (s1 s2 t1 t2 prefix1 prefix2 : List Int) (outputs : List Int × List Int) : Prop :=
  _root_.clos_refl_trans (EditLegalSwap (t1.map (48 + ·)))
    (s1.map (48 + ·)) ((prefix1 ++ outputs.1).map (48 + ·)) ∧
  _root_.clos_refl_trans (EditLegalSwap (t2.map (48 + ·)))
    (s2.map (48 + ·)) ((prefix2 ++ outputs.2).map (48 + ·))
def EditFeasibleSuffix (s1 s2 t1 t2 regions1 regions2 prefix1 prefix2 : List Int)
    (i : Int) (zeroes1 ones1 zeroes2 ones2 : List Int) (outputs : List Int × List Int) : Prop :=
  EditCompletion s1 s2 t1 t2 prefix1 prefix2 outputs ∧
  EditSuffixInventory regions1 i zeroes1 ones1 outputs.1 ∧
  EditSuffixInventory regions2 i zeroes2 ones2 outputs.2
def EditRemainingMatches (s1 s2 t1 t2 regions1 regions2 prefix1 prefix2 : List Int)
    (i : Int) (zeroes1 ones1 zeroes2 ones2 : List Int) (answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (LE.le (α := Int))
    (EditFeasibleSuffix s1 s2 t1 t2 regions1 regions2 prefix1 prefix2 i zeroes1 ones1 zeroes2 ones2)
    (fun outputs => EditPairMatches outputs.1 outputs.2) answer

theorem EditBuildState.toAnnotation (h : EditBuildState s t n upto seg cnt0 cnt1) :
    EditBuildMeaning s t n upto seg cnt0 cnt1 := ⟨h.2.2.2.1.2, h.2.2.2.2.2.2⟩

end SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib
namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings
export edit_strings_lib (EditBlockBitCount EditSegmentMeaning EditCountsMeaning EditBuildMeaning EditSwapAt EditLegalSwap EditPairMatches EditStringsAnswer EditInventoryCount EditSuffixInventory EditCompletion EditFeasibleSuffix EditRemainingMatches)
end SimpleC.EE.LLM_bench.Algorithms.edit_strings

set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace EditStringsProofInternal
open AUXLib SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib

def edit_hit (a b : Int) : Int := if a=b then 1 else 0

theorem edit_pair_cons (a b : Int) (xs ys : List Int) :
    EditPairMatches (a::xs) (b::ys)=edit_hit a b+EditPairMatches xs ys := by
  by_cases he : a=b
  · simp only [EditPairMatches,List.zip_cons_cons,List.filter_cons,edit_hit,he,
      decide_true,ite_true,Zlength,List.length_cons,Int.ofNat_eq_coe]
    omega
  · simp only [EditPairMatches,List.zip_cons_cons,List.filter_cons,edit_hit,he,
      decide_false,Bool.false_eq_true,ite_false,Zlength,Int.ofNat_eq_coe,Int.zero_add]

theorem edit_pair_symmetric (xs ys : List Int) : EditPairMatches xs ys=EditPairMatches ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      rw [edit_pair_cons,edit_pair_cons,ih]
      by_cases he : a=b
      · simp only [edit_hit,if_pos he,if_pos he.symm]
      · simp only [edit_hit,if_neg he,if_neg (Ne.symm he)]

theorem edit_pair_bounds (xs ys : List Int) : 0≤EditPairMatches xs ys ∧ EditPairMatches xs ys≤Zlength xs := by
  have hf := List.length_filter_le (p := fun p : Int×Int => decide (p.1=p.2)) (l := xs.zip ys)
  have hz : (xs.zip ys).length=min xs.length ys.length := List.length_zip
  simp only [EditPairMatches,Zlength,Int.ofNat_eq_coe]
  omega

theorem edit_pair_encode (xs ys : List Int) :
    EditPairMatches (xs.map (48+·)) (ys.map (48+·))=EditPairMatches xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      have he : (48+a=48+b) ↔ a=b := ⟨Int.add_left_cancel,congrArg (48+·)⟩
      simp only [List.map_cons,edit_pair_cons,ih,edit_hit,he]

private theorem edit_pair_update_nat (xs ys : List Int) (i : Nat) (value : Int)
    (hlen : xs.length=ys.length) (hi : i<xs.length) :
    EditPairMatches (replace_nth i xs value) ys = EditPairMatches xs ys-
      edit_hit (xs.getD i 0) (ys.getD i 0)+edit_hit value (ys.getD i 0) := by
  induction xs generalizing ys i with
  | nil => simp only [List.length_nil,Nat.not_lt_zero] at hi
  | cons a xs ih =>
    cases ys with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons b ys =>
      cases i with
      | zero =>
        simp only [replace_nth,List.getD_cons_zero,edit_pair_cons]
        omega
      | succ i =>
        simp only [replace_nth,List.getD_cons_succ,edit_pair_cons]
        rw [ih ys i (Nat.succ.inj hlen) (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)]
        omega

theorem edit_pair_update_left (xs ys : List Int) (i value : Int)
    (hlen : Zlength xs=Zlength ys) (hi : 0≤i ∧ i<Zlength xs) :
    EditPairMatches (replace_Znth i value xs) ys = EditPairMatches xs ys-
      edit_hit (Znth i xs 0) (Znth i ys 0)+edit_hit value (Znth i ys 0) := by
  exact edit_pair_update_nat xs ys i.toNat value (Int.ofNat_inj.mp hlen)
    (by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega)

theorem edit_pair_swap_left (xs ys : List Int) (j : Int)
    (hlen : Zlength xs=Zlength ys) (hj : 0<j ∧ j<Zlength xs) :
    EditPairMatches (EditSwapAt xs 0 j) ys = EditPairMatches xs ys-
      edit_hit (Znth 0 xs 0) (Znth 0 ys 0)-edit_hit (Znth j xs 0) (Znth j ys 0)+
      edit_hit (Znth j xs 0) (Znth 0 ys 0)+edit_hit (Znth 0 xs 0) (Znth j ys 0) := by
  unfold EditSwapAt
  rw [edit_pair_update_left _ ys j _ (by simpa only [Zlength_replace_Znth] using hlen)
      (by rw [Zlength_replace_Znth]; omega),
    edit_pair_update_left xs ys 0 _ hlen (by omega),
    Znth_replace_Znth_Diff 0 xs 0 j _ (by omega) (by omega) (by omega)]
  omega

theorem edit_pair_swap_improves (xs ys : List Int) (j : Int)
    (hlen : Zlength xs=Zlength ys) (hj : 0<j ∧ j<Zlength xs)
    (hne : Znth 0 xs 0≠Znth 0 ys 0) (he : Znth j xs 0=Znth 0 ys 0) :
    EditPairMatches xs ys≤EditPairMatches (EditSwapAt xs 0 j) ys := by
  rw [edit_pair_swap_left xs ys j hlen hj,he]
  simp only [edit_hit,if_neg hne,if_pos rfl]
  split_ifs <;> omega

def edit_inventory_hit (region value block bit : Int) : Int := if region=block ∧ value=bit then 1 else 0

theorem edit_inventory_cons (region value block bit : Int) (regions values : List Int) :
    EditInventoryCount (region::regions) (value::values) block bit =
      edit_inventory_hit region value block bit+EditInventoryCount regions values block bit := by
  by_cases hr : region=block <;> by_cases hv : value=bit <;>
    (simp only [EditInventoryCount,List.zip_cons_cons,List.filter_cons,edit_inventory_hit,hr,hv,
      decide_true,decide_false,Bool.true_and,Bool.false_and,and_self,and_false,false_and,
      Bool.false_eq_true,ite_true,ite_false,Zlength,List.length_cons,Int.ofNat_eq_coe] <;> omega)

private theorem edit_inventory_update_nat (regions values : List Int) (i : Nat) (value block bit : Int)
    (hlen : regions.length=values.length) (hi : i<values.length) :
    EditInventoryCount regions (replace_nth i values value) block bit = EditInventoryCount regions values block bit-
      edit_inventory_hit (regions.getD i 0) (values.getD i 0) block bit+
      edit_inventory_hit (regions.getD i 0) value block bit := by
  induction regions generalizing values i with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons r regions ih =>
    cases values with
    | nil => simp only [List.length_nil,Nat.not_lt_zero] at hi
    | cons v values =>
      cases i with
      | zero =>
        simp only [replace_nth,List.getD_cons_zero,edit_inventory_cons]
        omega
      | succ i =>
        simp only [replace_nth,List.getD_cons_succ,edit_inventory_cons]
        rw [ih values i (Nat.succ.inj hlen) (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)]
        omega

theorem edit_inventory_update (regions values : List Int) (i value block bit : Int)
    (hlen : Zlength regions=Zlength values) (hi : 0≤i ∧ i<Zlength values) :
    EditInventoryCount regions (replace_Znth i value values) block bit = EditInventoryCount regions values block bit-
      edit_inventory_hit (Znth i regions 0) (Znth i values 0) block bit+
      edit_inventory_hit (Znth i regions 0) value block bit := by
  exact edit_inventory_update_nat regions values i.toNat value block bit (Int.ofNat_inj.mp hlen)
    (by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega)

theorem edit_inventory_swap (regions values : List Int) (i j block bit : Int)
    (hlen : Zlength regions=Zlength values) (hi : 0≤i ∧ i<Zlength values) (hj : 0≤j ∧ j<Zlength values)
    (he : Znth i regions 0=Znth j regions 0) :
    EditInventoryCount regions (EditSwapAt values i j) block bit=EditInventoryCount regions values block bit := by
  unfold EditSwapAt
  by_cases hij : i=j
  · subst j
    simp only [replace_Znth_Znth]
  · rw [edit_inventory_update regions _ j _ block bit (by simpa only [Zlength_replace_Znth] using hlen)
        (by simpa only [Zlength_replace_Znth] using hj),
      edit_inventory_update regions values i _ block bit hlen hi,
      Znth_replace_Znth_Diff 0 values i j _ hi hj hij,he]
    omega

theorem edit_bounded_maximum {A : Type} (candidates : A → Prop) (score : A → Int) (bound : Int)
    (hne : ∃ x, candidates x) (hb : ∀ x, candidates x → 0≤score x ∧ score x≤bound) :
    ∃ answer, MaxMinLib.max_value_of_subset (LE.le (α := Int)) candidates score answer := by
  classical
  have hmain : ∀ n : Nat, (∀ x, candidates x → 0≤score x ∧ score x≤(n : Int)) →
      ∃ answer, MaxMinLib.max_value_of_subset (LE.le (α := Int)) candidates score answer := by
    intro n
    induction n with
    | zero =>
      intro hs
      obtain ⟨x,hx⟩ := hne
      have hx0 := hs x hx
      refine ⟨0,x,⟨hx,?_⟩,by omega⟩
      intro y hy
      have hy0 := hs y hy
      omega
    | succ n ih =>
      intro hs
      by_cases ht : ∃ x, candidates x ∧ score x=(n+1 : Nat)
      · obtain ⟨x,hx,he⟩ := ht
        refine ⟨(n+1 : Nat),x,⟨hx,?_⟩,he⟩
        intro y hy
        have hyb := hs y hy
        omega
      · apply ih
        intro x hx
        have hxs := hs x hx
        have hne' : score x≠(n+1 : Nat) := by intro he; exact ht ⟨x,hx,he⟩
        exact ⟨hxs.1,by omega⟩
  obtain ⟨x,hx⟩ := hne
  have hxbound := hb x hx
  apply hmain bound.toNat
  intro y hy
  have hybound := hb y hy
  exact ⟨hybound.1,by omega⟩

theorem edit_swap_length (xs : List Int) (i j : Int) : Zlength (EditSwapAt xs i j)=Zlength xs := by
  simp only [EditSwapAt,Zlength_replace_Znth]

theorem edit_swap_read (xs : List Int) (i j k : Int)
    (hi : 0≤i ∧ i<Zlength xs) (hj : 0≤j ∧ j<Zlength xs) (hk : 0≤k ∧ k<Zlength xs) :
    Znth k (EditSwapAt xs i j) 0 = if k=j then Znth i xs 0 else if k=i then Znth j xs 0 else Znth k xs 0 := by
  unfold EditSwapAt
  have hlen := Zlength_replace_Znth xs i (Znth j xs 0)
  by_cases hkj : k=j
  · subst k
    rw [if_pos rfl,Znth_replace_Znth_Same 0 _ j _ (by omega)]
  · rw [if_neg hkj,Znth_replace_Znth_Diff 0 _ j k _ (by omega) (by omega) (Ne.symm hkj)]
    by_cases hki : k=i
    · subst k
      rw [if_pos rfl,Znth_replace_Znth_Same 0 xs i _ hi]
    · rw [if_neg hki,Znth_replace_Znth_Diff 0 xs i k _ hi hk (Ne.symm hki)]

theorem edit_closure_preserves {A : Type} (step : A → A → Prop) (P : A → Prop)
    (hstep : ∀ x y, step x y → P x → P y) (x y : A) (h : clos_refl_trans step x y) : P x → P y := by
  exact clos_refl_trans_induction_1n (motive := fun x y _ => P x → P y) h
    (fun x hx => hx) (fun x y z hxy hyz ih hx => ih (hstep x y hxy hx))

theorem edit_legal_length (mask before after : List Int) (h : EditLegalSwap mask before after) :
    Zlength after=Zlength before := by
  obtain ⟨i,hi,hj,hm,hm',he⟩ := h
  subst after
  exact edit_swap_length before i (i+1)

theorem edit_reachable_length (mask before after : List Int)
    (h : clos_refl_trans (EditLegalSwap mask) before after) : Zlength after=Zlength before := by
  apply edit_closure_preserves (EditLegalSwap mask) (fun xs => Zlength xs=Zlength before) _ before after h rfl
  intro x y hxy hx
  exact (edit_legal_length mask x y hxy).trans hx

theorem edit_reachable_step (mask before after : List Int) (h : EditLegalSwap mask before after) :
    clos_refl_trans (EditLegalSwap mask) before after :=
  clos_refl_trans_cons h ⟨0,rfl⟩

theorem edit_answer_exists (s1 s2 t1 t2 : List Int) : ∃ answer, EditStringsAnswer s1 s2 t1 t2 answer := by
  apply edit_bounded_maximum (A := List Int × List Int) _ _ (Zlength s1)
  · exact ⟨(s1,s2),⟨0,rfl⟩,⟨0,rfl⟩⟩
  · rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hb := edit_pair_bounds x y
    rw [edit_reachable_length t1 s1 x hx] at hb
    exact hb


theorem edit_map_length {A B : Type} (f : A → B) (xs : List A) :
    Zlength (xs.map f)=Zlength xs := by simp only [Zlength,List.length_map]

theorem edit_map_replace {A B : Type} (f : A → B) (xs : List A) (i : Int) (x : A) :
    (replace_Znth i x xs).map f=replace_Znth i (f x) (xs.map f) := by
  unfold replace_Znth
  generalize i.toNat=k
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons a xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [replace_nth,List.map_cons,ih]

theorem edit_map_read {A B : Type} (f : A → B) (xs : List A) (i : Int) (da : A) (db : B)
    (hi : 0≤i ∧ i<Zlength xs) : Znth i (xs.map f) db=f (Znth i xs da) := by
  have hnat : i.toNat<xs.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  unfold Znth
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa only [List.length_map] using hnat),
    List.getElem?_eq_getElem hnat]
  simp only [Option.getD_some,List.getElem_map]

theorem edit_swap_encode (xs : List Int) (i j : Int)
    (hi : 0≤i ∧ i<Zlength xs) (hj : 0≤j ∧ j<Zlength xs) :
    (EditSwapAt xs i j).map (48+·)=EditSwapAt (xs.map (48+·)) i j := by
  unfold EditSwapAt
  rw [edit_map_replace,edit_map_replace,edit_map_read _ xs i 0 0 hi,edit_map_read _ xs j 0 0 hj]

theorem edit_Forall_replace {A : Type} (P : A → Prop) (xs : List A) (i : Int) (x : A)
    (hxs : Forall P xs) (hx : P x) : Forall P (replace_Znth i x xs) := by
  unfold replace_Znth
  generalize i.toNat=k
  induction hxs generalizing k with
  | nil => cases k <;> exact Forall.nil
  | cons ha ht ih =>
    cases k with
    | zero => exact Forall.cons hx ht
    | succ k => exact Forall.cons ha (ih k)

theorem edit_Forall_read {A : Type} (P : A → Prop) (xs : List A) (i : Int) (d : A)
    (hxs : Forall P xs) (hi : 0≤i ∧ i<Zlength xs) : P (Znth i xs d) := by
  have hnat : i.toNat<xs.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  have hm : Znth i xs d ∈ xs := by
    unfold Znth
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hnat]
    exact List.getElem_mem hnat
  exact hxs.mem hm

theorem edit_Forall_swap (P : Int → Prop) (xs : List Int) (i j : Int)
    (hxs : Forall P xs) (hi : 0≤i ∧ i<Zlength xs) (hj : 0≤j ∧ j<Zlength xs) :
    Forall P (EditSwapAt xs i j) := by
  exact edit_Forall_replace P _ j _
    (edit_Forall_replace P xs i _ hxs (edit_Forall_read P xs j 0 hxs hj))
    (edit_Forall_read P xs i 0 hxs hi)

theorem edit_reachable_Forall (mask before after : List Int) (P : Int → Prop)
    (h : clos_refl_trans (EditLegalSwap mask) before after) (hb : Forall P before) : Forall P after := by
  apply edit_closure_preserves (EditLegalSwap mask) (Forall P) _ before after h hb
  rintro x y ⟨i,hi,hj,hm,hm',rfl⟩ hx
  exact edit_Forall_swap P x i (i+1) hx ⟨hi,by omega⟩ ⟨by omega,hj⟩

theorem edit_swap_conjugate (xs : List Int) (i p j : Int)
    (hip : 0≤i ∧ i<p) (hpj : p<j ∧ j<Zlength xs) :
    EditSwapAt (EditSwapAt (EditSwapAt xs i p) p j) i p=EditSwapAt xs i j := by
  apply (ListLib.list_eq_ext _ _ 0).mpr
  constructor
  · change Zlength _=Zlength _
    simp only [edit_swap_length]
  · intro k hk
    change 0≤k ∧ k<Zlength _ at hk
    simp only [edit_swap_length] at hk
    change Znth k _ 0=Znth k _ 0
    simp (disch := (first | omega | (simp only [edit_swap_length] <;> omega))) only [edit_swap_read]
    split_ifs <;> subst_vars
    all_goals try simp (disch := (first | omega | (simp only [edit_swap_length] <;> omega))) only [edit_swap_read]
    all_goals first | rfl | omega | (split_ifs <;> first | rfl | omega)

theorem edit_swap_reachable (mask xs : List Int) (i j : Int)
    (hi : 0≤i ∧ i≤j) (hj : j<Zlength xs)
    (hm : ∀ k, i≤k ∧ k≤j → Znth k mask 0=49) :
    clos_refl_trans (EditLegalSwap mask) xs (EditSwapAt xs i j) := by
  have main : ∀ d : Nat, ∀ values lo high, high-lo=(d : Int) → 0≤lo → high<Zlength values →
      (∀ k, lo≤k ∧ k≤high → Znth k mask 0=49) →
      clos_refl_trans (EditLegalSwap mask) values (EditSwapAt values lo high) := by
    intro d
    induction d with
    | zero =>
      intro values lo high hd hlo hhigh hmask
      have he : high=lo := by omega
      subst high
      simp only [EditSwapAt,replace_Znth_Znth]
      exact ⟨0,rfl⟩
    | succ d ih =>
      intro values lo high hd hlo hhigh hmask
      by_cases he : high=lo+1
      · subst high
        exact edit_reachable_step mask values _ ⟨lo,hlo,by omega,hmask lo (by omega),hmask (lo+1) (by omega),rfl⟩
      · rw [←edit_swap_conjugate values lo (lo+1) high ⟨hlo,by omega⟩ ⟨by omega,hhigh⟩]
        apply clos_refl_trans_cons (y:=EditSwapAt values lo (lo+1))
          ⟨lo,hlo,by omega,hmask lo (by omega),hmask (lo+1) (by omega),rfl⟩
        apply clos_refl_trans_snoc (y:=EditSwapAt (EditSwapAt values lo (lo+1)) (lo+1) high)
        · apply ih _ (lo+1) high (by omega) (by omega)
            (by rw [edit_swap_length]; exact hhigh)
          intro k hk
          exact hmask k (by omega)
        · refine ⟨lo,hlo,?_,hmask lo (by omega),hmask (lo+1) (by omega),rfl⟩
          simp only [edit_swap_length]
          omega
  exact main (j-i).toNat xs i j (by omega) hi.1 hj hm


theorem edit_region_between (t seg : List Int) (n i j k : Int)
    (hs : EditSegmentMeaning t n seg) (hij : 0≤i ∧ i≤j) (hjk : j≤k ∧ k<n)
    (he : Znth i seg 0=Znth k seg 0) : Znth j seg 0=Znth i seg 0 := by
  have hi := hs i (by omega)
  have hk := hs k (by omega)
  rw [←he] at hk
  apply edit_block_start_unique__build_s2_segments_counts t j _ _ (hs j (by omega))
  exact ⟨⟨hi.1.1,by have := hi.1.2; omega⟩,
    (by intro q hq; exact hk.2.1 q (by omega)),hk.2.2⟩

theorem edit_region_open (t seg : List Int) (n i j : Int)
    (ht : Zlength t=n) (hs : EditSegmentMeaning t n seg) (hij : 0≤i ∧ i<j)
    (hj : j<n) (he : Znth i seg 0=Znth j seg 0) :
    ∀ k, i≤k ∧ k≤j → Znth k (t.map (48+·)) 0=49 := by
  intro k hk
  have hi := hs i (by omega)
  have hj' := hs j (by omega)
  rw [←he] at hj'
  rw [edit_map_read _ t k 0 0 (by omega)]
  by_cases hki : k=i
  · subst k
    have hh := hj'.2.1 (i+1) (by have := hi.1.2; omega)
    have hl : Znth i t 0=1 := by simpa only [edit_edge_open,Int.add_sub_cancel] using hh.1
    omega
  · have hh := hj'.2.1 k (by have := hi.1.2; omega)
    have hr := hh.2
    omega

theorem edit_encode_decode (xs : List Int) : (xs.map (-48+·)).map (48+·)=xs := by
  rw [List.map_map]
  simpa only [Function.comp_def,Int.add_neg_cancel_left] using List.map_id xs

theorem edit_pair_decode (xs ys : List Int) :
    EditPairMatches (xs.map (-48+·)) (ys.map (-48+·))=EditPairMatches xs ys := by
  have h := edit_pair_encode (xs.map (-48+·)) (ys.map (-48+·))
  rw [edit_encode_decode,edit_encode_decode] at h
  exact h.symm

theorem edit_inventory_encode (regions values : List Int) (block bit : Int) :
    EditInventoryCount regions (values.map (48+·)) block (48+bit)=EditInventoryCount regions values block bit := by
  induction regions generalizing values with
  | nil => cases values <;> rfl
  | cons r regions ih =>
    cases values with
    | nil => rfl
    | cons v values =>
      have he : (48+v=48+bit) ↔ v=bit := ⟨Int.add_left_cancel,congrArg (48+·)⟩
      simp only [List.map_cons,edit_inventory_cons,ih,edit_inventory_hit,he]

theorem edit_encode_alphabet (xs : List Int) (h : Forall (fun x => x=0 ∨ x=1) xs) :
    Forall (fun x => x=48 ∨ x=49) (xs.map (48+·)) := by
  induction h with
  | nil => exact Forall.nil
  | cons hx ht ih =>
    apply Forall.cons _ ih
    rcases hx with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem edit_decode_alphabet (xs : List Int) (h : Forall (fun x => x=48 ∨ x=49) xs) :
    Forall (fun x => x=0 ∨ x=1) (xs.map (-48+·)) := by
  induction h with
  | nil => exact Forall.nil
  | cons hx ht ih =>
    apply Forall.cons _ ih
    rcases hx with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem edit_regions_edges (t seg : List Int) (n : Int)
    (ht : Zlength t=n) (hlen : Zlength seg=n) (hs : EditSegmentMeaning t n seg)
    (i : Int) (hi : 0≤i) (hin : i+1<Zlength seg)
    (hl : Znth i (t.map (48+·)) 0=49) (hr : Znth (i+1) (t.map (48+·)) 0=49) :
    Znth i seg 0=Znth (i+1) seg 0 := by
  rw [edit_map_read _ t i 0 0 (by omega)] at hl
  rw [edit_map_read _ t (i+1) 0 0 (by omega)] at hr
  have hedge : edit_edge_open t (i+1) := by
    change Znth (i+1-1) t 0=1 ∧ Znth (i+1) t 0=1
    rw [Int.add_sub_cancel]
    constructor <;> omega
  have hs' := hs i (by omega)
  apply edit_block_start_unique__build_s2_segments_counts t (i+1) _ _ _ (hs (i+1) (by omega))
  refine ⟨⟨hs'.1.1,by have := hs'.1.2; omega⟩,?_,hs'.2.2⟩
  intro k hk
  by_cases he : k=i+1
  · simpa only [he] using hedge
  · exact hs'.2.1 k (by omega)

theorem edit_reachable_inventory (regions mask before after : List Int)
    (hlen : Zlength regions=Zlength before)
    (hedges : ∀ i, 0≤i → i+1<Zlength regions → Znth i mask 0=49 → Znth (i+1) mask 0=49 →
      Znth i regions 0=Znth (i+1) regions 0)
    (hreach : clos_refl_trans (EditLegalSwap mask) before after) (block bit : Int) :
    EditInventoryCount regions after block bit=EditInventoryCount regions before block bit := by
  have hpres : Zlength after=Zlength regions ∧
      EditInventoryCount regions after block bit=EditInventoryCount regions before block bit := by
    apply edit_closure_preserves (EditLegalSwap mask)
      (fun xs => Zlength xs=Zlength regions ∧ EditInventoryCount regions xs block bit=EditInventoryCount regions before block bit)
      _ before after hreach ⟨hlen.symm,rfl⟩
    rintro xs ys ⟨i,hi,hin,hl,hr,rfl⟩ ⟨hx,hcount⟩
    refine ⟨by rw [edit_swap_length]; exact hx,?_⟩
    rw [edit_inventory_swap regions xs i (i+1) block bit hx.symm ⟨hi,by omega⟩ ⟨by omega,hin⟩
      (hedges i hi (by omega) hl hr)]
    exact hcount
  exact hpres.2


theorem edit_zip_range (xs ys : List Int) (hlen : Zlength xs=Zlength ys) :
    xs.zip ys=(edit_zrange (Zlength xs)).map (fun i => (Znth i xs 0,Znth i ys 0)) := by
  have hn : xs.length=ys.length := Int.ofNat_inj.mp hlen
  unfold edit_zrange Zlength
  simp only [Int.ofNat_eq_coe,Int.toNat_natCast,List.map_map]
  apply List.ext_getElem
  · simp only [List.length_zip,List.length_map,List.length_range,hn,Nat.min_self]
  · intro i hi hj
    have hix : i<xs.length := by rw [List.length_zip] at hi; omega
    have hiy : i<ys.length := by omega
    simp only [List.getElem_zip,List.getElem_map,List.getElem_range,Function.comp_apply,Znth,Int.ofNat_eq_coe,Int.toNat_natCast]
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hix,List.getElem?_eq_getElem hiy]
    rfl

theorem edit_block_test_segment (t seg : List Int) (n i block : Int)
    (hs : EditSegmentMeaning t n seg) (hi : 0≤i ∧ i<n) :
    edit_block_startb t i block=decide (Znth i seg 0=block) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,edit_block_startb_true_iff__build_s2_segments_counts]
  constructor
  · intro hb
    exact edit_block_start_unique__build_s2_segments_counts t i _ _ (hs i hi) hb
  · intro he
    rw [←he]
    exact hs i hi

theorem edit_full_inventory (s t seg : List Int) (n block bit : Int)
    (hs : Zlength s=n) (hlen : Zlength seg=n) (hm : EditSegmentMeaning t n seg) :
    EditBlockBitCount s t n block bit=EditInventoryCount seg s block bit := by
  unfold EditBlockBitCount edit_count_bit_in_block_prefix EditInventoryCount
  rw [edit_zip_range seg s (hlen.trans hs.symm),List.filter_map,edit_map_length]
  change Int.ofNat ((edit_zrange (Zlength s)).filter _).length = Int.ofNat ((edit_zrange (Zlength seg)).filter _).length
  rw [hs,hlen]
  congr 2
  apply List.filter_congr
  intro i hi
  have hib := edit_zrange_in_bounds__greedy_common_and_mismatch_steps n i hi
  rw [edit_block_test_segment t seg n i block hm hib]
  simp only [decide_eq_true hib.2,Bool.true_and,edit_bit_atb,Function.comp_apply]

theorem edit_initial_inventory (s t seg zeroes ones : List Int) (n : Int) (output : List Int)
    (hs : Zlength s=n) (ht : Zlength t=n) (hseg : Zlength seg=n)
    (hb : Forall (fun bit => bit=0 ∨ bit=1) s)
    (hm : EditBuildMeaning s t n n seg zeroes ones)
    (hr : clos_refl_trans (EditLegalSwap (t.map (48+·))) (s.map (48+·)) output) :
    EditSuffixInventory seg 0 zeroes ones (output.map (-48+·)) := by
  have hout := edit_reachable_length _ _ _ hr
  rw [edit_map_length] at hout
  refine ⟨by rw [edit_map_length]; omega,
    edit_decode_alphabet output (edit_reachable_Forall _ _ _ _ hr (edit_encode_alphabet s hb)),?_⟩
  have hc : ∀ block bit, EditInventoryCount seg (output.map (-48+·)) block bit=EditBlockBitCount s t n block bit := by
    intro block bit
    rw [←edit_inventory_encode seg (output.map (-48+·)) block bit,edit_encode_decode,
      edit_reachable_inventory seg (t.map (48+·)) (s.map (48+·)) output
        (by rw [edit_map_length,hs,hseg]) (edit_regions_edges t seg n ht hseg hm.1) hr block (48+bit),
      edit_inventory_encode]
    exact (edit_full_inventory s t seg n block bit hs hseg hm.1).symm
  intro block hblock
  have hsub : sublist 0 (Zlength seg) seg=seg := by
    exact sublist_self seg _ rfl
  rw [hsub,hc,hc]
  exact ⟨(hm.2.1 block (by omega)).symm,(hm.2.2 block (by omega)).symm⟩

theorem edit_initial_remaining (s1 s2 t1 t2 seg1 seg2 c10 c11 c20 c21 : List Int) (n : Int)
    (hs1 : Zlength s1=n) (hs2 : Zlength s2=n) (ht1 : Zlength t1=n) (ht2 : Zlength t2=n)
    (hseg1 : Zlength seg1=n) (hseg2 : Zlength seg2=n)
    (hb1 : Forall (fun bit => bit=0 ∨ bit=1) s1) (hb2 : Forall (fun bit => bit=0 ∨ bit=1) s2)
    (hm1 : EditBuildMeaning s1 t1 n n seg1 c10 c11) (hm2 : EditBuildMeaning s2 t2 n n seg2 c20 c21) :
    ∃ answer, EditRemainingMatches s1 s2 t1 t2 seg1 seg2 [] [] 0 c10 c11 c20 c21 answer ∧
      EditStringsAnswer (s1.map (48+·)) (s2.map (48+·)) (t1.map (48+·)) (t2.map (48+·)) answer := by
  obtain ⟨answer,hanswer⟩ := edit_answer_exists (s1.map (48+·)) (s2.map (48+·)) (t1.map (48+·)) (t2.map (48+·))
  refine ⟨answer,?_,hanswer⟩
  obtain ⟨⟨out1,out2⟩,⟨⟨hr1,hr2⟩,hupper⟩,hvalue⟩ := hanswer
  have hinv1 := edit_initial_inventory s1 t1 seg1 c10 c11 n out1 hs1 ht1 hseg1 hb1 hm1 hr1
  have hinv2 := edit_initial_inventory s2 t2 seg2 c20 c21 n out2 hs2 ht2 hseg2 hb2 hm2 hr2
  refine ⟨(out1.map (-48+·),out2.map (-48+·)),⟨⟨?_,hinv1,hinv2⟩,?_⟩,?_⟩
  · change clos_refl_trans (EditLegalSwap (t1.map (48+·))) (s1.map (48+·)) (([]++out1.map (-48+·)).map (48+·)) ∧
      clos_refl_trans (EditLegalSwap (t2.map (48+·))) (s2.map (48+·)) (([]++out2.map (-48+·)).map (48+·))
    simpa only [List.nil_append,edit_encode_decode] using And.intro hr1 hr2
  · rintro ⟨x,y⟩ ⟨hc,hinv⟩
    have hu := hupper (x.map (48+·),y.map (48+·)) hc
    change EditPairMatches (x.map (48+·)) (y.map (48+·))≤EditPairMatches out1 out2 at hu
    change EditPairMatches x y≤EditPairMatches (out1.map (-48+·)) (out2.map (-48+·))
    rw [edit_pair_encode] at hu
    rw [edit_pair_decode]
    exact hu
  · change EditPairMatches (out1.map (-48+·)) (out2.map (-48+·))=answer
    rw [edit_pair_decode]
    exact hvalue


theorem edit_hit_symmetric (a b : Int) : edit_hit a b=edit_hit b a := by
  unfold edit_hit
  by_cases h : a=b
  · rw [if_pos h,if_pos h.symm]
  · rw [if_neg h,if_neg (Ne.symm h)]

theorem edit_pair_swap_flat (xs ys : List Int) (j : Int)
    (hlen : Zlength xs=Zlength ys) (hj : 0<j ∧ j<Zlength xs)
    (he : Znth 0 ys 0=Znth j ys 0) :
    EditPairMatches (EditSwapAt xs 0 j) ys=EditPairMatches xs ys := by
  rw [edit_pair_swap_left xs ys j hlen hj,he]
  omega

theorem edit_pair_swap_both (xs ys : List Int) (j : Int)
    (hlen : Zlength xs=Zlength ys) (hj : 0<j ∧ j<Zlength xs) :
    EditPairMatches (EditSwapAt xs 0 j) (EditSwapAt ys 0 j)=EditPairMatches xs ys := by
  rw [edit_pair_symmetric (EditSwapAt xs 0 j) (EditSwapAt ys 0 j),
    edit_pair_swap_left ys (EditSwapAt xs 0 j) j (by rw [edit_swap_length]; exact hlen.symm) (by omega),
    edit_pair_symmetric ys (EditSwapAt xs 0 j),edit_pair_swap_left xs ys j hlen hj]
  simp (disch := omega) only [edit_swap_read,ite_true,ite_false,if_neg (show (0:Int)≠j by omega)]
  rw [edit_hit_symmetric (Znth 0 ys 0) (Znth j xs 0),
    edit_hit_symmetric (Znth j ys 0) (Znth 0 xs 0),
    edit_hit_symmetric (Znth j ys 0) (Znth j xs 0),
    edit_hit_symmetric (Znth 0 ys 0) (Znth 0 xs 0)]
  omega

theorem edit_swap_front (xs : List Int) (j : Int) (hj : 0<j ∧ j<Zlength xs) :
    Znth 0 (EditSwapAt xs 0 j) 0=Znth j xs 0 := by
  rw [edit_swap_read xs 0 j 0 (by omega) (by omega) (by omega),
    if_neg (show (0:Int)≠j by omega),if_pos rfl]

theorem edit_pair_swap_right_improves (xs ys : List Int) (j : Int)
    (hlen : Zlength xs=Zlength ys) (hj : 0<j ∧ j<Zlength ys)
    (hne : Znth 0 ys 0≠Znth 0 xs 0) (he : Znth j ys 0=Znth 0 xs 0) :
    EditPairMatches xs ys≤EditPairMatches xs (EditSwapAt ys 0 j) := by
  rw [edit_pair_symmetric xs ys,edit_pair_symmetric xs (EditSwapAt ys 0 j)]
  exact edit_pair_swap_improves ys xs j hlen.symm hj hne he

theorem edit_force_common_ordered (P : List Int×List Int → Prop)
    (r1 r2 xs ys : List Int) (m bit j k : Int)
    (hm : 0<m) (hx : Zlength xs=m) (hy : Zlength ys=m)
    (hbinary : Forall (fun x => x=0 ∨ x=1) ys) (hbit : bit=0 ∨ bit=1)
    (hp : P (xs,ys)) (hheads : Znth 0 xs 0=Znth 0 ys 0) (hnot : Znth 0 ys 0≠bit)
    (hjk : 0<j ∧ j≤k) (hkm : k<m) (hxj : Znth j xs 0=bit) (hyk : Znth k ys 0=bit)
    (hr1 : Znth j r1 0=Znth 0 r1 0) (hr2 : Znth k r2 0=Znth 0 r2 0)
    (hclosed : ∀ a b, 0≤a ∧ a≤b → b<m → Znth b r2 0=Znth 0 r2 0 → Znth a r2 0=Znth 0 r2 0)
    (hswap1 : ∀ u v q, P (u,v) → 0<q ∧ q<m → Znth q r1 0=Znth 0 r1 0 → P (EditSwapAt u 0 q,v))
    (hswap2 : ∀ u v q, P (u,v) → 0<q ∧ q<m → Znth q r2 0=Znth 0 r2 0 → P (u,EditSwapAt v 0 q)) :
    ∃ u v, P (u,v) ∧ Znth 0 u 0=bit ∧ Znth 0 v 0=bit ∧ EditPairMatches xs ys≤EditPairMatches u v := by
  have hj2 := hclosed j k (by omega) hkm hr2
  have hh := edit_Forall_read _ ys 0 0 hbinary (by omega)
  have hjb := edit_Forall_read _ ys j 0 hbinary (by omega)
  have hc : Znth j ys 0=bit ∨ Znth j ys 0=Znth 0 ys 0 := by omega
  rcases hc with hc|hf
  · refine ⟨EditSwapAt xs 0 j,EditSwapAt ys 0 j,
      hswap2 _ _ j (hswap1 xs ys j hp (by omega) hr1) (by omega) hj2,?_,?_,?_⟩
    · rw [edit_swap_front xs j (by omega)]; exact hxj
    · rw [edit_swap_front ys j (by omega)]; exact hc
    · rw [edit_pair_swap_both xs ys j (by omega) (by omega)]
  · refine ⟨EditSwapAt xs 0 j,EditSwapAt ys 0 k,
      hswap2 _ _ k (hswap1 xs ys j hp (by omega) hr1) (by omega) hr2,?_,?_,?_⟩
    · rw [edit_swap_front xs j (by omega)]; exact hxj
    · rw [edit_swap_front ys k (by omega)]; exact hyk
    · have hscore := edit_pair_swap_flat xs ys j (by omega) (by omega) hf.symm
      rw [←hscore]
      apply edit_pair_swap_right_improves _ ys k (by rw [edit_swap_length]; omega) (by omega)
      · rw [edit_swap_front xs j (by omega),hxj]; exact hnot
      · rw [edit_swap_front xs j (by omega),hxj]; exact hyk

theorem edit_force_common (P : List Int×List Int → Prop)
    (r1 r2 xs ys : List Int) (m bit j k : Int)
    (hm : 0<m) (hx : Zlength xs=m) (hy : Zlength ys=m)
    (hb1 : Forall (fun x => x=0 ∨ x=1) xs) (hb2 : Forall (fun x => x=0 ∨ x=1) ys)
    (hbit : bit=0 ∨ bit=1) (hp : P (xs,ys))
    (hj : 0≤j ∧ j<m) (hk : 0≤k ∧ k<m) (hxj : Znth j xs 0=bit) (hyk : Znth k ys 0=bit)
    (hr1 : Znth j r1 0=Znth 0 r1 0) (hr2 : Znth k r2 0=Znth 0 r2 0)
    (hc1 : ∀ a b, 0≤a ∧ a≤b → b<m → Znth b r1 0=Znth 0 r1 0 → Znth a r1 0=Znth 0 r1 0)
    (hc2 : ∀ a b, 0≤a ∧ a≤b → b<m → Znth b r2 0=Znth 0 r2 0 → Znth a r2 0=Znth 0 r2 0)
    (hswap1 : ∀ u v q, P (u,v) → 0<q ∧ q<m → Znth q r1 0=Znth 0 r1 0 → P (EditSwapAt u 0 q,v))
    (hswap2 : ∀ u v q, P (u,v) → 0<q ∧ q<m → Znth q r2 0=Znth 0 r2 0 → P (u,EditSwapAt v 0 q)) :
    ∃ u v, P (u,v) ∧ Znth 0 u 0=bit ∧ Znth 0 v 0=bit ∧ EditPairMatches xs ys≤EditPairMatches u v := by
  by_cases hfirst : Znth 0 xs 0=bit
  · by_cases hsecond : Znth 0 ys 0=bit
    · exact ⟨xs,ys,hp,hfirst,hsecond,Int.le_refl _⟩
    · have hkp : 0<k := by
        have hk0 : k≠0 := by intro hk0; exact hsecond (hk0 ▸ hyk)
        omega
      refine ⟨xs,EditSwapAt ys 0 k,hswap2 xs ys k hp ⟨hkp,hk.2⟩ hr2,hfirst,?_,?_⟩
      · rw [edit_swap_front ys k (by omega)]; exact hyk
      · apply edit_pair_swap_right_improves xs ys k (by omega) (by omega)
        · rw [hfirst]; exact hsecond
        · rw [hfirst]; exact hyk
  · by_cases hsecond : Znth 0 ys 0=bit
    · have hjp : 0<j := by
        have hj0 : j≠0 := by intro hj0; exact hfirst (hj0 ▸ hxj)
        omega
      refine ⟨EditSwapAt xs 0 j,ys,hswap1 xs ys j hp ⟨hjp,hj.2⟩ hr1,?_,hsecond,?_⟩
      · rw [edit_swap_front xs j (by omega)]; exact hxj
      · apply edit_pair_swap_improves xs ys j (by omega) (by omega)
        · rw [hsecond]; exact hfirst
        · rw [hsecond]; exact hxj
    · have hjp : 0<j := by
        have hj0 : j≠0 := by intro hj0; exact hfirst (hj0 ▸ hxj)
        omega
      have hkp : 0<k := by
        have hk0 : k≠0 := by intro hk0; exact hsecond (hk0 ▸ hyk)
        omega
      have hh1 := edit_Forall_read _ xs 0 0 hb1 (by omega)
      have hh2 := edit_Forall_read _ ys 0 0 hb2 (by omega)
      have he : Znth 0 xs 0=Znth 0 ys 0 := by omega
      by_cases hjk : j≤k
      · exact edit_force_common_ordered P r1 r2 xs ys m bit j k hm hx hy hb2 hbit hp he hsecond
          ⟨hjp,hjk⟩ hk.2 hxj hyk hr1 hr2 hc2 hswap1 hswap2
      · obtain ⟨v,u,hp',hv,hu,hscore⟩ := edit_force_common_ordered
          (fun outputs => P (outputs.2,outputs.1)) r2 r1 ys xs m bit k j hm hy hx hb1 hbit hp he.symm hfirst
          ⟨hkp,by omega⟩ hj.2 hyk hxj hr2 hr1 hc1
          (fun u v q h hq he => hswap2 v u q h hq he)
          (fun u v q h hq he => hswap1 v u q h hq he)
        refine ⟨u,v,hp',hu,hv,?_⟩
        rw [edit_pair_symmetric xs ys,edit_pair_symmetric u v]
        exact hscore


theorem edit_inventory_bounds (regions values : List Int) (block bit : Int) :
    0≤EditInventoryCount regions values block bit ∧ EditInventoryCount regions values block bit≤Zlength values := by
  have hf := List.length_filter_le (fun p : Int×Int => decide (p.1=block) && decide (p.2=bit)) (regions.zip values)
  have hz : (regions.zip values).length=min regions.length values.length := List.length_zip
  simp only [EditInventoryCount,Zlength,Int.ofNat_eq_coe]
  omega

theorem edit_inventory_positive (regions values : List Int) (block bit : Int)
    (hlen : Zlength regions=Zlength values) (hp : 0<EditInventoryCount regions values block bit) :
    ∃ j, (0≤j ∧ j<Zlength values) ∧ Znth j regions 0=block ∧ Znth j values 0=bit := by
  induction regions generalizing values with
  | nil => change (0:Int)<0 at hp; omega
  | cons r regions ih =>
    cases values with
    | nil => change (0:Int)<0 at hp; omega
    | cons v values =>
      rw [edit_inventory_cons] at hp
      by_cases he : r=block ∧ v=bit
      · refine ⟨0,⟨Int.le_refl _,?_⟩,he.1,he.2⟩
        rw [Zlength_cons]
        have := Zlength_nonneg values
        omega
      · rw [edit_inventory_hit,if_neg he,Int.zero_add] at hp
        have hlen' : Zlength regions=Zlength values := by rw [Zlength_cons,Zlength_cons] at hlen; omega
        obtain ⟨j,hj,hr,hv⟩ := ih values hlen' hp
        refine ⟨j+1,⟨by omega,by rw [Zlength_cons]; omega⟩,?_,?_⟩
        · rw [Znth_cons 0 (j+1) r regions (by omega),Int.add_sub_cancel]; exact hr
        · rw [Znth_cons 0 (j+1) v values (by omega),Int.add_sub_cancel]; exact hv

theorem edit_inventory_at_positive (regions values : List Int) (j block bit : Int)
    (hlen : Zlength regions=Zlength values) (hj : 0≤j ∧ j<Zlength values)
    (hr : Znth j regions 0=block) (hv : Znth j values 0=bit) :
    0<EditInventoryCount regions values block bit := by
  induction regions generalizing values j with
  | nil => have : Zlength ([] : List Int)=0 := rfl; omega
  | cons r regions ih =>
    cases values with
    | nil => change 0≤j ∧ j<0 at hj; omega
    | cons v values =>
      rw [edit_inventory_cons]
      have hlen' : Zlength regions=Zlength values := by
        rw [Zlength_cons,Zlength_cons] at hlen; omega
      by_cases hj0 : j=0
      · subst j
        change r=block at hr
        change v=bit at hv
        rw [edit_inventory_hit,if_pos ⟨hr,hv⟩]
        have hb := edit_inventory_bounds regions values block bit
        omega
      · rw [Znth_cons 0 j r regions (by omega)] at hr
        rw [Znth_cons 0 j v values (by omega)] at hv
        have hi := ih values (j-1) hlen' (by rw [Zlength_cons] at hj; omega) hr hv
        unfold edit_inventory_hit
        split_ifs <;> omega

theorem edit_suffix_regions (regions : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength regions) :
    sublist i (Zlength regions) regions=Znth i regions 0::sublist (i+1) (Zlength regions) regions := by
  rw [sublist_split i (Zlength regions) (i+1) regions (by omega) (by omega),sublist_single 0 i regions hi]
  rfl

theorem edit_count_tail_iff (regions : List Int) (i : Int) (counts : List Int) (label bit target : Int) (values : List Int)
    (hlen : Zlength counts=Zlength regions) (hi : 0≤i ∧ i<Zlength regions)
    (hl : label=Znth i regions 0) (hlr : 0≤label ∧ label<Zlength regions) :
    (∀ block, 0≤block ∧ block<Zlength regions →
      EditInventoryCount (sublist i (Zlength regions) regions) (bit::values) block target=Znth block counts 0) ↔
    (∀ block, 0≤block ∧ block<Zlength regions →
      EditInventoryCount (sublist (i+1) (Zlength regions) regions) values block target=
        Znth block (if bit=target then replace_Znth label (Znth label counts 0-1) counts else counts) 0) := by
  have hpoint : ∀ block, 0≤block ∧ block<Zlength regions →
      (EditInventoryCount (sublist i (Zlength regions) regions) (bit::values) block target=Znth block counts 0 ↔
       EditInventoryCount (sublist (i+1) (Zlength regions) regions) values block target=
        Znth block (if bit=target then replace_Znth label (Znth label counts 0-1) counts else counts) 0) := by
    intro block hb
    rw [edit_suffix_regions regions i hi,edit_inventory_cons,←hl]
    by_cases hbit : bit=target
    · rw [if_pos hbit]
      by_cases he : label=block
      · subst block
        rw [Znth_replace_Znth_Same 0 counts label _ (by omega),edit_inventory_hit,if_pos ⟨rfl,hbit⟩]
        omega
      · rw [Znth_replace_Znth_Diff 0 counts label block _ (by omega) (by omega) he,
          edit_inventory_hit,if_neg (by intro h; exact he h.1),Int.zero_add]
    · rw [if_neg hbit,edit_inventory_hit,if_neg (by intro h; exact hbit h.2),Int.zero_add]
  constructor
  · intro h block hb; exact (hpoint block hb).mp (h block hb)
  · intro h block hb; exact (hpoint block hb).mpr (h block hb)

theorem edit_inventory_tail_iff (regions : List Int) (i : Int) (zeroes ones : List Int) (label bit : Int) (values : List Int)
    (hz : Zlength zeroes=Zlength regions) (ho : Zlength ones=Zlength regions)
    (hi : 0≤i ∧ i<Zlength regions) (hl : label=Znth i regions 0) (hlr : 0≤label ∧ label<Zlength regions)
    (hb : bit=0 ∨ bit=1) :
    EditSuffixInventory regions i zeroes ones (bit::values) ↔
    EditSuffixInventory regions (i+1)
      (if bit=0 then replace_Znth label (Znth label zeroes 0-1) zeroes else zeroes)
      (if bit=1 then replace_Znth label (Znth label ones 0-1) ones else ones) values := by
  have hzero := edit_count_tail_iff regions i zeroes label bit 0 values hz hi hl hlr
  have hone := edit_count_tail_iff regions i ones label bit 1 values ho hi hl hlr
  constructor
  · rintro ⟨hlen,hbinary,hcount⟩
    cases hbinary with
    | cons hhead htail =>
      refine ⟨by rw [Zlength_cons] at hlen; omega,htail,?_⟩
      have hz' := hzero.mp (fun b hb => (hcount b hb).1)
      have ho' := hone.mp (fun b hb => (hcount b hb).2)
      exact fun b hb => ⟨hz' b hb,ho' b hb⟩
  · rintro ⟨hlen,hbinary,hcount⟩
    refine ⟨by rw [Zlength_cons]; omega,Forall.cons hb hbinary,?_⟩
    have hz' := hzero.mpr (fun b hb => (hcount b hb).1)
    have ho' := hone.mpr (fun b hb => (hcount b hb).2)
    exact fun b hb => ⟨hz' b hb,ho' b hb⟩

theorem edit_pair_app (xs ys a b : List Int) (hlen : Zlength xs=Zlength ys) :
    EditPairMatches (xs++a) (ys++b)=EditPairMatches xs ys+EditPairMatches a b := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys=[] := by apply List.eq_nil_of_length_eq_zero; simp only [Zlength,Int.ofNat_eq_coe,List.length_nil] at hlen; omega
    subst ys
    change EditPairMatches a b=0+EditPairMatches a b
    omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [Zlength,Int.ofNat_eq_coe,List.length_nil,List.length_cons] at hlen; omega
    | cons y ys =>
      simp only [List.cons_append,edit_pair_cons]
      rw [ih ys (by rw [Zlength_cons,Zlength_cons] at hlen; omega)]
      omega

theorem edit_completion_cons (s1 s2 t1 t2 prefix1 prefix2 : List Int) (bit1 bit2 : Int) (xs ys : List Int) :
    EditCompletion s1 s2 t1 t2 prefix1 prefix2 (bit1::xs,bit2::ys) ↔
      EditCompletion s1 s2 t1 t2 (prefix1++[bit1]) (prefix2++[bit2]) (xs,ys) := by
  simp only [EditCompletion,List.append_assoc,List.cons_append,List.nil_append]


theorem edit_sublist_length (xs : List Int) (lo hi : Int) (hl : 0≤lo ∧ lo≤hi) (hh : hi≤Zlength xs) :
    Zlength (sublist lo hi xs)=hi-lo := ListLib.Zlength_sublist lo hi xs hl hh

theorem edit_swap_prepend (pref values : List Int) (i j : Int)
    (hi : 0≤i ∧ i<Zlength values) (hj : 0≤j ∧ j<Zlength values) :
    EditSwapAt (pref++values) (Zlength pref+i) (Zlength pref+j)=pref++EditSwapAt values i j := by
  unfold EditSwapAt
  rw [app_Znth2 0 pref values (Zlength pref+i) (by omega),
    app_Znth2 0 pref values (Zlength pref+j) (by omega)]
  have hi' : Zlength pref+i-Zlength pref=i := by omega
  have hj' : Zlength pref+j-Zlength pref=j := by omega
  rw [hi',hj',replace_Znth_app_r (Zlength pref+i) _ pref values (by omega),
    replace_Znth_nothing (Zlength pref+i) pref _ (by omega),hi',
    replace_Znth_app_r (Zlength pref+j) _ pref _ (by omega),
    replace_Znth_nothing (Zlength pref+j) pref _ (by omega),hj']

theorem edit_extension_swap (source t seg : List Int) (n : Int) (pref values : List Int) (i j : Int)
    (ht : Zlength t=n) (hs : EditSegmentMeaning t n seg) (hp : Zlength pref=i)
    (hv : Zlength values=n-i) (hi : 0≤i ∧ i<n) (hj : 0<j ∧ j<Zlength values)
    (he : Znth (i+j) seg 0=Znth i seg 0)
    (hr : clos_refl_trans (EditLegalSwap (t.map (48+·))) source ((pref++values).map (48+·))) :
    clos_refl_trans (EditLegalSwap (t.map (48+·))) source ((pref++EditSwapAt values 0 j).map (48+·)) := by
  apply (rt2_trans_ins (List Int) (EditLegalSwap (t.map (48+·)))).trans source ((pref++values).map (48+·)) _ hr
  rw [←edit_swap_prepend pref values 0 j (by omega) (by omega),edit_swap_encode _ _ _
    (by rw [Zlength_app]; omega) (by rw [Zlength_app]; omega),hp,Int.add_zero]
  apply edit_swap_reachable _ _ i (i+j) (by omega) (by rw [edit_map_length,Zlength_app]; omega)
  exact edit_region_open t seg n i (i+j) ht hs (by omega) (by omega) he.symm

theorem edit_suffix_swap (regions : List Int) (i : Int) (zeroes ones values : List Int) (j : Int)
    (hi : 0≤i ∧ i<Zlength regions) (hs : EditSuffixInventory regions i zeroes ones values)
    (hj : 0<j ∧ j<Zlength values) (he : Znth (i+j) regions 0=Znth i regions 0) :
    EditSuffixInventory regions i zeroes ones (EditSwapAt values 0 j) := by
  rcases hs with ⟨hlen,hbinary,hcounts⟩
  refine ⟨by rw [edit_swap_length]; exact hlen,edit_Forall_swap _ values 0 j hbinary (by omega) (by omega),?_⟩
  intro block hb
  have hlen' : Zlength (sublist i (Zlength regions) regions)=Zlength values := by
    rw [edit_sublist_length regions i (Zlength regions) (by omega) (Int.le_refl _)]
    exact hlen.symm
  have he' : Znth 0 (sublist i (Zlength regions) regions) 0=Znth j (sublist i (Zlength regions) regions) 0 := by
    rw [Znth_sublist 0 i 0 (Zlength regions) regions hi.1 (by omega),
      Znth_sublist 0 i j (Zlength regions) regions hi.1 (by omega),Int.zero_add,Int.add_comm j i]
    exact he.symm
  rw [edit_inventory_swap _ values 0 j block 0 hlen' (by omega) (by omega) he',
    edit_inventory_swap _ values 0 j block 1 hlen' (by omega) (by omega) he']
  exact hcounts block hb

theorem edit_feasible_swap_left (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n : Int) (x y : List Int) (j : Int)
    (ht : Zlength t1=n) (hseg : Zlength seg1=n) (hs : EditSegmentMeaning t1 n seg1)
    (hp : Zlength prefix1=i) (hi : 0≤i ∧ i<n)
    (hf : EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (x,y))
    (hj : 0<j ∧ j<n-i) (he : Znth (i+j) seg1 0=Znth i seg1 0) :
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (EditSwapAt x 0 j,y) := by
  rcases hf with ⟨⟨hc1,hc2⟩,hi1,hi2⟩
  have hx : Zlength x=n-i := by simpa only [Prod.fst,hseg] using hi1.1
  exact ⟨⟨edit_extension_swap _ t1 seg1 n prefix1 x i j ht hs hp hx hi (by omega) he hc1,hc2⟩,
    edit_suffix_swap seg1 i c10 c11 x j (by omega) hi1 (by omega) he,hi2⟩

theorem edit_feasible_swap_right (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n : Int) (x y : List Int) (j : Int)
    (ht : Zlength t2=n) (hseg : Zlength seg2=n) (hs : EditSegmentMeaning t2 n seg2)
    (hp : Zlength prefix2=i) (hi : 0≤i ∧ i<n)
    (hf : EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (x,y))
    (hj : 0<j ∧ j<n-i) (he : Znth (i+j) seg2 0=Znth i seg2 0) :
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (x,EditSwapAt y 0 j) := by
  rcases hf with ⟨⟨hc1,hc2⟩,hi1,hi2⟩
  have hy : Zlength y=n-i := by simpa only [Prod.snd,hseg] using hi2.1
  exact ⟨⟨hc1,edit_extension_swap _ t2 seg2 n prefix2 y i j ht hs hp hy hi (by omega) he hc2⟩,
    hi1,edit_suffix_swap seg2 i c20 c21 y j (by omega) hi2 (by omega) he⟩

theorem edit_region_suffix_closed (t seg : List Int) (n i : Int)
    (hs : EditSegmentMeaning t n seg) (hi : 0≤i ∧ i<n) :
    ∀ j k, 0≤j ∧ j≤k → k<n-i → Znth k (sublist i n seg) 0=Znth 0 (sublist i n seg) 0 →
      Znth j (sublist i n seg) 0=Znth 0 (sublist i n seg) 0 := by
  intro j k hj hk he
  rw [Znth_sublist 0 i k n seg hi.1 (by omega),Znth_sublist 0 i 0 n seg hi.1 (by omega),Int.zero_add] at he
  rw [Znth_sublist 0 i j n seg hi.1 (by omega),Znth_sublist 0 i 0 n seg hi.1 (by omega),Int.zero_add]
  exact edit_region_between t seg n i (j+i) (k+i) hs (by omega) (by omega) he.symm


theorem edit_remaining_force_common (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b bit answer : Int)
    (ht1 : Zlength t1=n) (ht2 : Zlength t2=n) (hseg1 : Zlength seg1=n) (hseg2 : Zlength seg2=n)
    (hm1 : EditSegmentMeaning t1 n seg1) (hm2 : EditSegmentMeaning t2 n seg2)
    (hp1 : Zlength prefix1=i) (hp2 : Zlength prefix2=i) (hi : 0≤i ∧ i<n)
    (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hbit : bit=0 ∨ bit=1)
    (hpos1 : 0<Znth a (if bit=0 then c10 else c11) 0)
    (hpos2 : 0<Znth b (if bit=0 then c20 else c21) 0)
    (hmax : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    ∃ xs ys, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit::xs,bit::ys) ∧
      EditPairMatches (bit::xs) (bit::ys)=answer := by
  obtain ⟨⟨xs,ys⟩,⟨hfeasible,hupper⟩,hvalue⟩ := hmax
  rcases hfeasible with ⟨hcompletion,⟨hx,hbinary1,hcounts1⟩,⟨hy,hbinary2,hcounts2⟩⟩
  change Zlength xs=Zlength seg1-i at hx
  change Zlength ys=Zlength seg2-i at hy
  rw [hseg1] at hx hcounts1
  rw [hseg2] at hy hcounts2
  let r1 := sublist i n seg1
  let r2 := sublist i n seg2
  have hrlen1 : Zlength r1=n-i := edit_sublist_length seg1 i n (by omega) (by omega)
  have hrlen2 : Zlength r2=n-i := edit_sublist_length seg2 i n (by omega) (by omega)
  have hrhead1 : Znth 0 r1 0=a := by
    change Znth 0 (sublist i n seg1) 0=a
    rw [Znth_sublist 0 i 0 n seg1 hi.1 (by omega),Int.zero_add]
    exact ha.symm
  have hrhead2 : Znth 0 r2 0=b := by
    change Znth 0 (sublist i n seg2) 0=b
    rw [Znth_sublist 0 i 0 n seg2 hi.1 (by omega),Int.zero_add]
    exact hb.symm
  have hcount1 : 0<EditInventoryCount r1 xs a bit := by
    rcases hbit with rfl|rfl
    · rw [(hcounts1 a har).1]; simpa only [ite_true] using hpos1
    · rw [(hcounts1 a har).2]; simpa only [Int.reduceEq,ite_false] using hpos1
  have hcount2 : 0<EditInventoryCount r2 ys b bit := by
    rcases hbit with rfl|rfl
    · rw [(hcounts2 b hbr).1]; simpa only [ite_true] using hpos2
    · rw [(hcounts2 b hbr).2]; simpa only [Int.reduceEq,ite_false] using hpos2
  obtain ⟨j,hj,hjr,hjbit⟩ := edit_inventory_positive r1 xs a bit (by omega) hcount1
  obtain ⟨k,hk,hkr,hkbit⟩ := edit_inventory_positive r2 ys b bit (by omega) hcount2
  have hswap1 : ∀ u v q, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (u,v) →
      0<q ∧ q<n-i → Znth q r1 0=Znth 0 r1 0 →
      EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (EditSwapAt u 0 q,v) := by
    intro u v q hf hq hlabel
    change Znth q (sublist i n seg1) 0=Znth 0 (sublist i n seg1) 0 at hlabel
    rw [Znth_sublist 0 i q n seg1 hi.1 (by omega),Znth_sublist 0 i 0 n seg1 hi.1 (by omega),Int.zero_add,Int.add_comm q i] at hlabel
    exact edit_feasible_swap_left s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n u v q ht1 hseg1 hm1 hp1 hi hf hq hlabel
  have hswap2 : ∀ u v q, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (u,v) →
      0<q ∧ q<n-i → Znth q r2 0=Znth 0 r2 0 →
      EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (u,EditSwapAt v 0 q) := by
    intro u v q hf hq hlabel
    change Znth q (sublist i n seg2) 0=Znth 0 (sublist i n seg2) 0 at hlabel
    rw [Znth_sublist 0 i q n seg2 hi.1 (by omega),Znth_sublist 0 i 0 n seg2 hi.1 (by omega),Int.zero_add,Int.add_comm q i] at hlabel
    exact edit_feasible_swap_right s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n u v q ht2 hseg2 hm2 hp2 hi hf hq hlabel
  have hf : EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (xs,ys) :=
    ⟨hcompletion,⟨by simpa only [Prod.fst,hseg1] using hx,hbinary1,by simpa only [hseg1] using hcounts1⟩,
      ⟨by simpa only [Prod.snd,hseg2] using hy,hbinary2,by simpa only [hseg2] using hcounts2⟩⟩
  obtain ⟨u,v,hf',hu,hv,hscore⟩ := edit_force_common
    (EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21)
    r1 r2 xs ys (n-i) bit j k (by omega) hx hy hbinary1 hbinary2 hbit hf
    (by omega) (by omega) hjbit hkbit (hjr.trans hrhead1.symm) (hkr.trans hrhead2.symm)
    (edit_region_suffix_closed t1 seg1 n i hm1 hi) (edit_region_suffix_closed t2 seg2 n i hm2 hi) hswap1 hswap2
  have hupper' := hupper (u,v) hf'
  change EditPairMatches u v≤EditPairMatches xs ys at hupper'
  change EditPairMatches xs ys=answer at hvalue
  have hvalue' : EditPairMatches u v=answer := by omega
  have hul : Zlength u=n-i := by simpa only [Prod.fst,hseg1] using hf'.2.1.1
  have hvl : Zlength v=n-i := by simpa only [Prod.snd,hseg2] using hf'.2.2.1
  cases u with
  | nil => change (0:Int)=n-i at hul; omega
  | cons head1 us =>
    cases v with
    | nil => change (0:Int)=n-i at hvl; omega
    | cons head2 vs =>
      change head1=bit at hu
      change head2=bit at hv
      subst head1 head2
      exact ⟨us,vs,hf',hvalue'⟩

theorem edit_suffix_head_available (regions : List Int) (i : Int) (zeroes ones : List Int)
    (label bit : Int) (values : List Int) (hi : 0≤i ∧ i<Zlength regions)
    (hl : label=Znth i regions 0) (hlr : 0≤label ∧ label<Zlength regions)
    (hs : EditSuffixInventory regions i zeroes ones (bit::values)) :
    (bit=0 → 0<Znth label zeroes 0) ∧ (bit=1 → 0<Znth label ones 0) := by
  have hc := hs.2.2 label hlr
  rw [edit_suffix_regions regions i hi,edit_inventory_cons,edit_inventory_cons,←hl] at hc
  have hz := edit_inventory_bounds (sublist (i+1) (Zlength regions) regions) values label 0
  have ho := edit_inventory_bounds (sublist (i+1) (Zlength regions) regions) values label 1
  constructor
  · intro hb
    rw [hb,edit_inventory_hit,if_pos ⟨rfl,rfl⟩] at hc
    omega
  · intro hb
    rw [hb] at hc
    have hh := hc.2
    rw [edit_inventory_hit,if_pos ⟨rfl,rfl⟩] at hh
    omega

theorem edit_remaining_heads (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b answer : Int)
    (hseg1 : Zlength seg1=n) (hseg2 : Zlength seg2=n) (hi : 0≤i ∧ i<n)
    (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hmax : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    ∃ bit1 bit2 xs ys,
      EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit1::xs,bit2::ys) ∧
      EditPairMatches (bit1::xs) (bit2::ys)=answer ∧ (bit1=0 ∨ bit1=1) ∧ (bit2=0 ∨ bit2=1) ∧
      (bit1=0 → 0<Znth a c10 0) ∧ (bit1=1 → 0<Znth a c11 0) ∧
      (bit2=0 → 0<Znth b c20 0) ∧ (bit2=1 → 0<Znth b c21 0) := by
  obtain ⟨⟨u,v⟩,⟨hf,hu⟩,hv⟩ := hmax
  have hul : Zlength u=n-i := by simpa only [Prod.fst,hseg1] using hf.2.1.1
  have hvl : Zlength v=n-i := by simpa only [Prod.snd,hseg2] using hf.2.2.1
  cases u with
  | nil => change (0:Int)=n-i at hul; omega
  | cons bit1 xs =>
    cases v with
    | nil => change (0:Int)=n-i at hvl; omega
    | cons bit2 ys =>
      have hbit1 : bit1=0 ∨ bit1=1 := edit_Forall_read _ (bit1::xs) 0 0 hf.2.1.2.1 (by omega)
      have hbit2 : bit2=0 ∨ bit2=1 := edit_Forall_read _ (bit2::ys) 0 0 hf.2.2.2.1 (by omega)
      have hc1 := edit_suffix_head_available seg1 i c10 c11 a bit1 xs (by omega) ha (by omega) hf.2.1
      have hc2 := edit_suffix_head_available seg2 i c20 c21 b bit2 ys (by omega) hb (by omega) hf.2.2
      exact ⟨bit1,bit2,xs,ys,hf,hv,hbit1,hbit2,hc1.1,hc1.2,hc2.1,hc2.2⟩

theorem edit_remaining_force_zero_one (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b answer : Int)
    (hseg1 : Zlength seg1=n) (hseg2 : Zlength seg2=n) (hi : 0≤i ∧ i<n)
    (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hno0 : ¬(0<Znth a c10 0 ∧ 0<Znth b c20 0)) (hno1 : ¬(0<Znth a c11 0 ∧ 0<Znth b c21 0))
    (hpos : 0<Znth a c10 0)
    (hmax : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    ∃ xs ys, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (0::xs,1::ys) ∧
      EditPairMatches (0::xs) (1::ys)=answer := by
  obtain ⟨bit1,bit2,xs,ys,hf,hv,hb1,hb2,h10,h11,h20,h21⟩ :=
    edit_remaining_heads s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer
      hseg1 hseg2 hi ha hb har hbr hmax
  have he1 : bit1=0 := by omega
  have he2 : bit2=1 := by omega
  subst bit1 bit2
  exact ⟨xs,ys,hf,hv⟩

theorem edit_remaining_force_one_zero (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b answer : Int)
    (hseg1 : Zlength seg1=n) (hseg2 : Zlength seg2=n) (hi : 0≤i ∧ i<n)
    (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hno1 : ¬(0<Znth a c11 0 ∧ 0<Znth b c21 0)) (hnon : Znth a c10 0≤0)
    (hmax : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    ∃ xs ys, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (1::xs,0::ys) ∧
      EditPairMatches (1::xs) (0::ys)=answer := by
  obtain ⟨bit1,bit2,xs,ys,hf,hv,hb1,hb2,h10,h11,h20,h21⟩ :=
    edit_remaining_heads s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer
      hseg1 hseg2 hi ha hb har hbr hmax
  have he1 : bit1=1 := by omega
  have he2 : bit2=0 := by omega
  subst bit1 bit2
  exact ⟨xs,ys,hf,hv⟩


theorem edit_feasible_cons_iff (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b bit1 bit2 : Int) (xs ys : List Int)
    (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (h10 : Zlength c10=n) (h11 : Zlength c11=n) (h20 : Zlength c20=n) (h21 : Zlength c21=n)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hbit1 : bit1=0 ∨ bit1=1) (hbit2 : bit2=0 ∨ bit2=1) :
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit1::xs,bit2::ys) ↔
    EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 (prefix1++[bit1]) (prefix2++[bit2]) (i+1)
      (if bit1=0 then replace_Znth a (Znth a c10 0-1) c10 else c10)
      (if bit1=1 then replace_Znth a (Znth a c11 0-1) c11 else c11)
      (if bit2=0 then replace_Znth b (Znth b c20 0-1) c20 else c20)
      (if bit2=1 then replace_Znth b (Znth b c21 0-1) c21 else c21) (xs,ys) := by
  unfold EditFeasibleSuffix
  rw [edit_completion_cons,
    edit_inventory_tail_iff seg1 i c10 c11 a bit1 xs (by omega) (by omega) (by omega) ha (by omega) hbit1,
    edit_inventory_tail_iff seg2 i c20 c21 b bit2 ys (by omega) (by omega) (by omega) hb (by omega) hbit2]

theorem edit_maximum_strip (P Q : List Int×List Int → Prop) (bit1 bit2 answer : Int)
    (hm : MaxMinLib.max_value_of_subset (LE.le (α:=Int)) P (fun o => EditPairMatches o.1 o.2) answer)
    (he : ∀ xs ys, P (bit1::xs,bit2::ys) ↔ Q (xs,ys))
    (hf : ∃ xs ys, P (bit1::xs,bit2::ys) ∧ EditPairMatches (bit1::xs) (bit2::ys)=answer) :
    MaxMinLib.max_value_of_subset (LE.le (α:=Int)) Q (fun o => EditPairMatches o.1 o.2) (answer-edit_hit bit1 bit2) := by
  obtain ⟨best,⟨hb,hu⟩,hv⟩ := hm
  obtain ⟨xs,ys,hp,hvalue⟩ := hf
  refine ⟨(xs,ys),⟨(he xs ys).mp hp,?_⟩,?_⟩
  · rintro ⟨u,v⟩ hq
    have hupper := hu (bit1::u,bit2::v) ((he u v).mpr hq)
    change EditPairMatches (bit1::u) (bit2::v)≤EditPairMatches best.1 best.2 at hupper
    change EditPairMatches best.1 best.2=answer at hv
    change EditPairMatches u v≤EditPairMatches xs ys
    rw [edit_pair_cons] at hupper hvalue
    omega
  · change EditPairMatches xs ys=answer-edit_hit bit1 bit2
    rw [edit_pair_cons] at hvalue
    omega

theorem edit_remaining_strip (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b bit1 bit2 answer : Int)
    (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (h10 : Zlength c10=n) (h11 : Zlength c11=n) (h20 : Zlength c20=n) (h21 : Zlength c21=n)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hbit1 : bit1=0 ∨ bit1=1) (hbit2 : bit2=0 ∨ bit2=1)
    (hm : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer)
    (hf : ∃ xs ys, EditFeasibleSuffix s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 (bit1::xs,bit2::ys) ∧
      EditPairMatches (bit1::xs) (bit2::ys)=answer) :
    EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1++[bit1]) (prefix2++[bit2]) (i+1)
      (if bit1=0 then replace_Znth a (Znth a c10 0-1) c10 else c10)
      (if bit1=1 then replace_Znth a (Znth a c11 0-1) c11 else c11)
      (if bit2=0 then replace_Znth b (Znth b c20 0-1) c20 else c20)
      (if bit2=1 then replace_Znth b (Znth b c21 0-1) c21 else c21) (answer-edit_hit bit1 bit2) := by
  apply edit_maximum_strip _ _ bit1 bit2 answer hm _ hf
  intro xs ys
  exact edit_feasible_cons_iff s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit1 bit2 xs ys
    hs1 hs2 h10 h11 h20 h21 hi ha hb har hbr hbit1 hbit2

theorem edit_Forall_of_read (P : Int → Prop) (xs : List Int)
    (h : ∀ i, 0≤i ∧ i<Zlength xs → P (Znth i xs 0)) : Forall P xs := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
  have hp := h (i : Int) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
  change P (xs.getD i 0) at hp
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] at hp
  exact hp

theorem edit_suffix_count_bounds (regions : List Int) (i : Int) (zeroes ones values : List Int) (n : Int)
    (hr : Zlength regions=n) (hz : Zlength zeroes=n) (ho : Zlength ones=n) (hi : 0≤i)
    (hs : EditSuffixInventory regions i zeroes ones values) :
    (Forall (LE.le (α:=Int) 0) zeroes ∧ Forall (GE.ge (α:=Int) n) zeroes) ∧
    (Forall (LE.le (α:=Int) 0) ones ∧ Forall (GE.ge (α:=Int) n) ones) := by
  have hlen := hs.1
  have hc := hs.2.2
  constructor <;> constructor <;> apply edit_Forall_of_read <;> intro block hb
  · have h := (hc block (by omega)).1
    have hi := edit_inventory_bounds (sublist i (Zlength regions) regions) values block 0
    change 0≤Znth block zeroes 0
    omega
  · have h := (hc block (by omega)).1
    have hi := edit_inventory_bounds (sublist i (Zlength regions) regions) values block 0
    change Znth block zeroes 0≤n
    omega
  · have h := (hc block (by omega)).2
    have hi := edit_inventory_bounds (sublist i (Zlength regions) regions) values block 1
    change 0≤Znth block ones 0
    omega
  · have h := (hc block (by omega)).2
    have hi := edit_inventory_bounds (sublist i (Zlength regions) regions) values block 1
    change Znth block ones 0≤n
    omega

theorem edit_remaining_empty (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 c10 c11 c20 c21 : List Int) (n answer : Int)
    (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (hm : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 n c10 c11 c20 c21 answer) : answer=0 := by
  obtain ⟨⟨xs,ys⟩,⟨hf,hu⟩,hv⟩ := hm
  have hx : xs=[] := by
    apply List.eq_nil_of_length_eq_zero
    have := hf.2.1.1
    change Zlength xs=Zlength seg1-n at this
    rw [hs1] at this
    simp only [Zlength,Int.ofNat_eq_coe] at this
    omega
  subst xs
  change (0:Int)=answer at hv
  exact hv.symm

theorem edit_remaining_common_step (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b bit answer : Int)
    (ht1 : Zlength t1=n) (ht2 : Zlength t2=n) (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (h10 : Zlength c10=n) (h11 : Zlength c11=n) (h20 : Zlength c20=n) (h21 : Zlength c21=n)
    (hmeaning1 : EditSegmentMeaning t1 n seg1) (hmeaning2 : EditSegmentMeaning t2 n seg2)
    (hp1 : Zlength prefix1=i) (hp2 : Zlength prefix2=i)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hbit : bit=0 ∨ bit=1)
    (hpos1 : 0<Znth a (if bit=0 then c10 else c11) 0)
    (hpos2 : 0<Znth b (if bit=0 then c20 else c21) 0)
    (hm : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1++[bit]) (prefix2++[bit]) (i+1)
      (if bit=0 then replace_Znth a (Znth a c10 0-1) c10 else c10)
      (if bit=1 then replace_Znth a (Znth a c11 0-1) c11 else c11)
      (if bit=0 then replace_Znth b (Znth b c20 0-1) c20 else c20)
      (if bit=1 then replace_Znth b (Znth b c21 0-1) c21 else c21) (answer-1) := by
  have hf := edit_remaining_force_common s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit answer
    ht1 ht2 hs1 hs2 hmeaning1 hmeaning2 hp1 hp2 hi ha hb har hbr hbit hpos1 hpos2 hm
  have hn := edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b bit bit answer
    hs1 hs2 h10 h11 h20 h21 hi ha hb har hbr hbit hbit hm hf
  simpa only [edit_hit,ite_true] using hn

theorem edit_remaining_zero_one_step (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b answer : Int)
    (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (h10 : Zlength c10=n) (h11 : Zlength c11=n) (h20 : Zlength c20=n) (h21 : Zlength c21=n)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hno0 : ¬(0<Znth a c10 0 ∧ 0<Znth b c20 0)) (hno1 : ¬(0<Znth a c11 0 ∧ 0<Znth b c21 0))
    (hpos : 0<Znth a c10 0)
    (hm : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1++[0]) (prefix2++[1]) (i+1)
      (replace_Znth a (Znth a c10 0-1) c10) c11 c20 (replace_Znth b (Znth b c21 0-1) c21) answer := by
  have hf := edit_remaining_force_zero_one s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer
    hs1 hs2 hi ha hb har hbr hno0 hno1 hpos hm
  have hn := edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b 0 1 answer
    hs1 hs2 h10 h11 h20 h21 hi ha hb har hbr (Or.inl rfl) (Or.inr rfl) hm hf
  simpa only [edit_hit,Int.reduceEq,ite_true,ite_false,Int.sub_zero] using hn

theorem edit_remaining_one_zero_step (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n a b answer : Int)
    (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (h10 : Zlength c10=n) (h11 : Zlength c11=n) (h20 : Zlength c20=n) (h21 : Zlength c21=n)
    (hi : 0≤i ∧ i<n) (ha : a=Znth i seg1 0) (hb : b=Znth i seg2 0) (har : 0≤a ∧ a<n) (hbr : 0≤b ∧ b<n)
    (hno1 : ¬(0<Znth a c11 0 ∧ 0<Znth b c21 0)) (hnon : Znth a c10 0≤0)
    (hm : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    EditRemainingMatches s1 s2 t1 t2 seg1 seg2 (prefix1++[1]) (prefix2++[0]) (i+1)
      c10 (replace_Znth a (Znth a c11 0-1) c11) (replace_Znth b (Znth b c20 0-1) c20) c21 answer := by
  have hf := edit_remaining_force_one_zero s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b answer
    hs1 hs2 hi ha hb har hbr hno1 hnon hm
  have hn := edit_remaining_strip s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 n a b 1 0 answer
    hs1 hs2 h10 h11 h20 h21 hi ha hb har hbr (Or.inr rfl) (Or.inl rfl) hm hf
  simpa only [edit_hit,Int.reduceEq,ite_true,ite_false,Int.sub_zero] using hn

theorem edit_remaining_count_bounds (s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 : List Int) (i : Int)
    (c10 c11 c20 c21 : List Int) (n answer : Int)
    (hs1 : Zlength seg1=n) (hs2 : Zlength seg2=n)
    (h10 : Zlength c10=n) (h11 : Zlength c11=n) (h20 : Zlength c20=n) (h21 : Zlength c21=n) (hi : 0≤i)
    (hm : EditRemainingMatches s1 s2 t1 t2 seg1 seg2 prefix1 prefix2 i c10 c11 c20 c21 answer) :
    (Forall (LE.le (α:=Int) 0) c10 ∧ Forall (GE.ge (α:=Int) n) c10) ∧
    (Forall (LE.le (α:=Int) 0) c11 ∧ Forall (GE.ge (α:=Int) n) c11) ∧
    (Forall (LE.le (α:=Int) 0) c20 ∧ Forall (GE.ge (α:=Int) n) c20) ∧
    (Forall (LE.le (α:=Int) 0) c21 ∧ Forall (GE.ge (α:=Int) n) c21) := by
  obtain ⟨⟨x,y⟩,⟨hf,hu⟩,hv⟩ := hm
  have hc1 := edit_suffix_count_bounds seg1 i c10 c11 x n hs1 h10 h11 hi hf.2.1
  have hc2 := edit_suffix_count_bounds seg2 i c20 c21 y n hs2 h20 h21 hi hf.2.2
  exact ⟨hc1.1,hc1.2,hc2⟩


theorem edit_zero_read (xs : List Int) (i : Int) (h : Forall (Eq (0 : Int)) xs) : Znth i xs 0=0 := by
  unfold Znth
  generalize i.toNat=k
  induction h generalizing k with
  | nil => rfl
  | cons hx ht ih =>
    cases k with
    | zero => exact hx.symm
    | succ k => exact ih k

theorem edit_bounded_read (xs : List Int) (i lo hi : Int)
    (hl : Forall (LE.le (α:=Int) lo) xs) (hh : Forall (GE.ge (α:=Int) hi) xs) (hz : lo≤0 ∧ 0≤hi) :
    lo≤Znth i xs 0 ∧ Znth i xs 0≤hi := by
  unfold Znth
  rw [List.getD_eq_getElem?_getD]
  by_cases hin : i.toNat<xs.length
  · rw [List.getElem?_eq_getElem hin]
    exact ⟨hl.mem (List.getElem_mem hin),hh.mem (List.getElem_mem hin)⟩
  · rw [List.getElem?_eq_none (by omega)]
    exact hz

theorem edit_counts_bounds (s t : List Int) (n upto : Int) (zeroes ones : List Int)
    (hn : 0≤n) (hs : Zlength s=n) (hz : Zlength zeroes=n) (ho : Zlength ones=n)
    (hc : EditCountsMeaning s t n upto zeroes ones) :
    (Forall (LE.le (α:=Int) 0) zeroes ∧ Forall (GE.ge (α:=Int) n) zeroes) ∧
    (Forall (LE.le (α:=Int) 0) ones ∧ Forall (GE.ge (α:=Int) n) ones) := by
  constructor <;> constructor <;> apply edit_Forall_of_read <;> intro block hb
  · change 0≤Znth block zeroes 0
    rw [hc.1 block (by omega)]
    exact (edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts s t n upto block 0 hs hn).1
  · change Znth block zeroes 0≤n
    rw [hc.1 block (by omega)]
    exact (edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts s t n upto block 0 hs hn).2
  · change 0≤Znth block ones 0
    rw [hc.2 block (by omega)]
    exact (edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts s t n upto block 1 hs hn).1
  · change Znth block ones 0≤n
    rw [hc.2 block (by omega)]
    exact (edit_count_bit_in_block_prefix_bound_n__build_s2_segments_counts s t n upto block 1 hs hn).2

theorem edit_zero_bounds (xs : List Int) (n : Int) (hn : 0≤n) (hz : Forall (Eq (0 : Int)) xs) :
    Forall (LE.le (α:=Int) 0) xs ∧ Forall (GE.ge (α:=Int) n) xs := by
  constructor <;> apply edit_Forall_of_read <;> intro i hi
  · change 0≤Znth i xs 0
    rw [edit_zero_read xs i hz]
  · change Znth i xs 0≤n
    rw [edit_zero_read xs i hz]
    exact hn

theorem edit_build_first_zero (s t : List Int) (n : Int) (zeroes ones : List Int)
    (hn : 1≤n) (hs : Zlength s=n) (hz : Zlength zeroes=n) (ho : Zlength ones=n)
    (hzero : Forall (Eq (0 : Int)) zeroes) (hone : Forall (Eq (0 : Int)) ones) (hbit : Znth 0 s 0=0) :
    EditBuildMeaning s t n 1 [0] (replace_Znth 0 (Znth 0 zeroes 0+1) zeroes) ones := by
  constructor
  · intro idx hi
    have he : idx=0 := by omega
    subst idx
    change EditBlockStart t 0 0
    exact ⟨⟨Int.le_refl _,Int.le_refl _⟩,(by intro k hk; omega),Or.inl rfl⟩
  · have hc := EditCountsForPrefix_initial_zero__zeroing_and_base_build s t n zeroes ones hn hs hbit
      ⟨hz,fun i hi => edit_zero_read zeroes i hzero⟩ ⟨ho,fun i hi => edit_zero_read ones i hone⟩
    exact hc.2.2

theorem edit_build_first_one (s t : List Int) (n : Int) (zeroes ones : List Int)
    (hn : 1≤n) (hs : Zlength s=n) (hz : Zlength zeroes=n) (ho : Zlength ones=n)
    (hzero : Forall (Eq (0 : Int)) zeroes) (hone : Forall (Eq (0 : Int)) ones)
    (hl : Forall (LE.le (α:=Int) 0) s) (hh : Forall (GE.ge (α:=Int) 1) s) (hbit : Znth 0 s 0≠0) :
    EditBuildMeaning s t n 1 [0] zeroes (replace_Znth 0 (Znth 0 ones 0+1) ones) := by
  constructor
  · intro idx hi
    have he : idx=0 := by omega
    subst idx
    change EditBlockStart t 0 0
    exact ⟨⟨Int.le_refl _,Int.le_refl _⟩,(by intro k hk; omega),Or.inl rfl⟩
  · have hc := EditCountsForPrefix_initial_one__zeroing_and_base_build s t n zeroes ones hn hs
      (fun idx hi => edit_bounded_read s idx 0 1 hl hh (by omega)) hbit
      ⟨hz,fun i hi => edit_zero_read zeroes i hzero⟩ ⟨ho,fun i hi => edit_zero_read ones i hone⟩
    exact hc.2.2

theorem edit_counts_inc_zero (s t : List Int) (n i : Int) (seg zeroes ones : List Int) (block : Int)
    (hs : Zlength s=n) (hz : Zlength zeroes=n) (ho : Zlength ones=n) (hseg : Zlength seg=i+1)
    (hi : 0≤i ∧ i<n) (hm : EditSegmentMeaning t (i+1) seg) (hc : EditCountsMeaning s t n i zeroes ones)
    (hb : block=Znth i seg 0) (hbit : Znth i s 0=0) :
    EditCountsMeaning s t n (i+1) (replace_Znth block (Znth block zeroes 0+1) zeroes) ones :=
  (edit_counts_prefix_extend_zero__build_s2_segments_counts s t n i seg zeroes ones block hs hi ⟨hseg,hm⟩ ⟨hz,ho,hc⟩ hb hbit).2.2

theorem edit_counts_inc_one (s t : List Int) (n i : Int) (seg zeroes ones : List Int) (block : Int)
    (hs : Zlength s=n) (hz : Zlength zeroes=n) (ho : Zlength ones=n) (hseg : Zlength seg=i+1)
    (hi : 0≤i ∧ i<n) (hm : EditSegmentMeaning t (i+1) seg) (hc : EditCountsMeaning s t n i zeroes ones)
    (hb : block=Znth i seg 0) (hbit : Znth i s 0=1) :
    EditCountsMeaning s t n (i+1) zeroes (replace_Znth block (Znth block ones 0+1) ones) :=
  (edit_counts_prefix_extend_one__build_s2_segments_counts s t n i seg zeroes ones block hs hi ⟨hseg,hm⟩ ⟨hz,ho,hc⟩ hb hbit).2.2

theorem edit_segment_extend_same (t seg : List Int) (i : Int) (hl : Zlength seg=i) (hi : 1≤i)
    (hm : EditSegmentMeaning t i seg) (he : edit_edge_open t i) :
    EditSegmentMeaning t (i+1) (seg++[Znth (i-1) seg 0]) :=
  (edit_segment_prefix_append_same__build_s2_segments_counts t i seg ⟨hl,hm⟩ hi he).2

theorem edit_segment_extend_new (t seg : List Int) (i : Int) (hl : Zlength seg=i) (hi : 0≤i)
    (hm : EditSegmentMeaning t i seg) (he : ¬edit_edge_open t i) :
    EditSegmentMeaning t (i+1) (seg++[i]) :=
  (edit_segment_prefix_append_new__build_s2_segments_counts t i seg ⟨hl,hm⟩ hi he).2

theorem edit_segment_bound (t seg : List Int) (upto idx : Int)
    (hm : EditSegmentMeaning t upto seg) (hi : 0≤idx ∧ idx<upto) : 0≤Znth idx seg 0 ∧ Znth idx seg 0≤idx :=
  (hm idx hi).1

end EditStringsProofInternal
