import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib
open AUXLib AUXLib.Sorting
open SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
def heap_capacity : Int := 100000

def absent : Int := -1

def heap_item (key data : Int) : (Int × Int) := (key, data)

def item_key (item : (Int × Int)) : Int := item.1

def item_data (item : (Int × Int)) : Int := item.2

def pair_list (key_values data_values : List Int) : List (Int × Int) :=
  key_values.zip data_values

def partial_map : Type := Int → Option Int

def partial_map_get (M : partial_map) (data_x : Int) : Option Int :=
  M data_x

def partial_map_add
    (M : partial_map) (data_x key_x : Int) : partial_map :=
  fun query =>
    if query = data_x then some key_x else M query

def partial_map_update
    (M : partial_map) (data_x key_x : Int) : partial_map :=
  partial_map_add M data_x key_x

def partial_map_update_or_add
    (M : partial_map) (data_x key_x : Int) : partial_map :=
  partial_map_update M data_x key_x

def partial_map_remove
    (M : partial_map) (data_x : Int) : partial_map :=
  fun query =>
    if query = data_x then none else M query

def partial_map_absent (M : partial_map) (data_x : Int) : Prop :=
  partial_map_get M data_x = none

def partial_map_present
    (M : partial_map) (data_x key_x : Int) : Prop :=
  partial_map_get M data_x = some key_x

def partial_map_contains
    (M : partial_map) (data_x : Int) : Prop :=
  ∃ key_x, partial_map_present M data_x key_x

def partial_map_item (M : partial_map) (item : (Int × Int)) : Prop :=
  partial_map_present M (item_data item) (item_key item)

def partial_map_minimum (M : partial_map) (item : (Int × Int)) : Prop :=
  partial_map_item M item ∧
  ∀ data_x key_x,
    partial_map_present M data_x key_x →
    item_key item ≤ key_x

def heap_data_at
    (data_values : List Int) (index data_x : Int) : Prop :=
  (0 ≤ index ∧ index < Zlength data_values) ∧
  Znth index data_values 0 = data_x

def heap_contains_data
    (M : partial_map) (data_x : Int) : Prop :=
  partial_map_contains M data_x

def heap_data_absent
    (M : partial_map) (data_x : Int) : Prop :=
  partial_map_absent M data_x

def heap_data_present
    (M : partial_map) (data_x : Int) : Prop :=
  heap_contains_data M data_x

def heap_key_of
    (M : partial_map) (data_x key_x : Int) : Prop :=
  partial_map_present M data_x key_x

def heap_data_valid
    (data_values : List Int) (data_bound size : Int) : Prop :=
  ∀ index,
    (0 ≤ index ∧ index < size) →
    (0 ≤ Znth index data_values 0 ∧ Znth index data_values 0 < data_bound)

def heap_data_unique
    (data_values : List Int) (size : Int) : Prop :=
  ∀ i j,
    (0 ≤ i ∧ i < size) →
    (0 ≤ j ∧ j < size) →
    Znth i data_values 0 = Znth j data_values 0 →
    i = j

def heap_map_relation
    (M : partial_map)
    (key_values data_values : List Int) (size : Int) : Prop :=
  Zlength key_values = size ∧
  Zlength data_values = size ∧
  heap_data_unique data_values size ∧
  (∀ index,
    (0 ≤ index ∧ index < size) →
    partial_map_present
      M
      (Znth index data_values 0)
      (Znth index key_values 0)) ∧
  (∀ data_x key_x,
    partial_map_present M data_x key_x →
    ∃ index,
      (0 ≤ index ∧ index < size) ∧
      Znth index data_values 0 = data_x ∧
      Znth index key_values 0 = key_x)

def heap_parent (child : Int) : Int :=
  Z.quot (child - 1) 2

def heap_left_child (index : Int) : Int :=
  index * 2 + 1

def heap_right_child (index : Int) : Int :=
  index * 2 + 2

def heap_selected_child (key_values : List Int) (size index : Int) : Int :=
  let left := heap_left_child index
  let right := heap_right_child index
  if right < size then if Znth left key_values 0 ≤ Znth right key_values 0 then left else right else left

def heap_ordered (key_values : List Int) (size : Int) : Prop :=
  ∀ child,
    0 < child ∧ child < size →
    Znth (heap_parent child) key_values 0 ≤ Znth child key_values 0

def heap_pos_backlinks
    (data_values pos_values : List Int) (size : Int) : Prop :=
  ∀ index,
    (0 ≤ index ∧ index < size) →
    Znth (Znth index data_values 0) pos_values absent = index

def heap_pos_forward_links
    (data_values pos_values : List Int) (data_bound size : Int) : Prop :=
  ∀ data_x,
    (0 ≤ data_x ∧ data_x < data_bound) →
    Znth data_x pos_values absent = absent ∨
    ∃ index,
      (0 ≤ index ∧ index < size) ∧
      Znth index data_values 0 = data_x ∧
      Znth data_x pos_values absent = index

def heap_pos_consistent
    (data_values pos_values : List Int) (data_bound size : Int) : Prop :=
  0 ≤ data_bound ∧
  Zlength pos_values = data_bound ∧
  heap_data_valid data_values data_bound size ∧
  heap_pos_backlinks data_values pos_values size ∧
  heap_pos_forward_links data_values pos_values data_bound size

def heap_representation
    (M : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size : Int) : Prop :=
  0 ≤ size ∧
  size ≤ heap_capacity ∧
  heap_map_relation M key_values data_values size ∧
  heap_ordered key_values size ∧
  heap_pos_consistent data_values pos_values data_bound size

noncomputable def store_heap
    (key data pos : Int) (data_bound capacity : Int)
    (M : partial_map) (size : Int) : Assertion :=
  EX key_values : List Int,
  EX data_values : List Int,
  EX pos_values : List Int,
    “ heap_representation
        M key_values data_values pos_values data_bound size ” &&
    intArray.full key size key_values **
    intArray.undef_seg key size capacity **
    intArray.full data size data_values **
    intArray.undef_seg data size capacity **
    intArray.full pos data_bound pos_values

def heap_index_of
    (M : partial_map)
    (data_values pos_values : List Int) (data_x index : Int) : Prop :=
  heap_data_present M data_x ∧
  (0 ≤ index ∧ index < Zlength data_values) ∧
  Znth index data_values 0 = data_x ∧
  Znth data_x pos_values absent = index

def decrease_key_pre
    (M : partial_map) (data_x key_x : Int) : Prop :=
  ∃ old_key,
    heap_key_of M data_x old_key ∧
    key_x ≤ old_key

def partial_map_decrease_key_pre :=
  decrease_key_pre

def update_or_push_pre
    (M : partial_map) (data_x key_x : Int) : Prop :=
  heap_data_absent M data_x ∨
  decrease_key_pre M data_x key_x

def partial_map_update_or_add_pre :=
  update_or_push_pre

def partial_map_update_or_add_size
    (before : partial_map)
    (size_before size_after data_x key_x : Int) : Prop :=
  (partial_map_absent before data_x ∧
   size_after = size_before + 1) ∨
  (partial_map_decrease_key_pre before data_x key_x ∧
   size_after = size_before)

def HeapOrderExceptUp
    (key_values : List Int) (size child : Int) : Prop :=
  0 ≤ child ∧
  child < size ∧
  ∀ node,
    0 < node ∧ node < size ∧ node ≠ child →
    Znth (heap_parent node) key_values 0 ≤ Znth node key_values 0

def PushHoleChildrenPreserved
    (key_values : List Int) (size child : Int) : Prop :=
  ∀ node,
    0 < node ∧ node < size ∧ heap_parent node = child →
    Znth (heap_parent child) key_values 0 ≤ Znth node key_values 0

def HeapOrderExceptDown
    (key_values : List Int) (size index : Int) : Prop :=
  0 ≤ index ∧
  index < size ∧
  ∀ child,
    0 < child ∧ child < size ∧ heap_parent child ≠ index →
    Znth (heap_parent child) key_values 0 ≤ Znth child key_values 0

def PopHoleParentDominatesChildren
    (key_values : List Int) (size index : Int) : Prop :=
  index = 0 ∨
  ∀ child,
    0 < child ∧ child < size ∧ heap_parent child = index →
    Znth (heap_parent index) key_values 0 ≤ Znth child key_values 0

def SelectedChild
    (key_values : List Int) (size index selected : Int) : Prop :=
  0 ≤ index ∧
  index < size ∧
  index < selected ∧
  0 ≤ selected ∧
  selected < size ∧
  heap_parent selected = index ∧
  selected = heap_selected_child key_values size index ∧
  ∀ child,
    0 < child ∧ child < size ∧ heap_parent child = index →
    Znth selected key_values 0 ≤ Znth child key_values 0

def HeapArrayState
    (M : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size : Int) : Prop :=
  0 ≤ size ∧
  size ≤ heap_capacity ∧
  heap_map_relation M key_values data_values size ∧
  heap_pos_consistent data_values pos_values data_bound size

def SiftUpState
    (M : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size child : Int) : Prop :=
  HeapArrayState M key_values data_values pos_values data_bound size ∧
  (0 ≤ child ∧ child < size) ∧
  HeapOrderExceptUp key_values size child ∧
  PushHoleChildrenPreserved key_values size child

def SiftDownState
    (M : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size index : Int) : Prop :=
  HeapArrayState M key_values data_values pos_values data_bound size ∧
  (0 ≤ index ∧ index < size) ∧
  HeapOrderExceptDown key_values size index ∧
  PopHoleParentDominatesChildren key_values size index

noncomputable def store_sift_up
    (key data pos : Int) (data_bound capacity : Int)
    (M : partial_map) (size index : Int) : Assertion :=
  EX key_values : List Int,
  EX data_values : List Int,
  EX pos_values : List Int,
    “ SiftUpState
        M key_values data_values pos_values data_bound size index ” &&
    intArray.full key size key_values **
    intArray.undef_seg key size capacity **
    intArray.full data size data_values **
    intArray.undef_seg data size capacity **
    intArray.full pos data_bound pos_values

noncomputable def store_sift_down
    (key data pos : Int) (data_bound capacity : Int)
    (M : partial_map) (size index : Int) : Assertion :=
  EX key_values : List Int,
  EX data_values : List Int,
  EX pos_values : List Int,
    “ SiftDownState
        M key_values data_values pos_values data_bound size index ” &&
    intArray.full key size key_values **
    intArray.undef_seg key size capacity **
    intArray.full data size data_values **
    intArray.undef_seg data size capacity **
    intArray.full pos data_bound pos_values

def PushWriteState
    (before : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size data_x key_x : Int) : Prop :=
  partial_map_absent before data_x ∧
  SiftUpState (partial_map_add before data_x key_x)
    key_values data_values pos_values
    data_bound (size + 1) size ∧
  Znth size key_values 0 = key_x ∧
  Znth size data_values 0 = data_x ∧
  Znth data_x pos_values absent = size

def DecreaseKeyWriteState
    (before : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size data_x key_x index : Int) : Prop :=
  (0 ≤ index ∧ index < size) ∧
  Znth index data_values 0 = data_x ∧
  partial_map_decrease_key_pre before data_x key_x ∧
  SiftUpState (partial_map_update before data_x key_x)
    key_values data_values pos_values
    data_bound size index ∧
  Znth index key_values 0 = key_x

def PopRootState
    (before : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size : Int) (popped : (Int × Int)) : Prop :=
  1 ≤ size ∧
  partial_map_minimum before popped ∧
  heap_representation
    (partial_map_remove before (item_data popped))
    key_values data_values pos_values data_bound (size - 1)

def heap_pos_backlinks_except
    (data_values pos_values : List Int) (size skipped_index : Int) : Prop :=
  ∀ index,
    (0 ≤ index ∧ index < size) →
    index ≠ skipped_index →
    Znth (Znth index data_values 0) pos_values absent = index

def PopMarkedState
    (before : partial_map)
    (key_values data_values pos_values : List Int)
    (data_bound size : Int) (popped : (Int × Int)) : Prop :=
  1 ≤ size ∧
  partial_map_minimum before popped ∧
  0 ≤ size ∧
  size ≤ heap_capacity ∧
  heap_map_relation before key_values data_values size ∧
  heap_ordered key_values size ∧
  0 ≤ data_bound ∧
  Zlength pos_values = data_bound ∧
  heap_data_valid data_values data_bound size ∧
  heap_pos_backlinks_except data_values pos_values size 0 ∧
  heap_pos_forward_links data_values pos_values data_bound size ∧
  Znth 0 key_values 0 = item_key popped ∧
  Znth 0 data_values 0 = item_data popped ∧
  Znth (item_data popped) pos_values absent = absent ∧
  (0 ≤ item_data popped ∧ item_data popped < data_bound)

def pop_replaced_values (size : Int) (values : List Int) : List Int :=
  sublist 0 (size - 1)
    (replace_Znth 0 (Znth (size - 1) values 0) values)

def pop_replacement_source (size index : Int) : Int :=
  if index = 0 then size - 1 else index

def heap_swap_values (i j : Int) (values : List Int) : List Int :=
  replace_Znth j (Znth i values 0)
    (replace_Znth i (Znth j values 0) values)

def heap_swap_pos
    (data_values pos_values : List Int) (i j : Int) : List Int :=
  replace_Znth (Znth j data_values 0) i
    (replace_Znth (Znth i data_values 0) j pos_values)

def swap_source (i j k : Int) : Int :=
  if k = i then j else if k = j then i else k

private theorem prefix_len {A : Type} (l : List A) (n : Int) (hn : 0 ≤ n ∧ n ≤ Zlength l) :
    Zlength (sublist 0 n l) = n := by
  unfold Zlength
  rw [sublist_length 0 n l (by omega) hn.2]
  simp only [Int.sub_zero,Int.ofNat_eq_coe]
  omega


private theorem Znth_prefix {A : Type} (l : List A) (d : A) (n i : Int) (hi : 0 ≤ i ∧ i < n) :
    Znth i (sublist 0 n l) d = Znth i l d := by
  simpa only [Int.add_zero] using Znth_sublist d 0 i n l (by omega) (by omega)


private theorem app_Znth1 (d : Int) (l1 l2 : List Int) (i : Int)
    (h : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1 ++ l2) d = Znth i l1 d := by
  have hn : i.toNat < l1.length := by simp only [Zlength, Int.ofNat_eq_coe] at h; omega
  simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_append_left hn]



theorem heap_parent_positive_bounds (child size : Int) (hc : 0 < child) (hs : child < size) :
    0 ≤ heap_parent child ∧ heap_parent child < child ∧ heap_parent child < size := by
  unfold heap_parent Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

theorem heap_parent_left_child (index : Int) (hi : 0 ≤ index) : heap_parent (heap_left_child index) = index := by
  unfold heap_parent heap_left_child Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

theorem heap_parent_right_child (index : Int) (hi : 0 ≤ index) : heap_parent (heap_right_child index) = index := by
  unfold heap_parent heap_right_child Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

theorem heap_children_characterization (index child : Int) (hi : 0 ≤ index) (hc : 0 < child) (hp : heap_parent child = index) :
    child = heap_left_child index ∨ child = heap_right_child index := by
  unfold heap_parent Z.quot at hp
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hp
  unfold heap_left_child heap_right_child
  omega

theorem heap_ordered_root_lower_bound (key_values : List Int) (size index : Int)
    (ho : heap_ordered key_values size) (hi : 0 ≤ index ∧ index < size) :
    Znth 0 key_values 0 ≤ Znth index key_values 0 :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.heap_ordered_root_lower_bound__pop_initialization key_values size index ho hi

theorem heap_root_is_partial_map_minimum (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size : Int) (hs : 1 ≤ size) (hr : heap_representation M key_values data_values pos_values data_bound size) :
    partial_map_minimum M (heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)) := by
  rcases hr with ⟨_,_,hm,ho,_⟩
  refine ⟨hm.2.2.2.1 0 (by omega),?_⟩
  intro d k h
  obtain ⟨i,hi,_,he⟩ := hm.2.2.2.2 d k h
  change Znth 0 key_values 0 ≤ k
  rw [← he]
  exact heap_ordered_root_lower_bound key_values size i ho hi

theorem singleton_full_to_empty_undef (p capacity : Int) (values : List Int)
    (hc : 1 ≤ capacity) (hl : Zlength values = 1) :
    intArray.full p 1 values ** intArray.undef_seg p 1 capacity |--
    intArray.full p 0 [] ** intArray.undef_seg p 0 capacity := by
  sep_apply (SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.singleton_full_split_spare__pop_singleton p values hl)
  sep_apply (intArray.undef_seg_merge_to_undef_seg p 0 1 capacity (by omega))
  cancel

theorem full_retire_last_to_undef (p size capacity : Int) (values : List Int)
    (hs : 0 < size) (hc : size ≤ capacity) (hl : Zlength values = size) :
    intArray.full p size values ** intArray.undef_seg p size capacity |--
    intArray.full p (size-1) (sublist 0 (size-1) values) ** intArray.undef_seg p (size-1) capacity := by
  sep_apply (intArray.full_split_to_seg p (size-1) size values (by omega))
  sep_apply (intArray.seg_to_full p 0 (size-1) (sublist 0 (size-1) values))
  sep_apply (intArray.seg_to_undef_seg p (size-1) size (sublist (size-1) size values))
  sep_apply (intArray.undef_seg_merge_to_undef_seg p (size-1) size capacity (by omega))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem Zlength_pop_replaced_values (size : Int) (values : List Int) (hs : 1 < size) (hl : Zlength values = size) :
    Zlength (pop_replaced_values size values) = size-1 := by
  unfold pop_replaced_values
  apply prefix_len
  rw [Zlength_replace_Znth,hl]; omega

theorem Znth_pop_replaced_values (size : Int) (values : List Int) (index : Int)
    (hs : 1 < size) (hl : Zlength values = size) (hi : 0 ≤ index ∧ index < size-1) :
    Znth index (pop_replaced_values size values) 0 = Znth (pop_replacement_source size index) values 0 := by
  unfold pop_replaced_values pop_replacement_source
  rw [Znth_prefix _ 0 (size-1) index hi]
  by_cases h0 : index = 0
  · subst index; rw [if_pos rfl,Znth_replace_Znth_Same 0 values 0 _ (by omega)]
  · rw [if_neg h0,Znth_replace_Znth_Diff 0 values 0 index _ (by omega) (by omega) (Ne.symm h0)]

theorem pop_replacement_source_range (size index : Int) (hs : 1 < size) (hi : 0 ≤ index ∧ index < size-1) :
    0 < pop_replacement_source size index ∧ pop_replacement_source size index < size := by
  unfold pop_replacement_source; split <;> omega

theorem pop_replacement_source_injective (size i j : Int) (hs : 1 < size)
    (hi : 0 ≤ i ∧ i < size-1) (hj : 0 ≤ j ∧ j < size-1)
    (he : pop_replacement_source size i = pop_replacement_source size j) : i = j := by
  unfold pop_replacement_source at he
  split at he <;> split at he <;> omega

theorem Znth_swap_Znth {A : Type} (l : List A) (i j : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hne : i ≠ j) :
    let swapped := replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)
    Znth i swapped d = Znth j l d ∧ Znth j swapped d = Znth i l d ∧
      ∀ k, (0 ≤ k ∧ k < Zlength l) → k ≠ i → k ≠ j → Znth k swapped d = Znth k l d :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.Znth_swap_Znth l i j d hi hj hne

theorem swap_source_range (i j k size : Int) (hi : 0 ≤ i ∧ i < size) (hj : 0 ≤ j ∧ j < size)
    (hk : 0 ≤ k ∧ k < size) : 0 ≤ swap_source i j k ∧ swap_source i j k < size := by
  unfold swap_source
  split
  · exact hj
  · split
    · exact hi
    · exact hk

theorem swap_source_involutive (i j k : Int) (hne : i ≠ j) : swap_source i j (swap_source i j k) = k := by
  by_cases hki : k = i
  · subst k; simp [swap_source,hne,Ne.symm hne]
  · by_cases hkj : k = j
    · subst k; simp [swap_source,hne,Ne.symm hne]
    · simp [swap_source,hki,hkj]

theorem swap_source_injective (i j k1 k2 : Int) (hne : i ≠ j)
    (he : swap_source i j k1 = swap_source i j k2) : k1 = k2 := by
  have h := congrArg (swap_source i j) he
  simpa only [swap_source_involutive i j _ hne] using h

theorem Zlength_heap_swap_values (i j : Int) (values : List Int) :
    Zlength (heap_swap_values i j values) = Zlength values := by
  unfold heap_swap_values; rw [Zlength_replace_Znth,Zlength_replace_Znth]

theorem Znth_heap_swap_values (values : List Int) (i j k : Int) (hi : 0 ≤ i ∧ i < Zlength values)
    (hj : 0 ≤ j ∧ j < Zlength values) (hne : i ≠ j) (hk : 0 ≤ k ∧ k < Zlength values) :
    Znth k (heap_swap_values i j values) 0 = Znth (swap_source i j k) values 0 := by
  have hs := Znth_swap_Znth values i j 0 hi hj hne
  unfold swap_source
  by_cases hki : k = i
  · subst k; rw [if_pos rfl]; exact hs.1
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst k; rw [if_pos rfl]; exact hs.2.1
    · rw [if_neg hkj]; exact hs.2.2 k hk hki hkj

theorem selected_child_left (key_values : List Int) (size index : Int) (hi : 0 ≤ index) (hb : index < size)
    (hl : heap_left_child index < size)
    (hs : heap_right_child index ≥ size ∨ Znth (heap_left_child index) key_values 0 ≤ Znth (heap_right_child index) key_values 0) :
    SelectedChild key_values size index (heap_left_child index) :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.pop_select_left__pop_child_selection key_values size index hi hl hs

theorem selected_child_right (key_values : List Int) (size index : Int) (hi : 0 ≤ index) (hb : index < size)
    (hr : heap_right_child index < size)
    (hs : Znth (heap_right_child index) key_values 0 < Znth (heap_left_child index) key_values 0) :
    SelectedChild key_values size index (heap_right_child index) :=
  SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.pop_select_right__pop_child_selection key_values size index hi hr hs

theorem selected_child_current_lt (key_values : List Int) (size index selected : Int)
    (hs : SelectedChild key_values size index selected) : index < selected := hs.2.2.1

theorem heap_parent_zero : heap_parent 0 = 0 := rfl
theorem heap_data_unique_swap_values (data_values : List Int) (size i j : Int)
    (hu : heap_data_unique data_values size) (hi : 0 ≤ i ∧ i < size) (hj : 0 ≤ j ∧ j < size)
    (hne : i ≠ j) (hl : Zlength data_values = size) : heap_data_unique (heap_swap_values i j data_values) size := by
  intro k1 k2 hk1 hk2 he
  rw [Znth_heap_swap_values data_values i j k1 (by omega) (by omega) hne (by omega),
    Znth_heap_swap_values data_values i j k2 (by omega) (by omega) hne (by omega)] at he
  exact swap_source_injective i j k1 k2 hne
    (hu _ _ (swap_source_range i j k1 size hi hj hk1) (swap_source_range i j k2 size hi hj hk2) he)

theorem heap_map_relation_swap_values (M : partial_map) (key_values data_values : List Int) (size i j : Int)
    (hm : heap_map_relation M key_values data_values size) (hi : 0 ≤ i ∧ i < size) (hj : 0 ≤ j ∧ j < size)
    (hne : i ≠ j) : heap_map_relation M (heap_swap_values i j key_values) (heap_swap_values i j data_values) size := by
  rcases hm with ⟨hk,hd,hu,hforward,hback⟩
  refine ⟨(Zlength_heap_swap_values _ _ _).trans hk,(Zlength_heap_swap_values _ _ _).trans hd,
    heap_data_unique_swap_values data_values size i j hu hi hj hne hd,?_,?_⟩
  · intro k hkr
    rw [Znth_heap_swap_values data_values i j k (by omega) (by omega) hne (by omega),
      Znth_heap_swap_values key_values i j k (by omega) (by omega) hne (by omega)]
    exact hforward _ (swap_source_range i j k size hi hj hkr)
  · intro dx kx h
    obtain ⟨k,hkr,hdx,hkx⟩ := hback dx kx h
    have hs := swap_source_range i j k size hi hj hkr
    refine ⟨swap_source i j k,hs,?_,?_⟩
    · rw [Znth_heap_swap_values data_values i j _ (by omega) (by omega) hne (by omega),swap_source_involutive i j k hne]; exact hdx
    · rw [Znth_heap_swap_values key_values i j _ (by omega) (by omega) hne (by omega),swap_source_involutive i j k hne]; exact hkx

theorem heap_pos_consistent_swap_values (data_values pos_values : List Int) (data_bound size i j : Int)
    (hu : heap_data_unique data_values size) (hp : heap_pos_consistent data_values pos_values data_bound size)
    (hi : 0 ≤ i ∧ i < size) (hj : 0 ≤ j ∧ j < size) (hne : i ≠ j) (hl : Zlength data_values = size) :
    heap_pos_consistent (heap_swap_values i j data_values) (heap_swap_pos data_values pos_values i j) data_bound size := by
  rcases hp with ⟨hb,hp,valid,back,forward⟩
  have hdi := valid i hi
  have hdj := valid j hj
  have hdne : Znth i data_values 0 ≠ Znth j data_values 0 := fun he => hne (hu i j hi hj he)
  have hs := Znth_swap_Znth data_values i j 0 (by omega) (by omega) hne
  have hpi : Znth (Znth i data_values 0) (heap_swap_pos data_values pos_values i j) absent = j := by
    unfold heap_swap_pos
    rw [Znth_replace_Znth_Diff absent _ (Znth j data_values 0) (Znth i data_values 0) _
        (by rw [Zlength_replace_Znth]; omega) (by rw [Zlength_replace_Znth]; omega) (Ne.symm hdne),
      Znth_replace_Znth_Same absent pos_values _ _ (by omega)]
  have hpj : Znth (Znth j data_values 0) (heap_swap_pos data_values pos_values i j) absent = i := by
    unfold heap_swap_pos
    exact Znth_replace_Znth_Same absent _ _ _ (by rw [Zlength_replace_Znth]; omega)
  have hps (dx : Int) (hdx : 0 ≤ dx ∧ dx < data_bound)
      (hni : dx ≠ Znth i data_values 0) (hnj : dx ≠ Znth j data_values 0) :
      Znth dx (heap_swap_pos data_values pos_values i j) absent = Znth dx pos_values absent := by
    unfold heap_swap_pos
    rw [Znth_replace_Znth_Diff absent _ (Znth j data_values 0) dx _
        (by rw [Zlength_replace_Znth]; omega) (by rw [Zlength_replace_Znth]; omega) (Ne.symm hnj),
      Znth_replace_Znth_Diff absent pos_values (Znth i data_values 0) dx _ (by omega) (by omega) (Ne.symm hni)]
  refine ⟨hb,?_,?_,?_,?_⟩
  · unfold heap_swap_pos; rw [Zlength_replace_Znth,Zlength_replace_Znth,hp]
  · intro k hk
    rw [Znth_heap_swap_values data_values i j k (by omega) (by omega) hne (by omega)]
    exact valid _ (swap_source_range i j k size hi hj hk)
  · intro k hk
    by_cases hki : k = i
    · subst k; rw [show Znth i (heap_swap_values i j data_values) 0 = Znth j data_values 0 from hs.1]; exact hpj
    · by_cases hkj : k = j
      · subst k; rw [show Znth j (heap_swap_values i j data_values) 0 = Znth i data_values 0 from hs.2.1]; exact hpi
      · rw [show Znth k (heap_swap_values i j data_values) 0 = Znth k data_values 0 from hs.2.2 k (by omega) hki hkj,
          hps _ (valid k hk) (fun he => hki (hu k i hk hi he)) (fun he => hkj (hu k j hk hj he))]
        exact back k hk
  · intro dx hdx
    by_cases hei : dx = Znth i data_values 0
    · subst dx; exact Or.inr ⟨j,hj,hs.2.1,hpi⟩
    · by_cases hej : dx = Znth j data_values 0
      · subst dx; exact Or.inr ⟨i,hi,hs.1,hpj⟩
      · rw [hps dx hdx hei hej]
        rcases forward dx hdx with ha | ⟨k,hk,hdxk,hpk⟩
        · exact Or.inl ha
        · have hki : k ≠ i := by intro he; rw [he] at hdxk; exact hei hdxk.symm
          have hkj : k ≠ j := by intro he; rw [he] at hdxk; exact hej hdxk.symm
          exact Or.inr ⟨k,hk,(hs.2.2 k (by omega) hki hkj).trans hdxk,hpk⟩

theorem heap_array_state_swap_values (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size i j : Int) (h : HeapArrayState M key_values data_values pos_values data_bound size)
    (hi : 0 ≤ i ∧ i < size) (hj : 0 ≤ j ∧ j < size) (hne : i ≠ j) :
    HeapArrayState M (heap_swap_values i j key_values) (heap_swap_values i j data_values)
      (heap_swap_pos data_values pos_values i j) data_bound size := by
  rcases h with ⟨hn,hc,hm,hp⟩
  exact ⟨hn,hc,heap_map_relation_swap_values M key_values data_values size i j hm hi hj hne,
    heap_pos_consistent_swap_values data_values pos_values data_bound size i j hm.2.2.1 hp hi hj hne hm.2.1⟩

theorem sift_up_state_heap_representation_at_root (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size child : Int) (hc : child ≤ 0) (hs : SiftUpState M key_values data_values pos_values data_bound size child) :
    heap_representation M key_values data_values pos_values data_bound size := by
  rcases hs with ⟨⟨hn,hcap,hm,hp⟩,hr,he,_⟩
  refine ⟨hn,hcap,hm,?_,hp⟩
  intro node hh
  exact he.2.2 node ⟨hh.1,hh.2,by omega⟩

theorem sift_up_state_heap_representation_at_break (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size child parent : Int) (hc : 0 < child) (hp : parent = heap_parent child)
    (hv : Znth parent key_values 0 ≤ Znth child key_values 0)
    (hs : SiftUpState M key_values data_values pos_values data_bound size child) :
    heap_representation M key_values data_values pos_values data_bound size := by
  rcases hs with ⟨⟨hn,hcap,hm,hpos⟩,hr,he,_⟩
  refine ⟨hn,hcap,hm,?_,hpos⟩
  intro node hh
  by_cases heq : node = child
  · subst node; simpa only [hp] using hv
  · exact he.2.2 node ⟨hh.1,hh.2,heq⟩

theorem sift_down_state_heap_representation_at_leaf (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size index : Int) (hl : heap_left_child index ≥ size)
    (hs : SiftDownState M key_values data_values pos_values data_bound size index) :
    heap_representation M key_values data_values pos_values data_bound size := by
  rcases hs with ⟨⟨hn,hcap,hm,hpos⟩,hr,he,_⟩
  refine ⟨hn,hcap,hm,?_,hpos⟩
  intro child hc
  apply he.2.2 child
  refine ⟨hc.1,hc.2,?_⟩
  intro hp
  have hh := heap_children_characterization index child hr.1 hc.1 hp
  unfold heap_left_child heap_right_child at *
  omega

theorem sift_down_state_heap_representation_at_break (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size index selected : Int) (hv : Znth index key_values 0 ≤ Znth selected key_values 0)
    (hsel : SelectedChild key_values size index selected)
    (hs : SiftDownState M key_values data_values pos_values data_bound size index) :
    heap_representation M key_values data_values pos_values data_bound size := by
  rcases hs with ⟨⟨hn,hcap,hm,hpos⟩,hr,he,_⟩
  refine ⟨hn,hcap,hm,?_,hpos⟩
  intro child hc
  by_cases hp : heap_parent child = index
  · rw [hp]; exact Int.le_trans hv (hsel.2.2.2.2.2.2.2 child ⟨hc.1,hc.2,hp⟩)
  · exact he.2.2 child ⟨hc.1,hc.2,hp⟩
theorem heap_key_at_index_from_relation (M : partial_map) (key_values data_values : List Int)
    (size index data_x key_x : Int) (hm : heap_map_relation M key_values data_values size)
    (hi : 0 ≤ index ∧ index < size) (hd : Znth index data_values 0 = data_x)
    (hp : partial_map_present M data_x key_x) : Znth index key_values 0 = key_x := by
  have hh := hm.2.2.2.1 index hi
  rw [hd] at hh
  exact Option.some.inj (hh.symm.trans hp)

theorem decrease_key_new_le_old_index (M : partial_map) (key_values data_values : List Int)
    (size index data_x key_x : Int) (hm : heap_map_relation M key_values data_values size)
    (hi : 0 ≤ index ∧ index < size) (hd : Znth index data_values 0 = data_x)
    (hp : partial_map_decrease_key_pre M data_x key_x) : key_x ≤ Znth index key_values 0 := by
  obtain ⟨old,ho,hk⟩ := hp
  rw [heap_key_at_index_from_relation M key_values data_values size index data_x old hm hi hd ho]
  exact hk

theorem heap_index_of_from_heap_representation (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size data_x key_x : Int) (hr : heap_representation M key_values data_values pos_values data_bound size)
    (hd : 0 ≤ data_x ∧ data_x < data_bound) (hp : partial_map_decrease_key_pre M data_x key_x) :
    heap_index_of M data_values pos_values data_x (Znth data_x pos_values 0) ∧
      (0 ≤ Znth data_x pos_values 0 ∧ Znth data_x pos_values 0 < size) := by
  rcases hr with ⟨hn,hc,hm,ho,hpos⟩
  obtain ⟨old,hold,hnew⟩ := hp
  obtain ⟨index,hi,hdi,hki⟩ := hm.2.2.2.2 data_x old hold
  have hback := hpos.2.2.2.1 index hi
  rw [hdi] at hback
  have he : Znth data_x pos_values 0 = index := (Znth_indep pos_values data_x 0 absent (by rw [hpos.2.1]; exact hd)).trans hback
  rw [he]
  exact ⟨⟨⟨old,hold⟩,by rw [hm.2.1]; exact hi,hdi,hback⟩,hi⟩

theorem heap_map_relation_update_key (M : partial_map) (key_values data_values : List Int)
    (size index data_x key_x : Int) (hm : heap_map_relation M key_values data_values size)
    (hi : 0 ≤ index ∧ index < size) (hdx : Znth index data_values 0 = data_x) :
    heap_map_relation (partial_map_update M data_x key_x) (replace_Znth index key_x key_values) data_values size := by
  rcases hm with ⟨hk,hd,hu,forward,back⟩
  refine ⟨(Zlength_replace_Znth _ _ _).trans hk,hd,hu,?_,?_⟩
  · intro j hj
    by_cases hji : j = index
    · subst j
      rw [hdx,Znth_replace_Znth_Same 0 key_values index key_x (by omega)]
      simp [partial_map_present,partial_map_get,partial_map_update,partial_map_add]
    · have hdata : Znth j data_values 0 ≠ data_x := by
        intro he
        exact hji (hu j index hj hi (he.trans hdx.symm))
      rw [Znth_replace_Znth_Diff 0 key_values index j key_x (by omega) (by omega) (Ne.symm hji)]
      simpa only [partial_map_present,partial_map_get,partial_map_update,partial_map_add,if_neg hdata] using forward j hj
  · intro dx kx h
    by_cases he : dx = data_x
    · subst dx
      have hkx : key_x = kx := by simpa [partial_map_present,partial_map_get,partial_map_update,partial_map_add] using h
      exact ⟨index,hi,hdx,(Znth_replace_Znth_Same 0 key_values index key_x (by omega)).trans hkx⟩
    · have hold : partial_map_present M dx kx := by
        simpa only [partial_map_present,partial_map_get,partial_map_update,partial_map_add,if_neg he] using h
      obtain ⟨j,hj,hdj,hkj⟩ := back dx kx hold
      have hji : j ≠ index := by intro hh; subst j; exact he (hdj.symm.trans hdx)
      exact ⟨j,hj,hdj,(Znth_replace_Znth_Diff 0 key_values index j key_x (by omega) (by omega) (Ne.symm hji)).trans hkj⟩

theorem heap_order_except_up_after_decrease (M : partial_map) (key_values data_values : List Int)
    (size index data_x key_x : Int) (hm : heap_map_relation M key_values data_values size)
    (ho : heap_ordered key_values size) (hd : partial_map_decrease_key_pre M data_x key_x)
    (hi : 0 ≤ index ∧ index < size) (hx : Znth index data_values 0 = data_x) :
    HeapOrderExceptUp (replace_Znth index key_x key_values) size index := by
  have hk := hm.1
  have hnew := decrease_key_new_le_old_index M key_values data_values size index data_x key_x hm hi hx hd
  refine ⟨hi.1,hi.2,?_⟩
  intro node hn
  have hp := heap_parent_positive_bounds node size hn.1 hn.2.1
  rw [Znth_replace_Znth_Diff 0 key_values index node key_x (by omega) (by omega) (Ne.symm hn.2.2)]
  have hold := ho node ⟨hn.1,hn.2.1⟩
  by_cases hpi : heap_parent node = index
  · rw [hpi,Znth_replace_Znth_Same 0 key_values index key_x (by omega)]
    rw [hpi] at hold; omega
  · rw [Znth_replace_Znth_Diff 0 key_values index (heap_parent node) key_x (by omega) (by omega) (Ne.symm hpi)]
    exact hold

theorem push_hole_children_preserved_after_decrease (M : partial_map) (key_values data_values : List Int)
    (size index data_x key_x : Int) (hm : heap_map_relation M key_values data_values size)
    (ho : heap_ordered key_values size) (hd : partial_map_decrease_key_pre M data_x key_x)
    (hi : 0 ≤ index ∧ index < size) (hx : Znth index data_values 0 = data_x) :
    PushHoleChildrenPreserved (replace_Znth index key_x key_values) size index := by
  have hk := hm.1
  have hnew := decrease_key_new_le_old_index M key_values data_values size index data_x key_x hm hi hx hd
  intro node hn
  have hp := heap_parent_positive_bounds node size hn.1 hn.2.1
  rw [Znth_replace_Znth_Diff 0 key_values index node key_x (by omega) (by omega) (by omega)]
  have hedge := ho node ⟨hn.1,hn.2.1⟩
  rw [hn.2.2] at hedge
  by_cases h0 : index = 0
  · rw [h0,heap_parent_zero,Znth_replace_Znth_Same 0 key_values 0 key_x (by omega)]
    rw [h0] at hnew hedge; omega
  · have hgp := heap_parent_positive_bounds index size (by omega) hi.2
    rw [Znth_replace_Znth_Diff 0 key_values index (heap_parent index) key_x (by omega) (by omega) (by omega)]
    exact Int.le_trans (ho index ⟨by omega,hi.2⟩) hedge

theorem decrease_key_write_state_from_heap_representation (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size data_x key_x index : Int) (hr : heap_representation M key_values data_values pos_values data_bound size)
    (hd : partial_map_decrease_key_pre M data_x key_x) (hx : heap_index_of M data_values pos_values data_x index)
    (hi : 0 ≤ index ∧ index < size) :
    DecreaseKeyWriteState M (replace_Znth index key_x key_values) data_values pos_values data_bound size data_x key_x index := by
  rcases hr with ⟨hn,hc,hm,ho,hp⟩
  have hdata := hx.2.2.1
  exact ⟨hi,hdata,hd,⟨⟨hn,hc,heap_map_relation_update_key M key_values data_values size index data_x key_x hm hi hdata,hp⟩,
      hi,heap_order_except_up_after_decrease M key_values data_values size index data_x key_x hm ho hd hi hdata,
      push_hole_children_preserved_after_decrease M key_values data_values size index data_x key_x hm ho hd hi hdata⟩,
    Znth_replace_Znth_Same 0 key_values index key_x (by rw [hm.1]; exact hi)⟩

theorem partial_map_absent_from_negative_pos (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size data_x : Int) (hr : heap_representation M key_values data_values pos_values data_bound size)
    (hd : 0 ≤ data_x ∧ data_x < data_bound) (hneg : Znth data_x pos_values 0 < 0) : partial_map_absent M data_x := by
  rcases hr with ⟨hn,hc,hm,ho,hp⟩
  change M data_x = none
  cases he : M data_x with
  | none => rfl
  | some k =>
    obtain ⟨i,hi,hdi,hki⟩ := hm.2.2.2.2 data_x k he
    have hb := hp.2.2.2.1 i hi
    rw [hdi,← Znth_indep pos_values data_x 0 absent (by rw [hp.2.1]; exact hd)] at hb
    omega

theorem partial_map_decrease_key_pre_from_nonnegative_pos (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size data_x key_x : Int) (hr : heap_representation M key_values data_values pos_values data_bound size)
    (hd : 0 ≤ data_x ∧ data_x < data_bound) (hn : 0 ≤ Znth data_x pos_values 0)
    (hu : partial_map_update_or_add_pre M data_x key_x) : partial_map_decrease_key_pre M data_x key_x := by
  rcases hu with ha | hdec
  · rcases hr with ⟨_,_,hm,_,hp⟩
    have hz : Znth data_x pos_values absent = Znth data_x pos_values 0 := Znth_indep _ _ _ _ (by rw [hp.2.1]; exact hd)
    rcases hp.2.2.2.2 data_x hd with hnone | ⟨i,hi,hdi,hpi⟩
    · rw [hz] at hnone; unfold absent at hnone; omega
    · have hpres := hm.2.2.2.1 i hi
      rw [hdi] at hpres
      have hfalse := ha.symm.trans hpres
      exact False.elim (Option.noConfusion hfalse)
  · exact hdec
theorem heap_map_relation_absent_not_in_data (M : partial_map) (key_values data_values : List Int) (size data_x : Int)
    (hm : heap_map_relation M key_values data_values size) (ha : partial_map_absent M data_x) :
    ∀ index, (0 ≤ index ∧ index < size) → Znth index data_values 0 ≠ data_x := by
  intro index hi he
  have hp := hm.2.2.2.1 index hi
  rw [he] at hp
  exact Option.noConfusion (ha.symm.trans hp)

private theorem snoc_lookup (l : List Int) (size x : Int) (hl : Zlength l = size) : Znth size (l ++ [x]) 0 = x := by
  rw [app_Znth2 0 l [x] size (by omega),hl]
  simp [Znth]

theorem heap_data_unique_snoc (data_values : List Int) (size data_x : Int) (hl : Zlength data_values = size)
    (hu : heap_data_unique data_values size)
    (hn : ∀ index, (0 ≤ index ∧ index < size) → Znth index data_values 0 ≠ data_x) :
    heap_data_unique (data_values ++ [data_x]) (size+1) := by
  intro i j hi hj he
  by_cases his : i = size
  · rw [his,snoc_lookup data_values size data_x hl] at he
    by_cases hjs : j = size
    · omega
    · rw [app_Znth1 0 data_values [data_x] j (by omega)] at he
      exact False.elim (hn j (by omega) he.symm)
  · rw [app_Znth1 0 data_values [data_x] i (by omega)] at he
    by_cases hjs : j = size
    · rw [hjs,snoc_lookup data_values size data_x hl] at he
      exact False.elim (hn i (by omega) he)
    · rw [app_Znth1 0 data_values [data_x] j (by omega)] at he
      exact hu i j (by omega) (by omega) he

theorem heap_map_relation_add_snoc (M : partial_map) (key_values data_values : List Int) (size data_x key_x : Int)
    (hm : heap_map_relation M key_values data_values size) (ha : partial_map_absent M data_x) :
    heap_map_relation (partial_map_add M data_x key_x) (key_values ++ [key_x]) (data_values ++ [data_x]) (size+1) := by
  have hn := heap_map_relation_absent_not_in_data M key_values data_values size data_x hm ha
  rcases hm with ⟨hk,hd,hu,forward,back⟩
  have hsize : 0 ≤ size := by rw [← hk]; exact Zlength_nonneg _
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega,
    by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega,heap_data_unique_snoc _ _ _ hd hu hn,?_,?_⟩
  · intro i hi
    by_cases his : i = size
    · rw [his,snoc_lookup key_values size key_x hk,snoc_lookup data_values size data_x hd]
      simp [partial_map_present,partial_map_get,partial_map_add]
    · rw [app_Znth1 0 key_values [key_x] i (by omega),app_Znth1 0 data_values [data_x] i (by omega)]
      simpa only [partial_map_present,partial_map_get,partial_map_add,if_neg (hn i (by omega))] using forward i (by omega)
  · intro dx kx h
    by_cases he : dx = data_x
    · have hkey : key_x = kx := by simpa [partial_map_present,partial_map_get,partial_map_add,he] using h
      exact ⟨size,by omega,(snoc_lookup data_values size data_x hd).trans he.symm,(snoc_lookup key_values size key_x hk).trans hkey⟩
    · have hold : partial_map_present M dx kx := by simpa only [partial_map_present,partial_map_get,partial_map_add,if_neg he] using h
      obtain ⟨i,hi,hdi,hki⟩ := back dx kx hold
      exact ⟨i,by omega,(app_Znth1 0 data_values [data_x] i (by omega)).trans hdi,
        (app_Znth1 0 key_values [key_x] i (by omega)).trans hki⟩

theorem heap_pos_consistent_add_snoc (data_values pos_values : List Int) (data_bound size data_x : Int)
    (hl : Zlength data_values = size) (hp : heap_pos_consistent data_values pos_values data_bound size)
    (hu : heap_data_unique data_values size)
    (hn : ∀ index, (0 ≤ index ∧ index < size) → Znth index data_values 0 ≠ data_x)
    (hdx : 0 ≤ data_x ∧ data_x < data_bound) :
    heap_pos_consistent (data_values ++ [data_x]) (replace_Znth data_x size pos_values) data_bound (size+1) := by
  rcases hp with ⟨hb,hpl,valid,back,forward⟩
  have hsize : 0 ≤ size := by rw [← hl]; exact Zlength_nonneg _
  have hposx := Znth_replace_Znth_Same absent pos_values data_x size (by omega)
  refine ⟨hb,(Zlength_replace_Znth _ _ _).trans hpl,?_,?_,?_⟩
  · intro i hi
    by_cases his : i = size
    · rw [his,snoc_lookup data_values size data_x hl]; exact hdx
    · rw [app_Znth1 0 data_values [data_x] i (by omega)]; exact valid i (by omega)
  · intro i hi
    by_cases his : i = size
    · rw [his,snoc_lookup data_values size data_x hl]; exact hposx
    · rw [app_Znth1 0 data_values [data_x] i (by omega)]
      have hv := valid i (by omega)
      rw [Znth_replace_Znth_Diff absent pos_values data_x (Znth i data_values 0) size (by omega) (by omega) (Ne.symm (hn i (by omega)))]
      exact back i (by omega)
  · intro dx hd
    by_cases he : dx = data_x
    · rw [he]; exact Or.inr ⟨size,by omega,snoc_lookup data_values size data_x hl,hposx⟩
    · rw [Znth_replace_Znth_Diff absent pos_values data_x dx size (by omega) (by omega) (Ne.symm he)]
      rcases forward dx hd with ha | ⟨i,hi,hdi,hpi⟩
      · exact Or.inl ha
      · exact Or.inr ⟨i,by omega,(app_Znth1 0 data_values [data_x] i (by omega)).trans hdi,hpi⟩

theorem push_write_state_from_heap_representation (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size data_x key_x : Int) (hr : heap_representation M key_values data_values pos_values data_bound size)
    (ha : partial_map_absent M data_x) (hdx : 0 ≤ data_x ∧ data_x < data_bound) (hc : size+1 ≤ heap_capacity) :
    PushWriteState M (key_values ++ [key_x]) (data_values ++ [data_x]) (replace_Znth data_x size pos_values) data_bound size data_x key_x := by
  rcases hr with ⟨hn,hcap,hm,ho,hp⟩
  have hk := hm.1
  have hd := hm.2.1
  have hnewmap := heap_map_relation_add_snoc M key_values data_values size data_x key_x hm ha
  have hnewpos := heap_pos_consistent_add_snoc data_values pos_values data_bound size data_x hd hp hm.2.2.1
    (heap_map_relation_absent_not_in_data M key_values data_values size data_x hm ha) hdx
  refine ⟨ha,⟨⟨by omega,hc,hnewmap,hnewpos⟩,by omega,?_,?_⟩,
    snoc_lookup key_values size key_x hk,snoc_lookup data_values size data_x hd,?_⟩
  · refine ⟨hn,by omega,?_⟩
    intro node hh
    have hb := heap_parent_positive_bounds node size hh.1 (by omega)
    rw [app_Znth1 0 key_values [key_x] (heap_parent node) (by omega),app_Znth1 0 key_values [key_x] node (by omega)]
    exact ho node ⟨hh.1,by omega⟩
  · intro node hh
    have hb := heap_parent_positive_bounds node (size+1) hh.1 hh.2.1
    omega
  · exact Znth_replace_Znth_Same absent pos_values data_x size (by rw [hp.2.1]; exact hdx)
theorem pop_marked_state_from_heap_representation (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size : Int) (hs : 1 ≤ size) (hr : heap_representation M key_values data_values pos_values data_bound size) :
    PopMarkedState M key_values data_values (replace_Znth (Znth 0 data_values 0) absent pos_values) data_bound size
      (heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)) := by
  have hmin := heap_root_is_partial_map_minimum M key_values data_values pos_values data_bound size hs hr
  rcases hr with ⟨hn,hc,hm,ho,hp⟩
  rcases hp with ⟨hb,hpl,valid,back,forward⟩
  have rootvalid := valid 0 (by omega)
  refine ⟨hs,hmin,hn,hc,hm,ho,hb,(Zlength_replace_Znth _ _ _).trans hpl,valid,?_,?_,rfl,rfl,?_,rootvalid⟩
  · intro i hi hn0
    have hiv := valid i hi
    have hne : Znth 0 data_values 0 ≠ Znth i data_values 0 := by
      intro he; have hh := hm.2.2.1 0 i (by omega) hi he; omega
    rw [Znth_replace_Znth_Diff absent pos_values (Znth 0 data_values 0) (Znth i data_values 0) absent (by omega) (by omega) hne]
    exact back i hi
  · intro dx hdx
    by_cases he : dx = Znth 0 data_values 0
    · rw [he]; exact Or.inl (Znth_replace_Znth_Same absent pos_values _ absent (by omega))
    · rw [Znth_replace_Znth_Diff absent pos_values (Znth 0 data_values 0) dx absent (by omega) (by omega) (Ne.symm he)]
      exact forward dx hdx
  · change Znth (Znth 0 data_values 0) (replace_Znth (Znth 0 data_values 0) absent pos_values) absent = absent
    exact Znth_replace_Znth_Same absent pos_values _ absent (by omega)

theorem heap_representation_remove_singleton (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound : Int) (hr : heap_representation M key_values data_values pos_values data_bound 1) :
    heap_representation (partial_map_remove M (Znth 0 data_values 0)) [] []
      (replace_Znth (Znth 0 data_values 0) absent pos_values) data_bound 0 := by
  rcases hr with ⟨hn,hc,hm,ho,hp⟩
  rcases hp with ⟨hb,hpl,valid,back,forward⟩
  have rootvalid := valid 0 (by omega)
  refine ⟨by omega,by decide,⟨rfl,rfl,?_,?_,?_⟩,?_,hb,(Zlength_replace_Znth _ _ _).trans hpl,?_,?_,?_⟩
  · intro i j hi hj; omega
  · intro i hi; omega
  · intro dx kx h
    by_cases he : dx = Znth 0 data_values 0
    · simp [partial_map_present,partial_map_get,partial_map_remove,he] at h
    · have hold : partial_map_present M dx kx := by simpa only [partial_map_present,partial_map_get,partial_map_remove,if_neg he] using h
      obtain ⟨i,hi,hdi,_⟩ := hm.2.2.2.2 dx kx hold
      have hz : i = 0 := by omega
      rw [hz] at hdi; exact False.elim (he hdi.symm)
  · intro child hc'; omega
  · intro i hi; omega
  · intro i hi; omega
  · intro dx hdx
    by_cases he : dx = Znth 0 data_values 0
    · rw [he]; exact Or.inl (Znth_replace_Znth_Same absent pos_values _ absent (by omega))
    · rw [Znth_replace_Znth_Diff absent pos_values (Znth 0 data_values 0) dx absent (by omega) (by omega) (Ne.symm he)]
      rcases forward dx hdx with ha | ⟨i,hi,hdi,hpi⟩
      · exact Or.inl ha
      · have hz : i = 0 := by omega
        rw [hz] at hdi; exact False.elim (he hdi.symm)

private theorem pop_lookup_zero (size : Int) (values : List Int) (hs : 1 < size) (hl : Zlength values = size) :
    Znth 0 (pop_replaced_values size values) 0 = Znth (size-1) values 0 := by
  rw [Znth_pop_replaced_values size values 0 hs hl (by omega)]
  simp [pop_replacement_source]
private theorem pop_lookup_nonzero (size : Int) (values : List Int) (i : Int)
    (hs : 1 < size) (hl : Zlength values = size) (hi : 0 ≤ i ∧ i < size-1) (hne : i ≠ 0) :
    Znth i (pop_replaced_values size values) 0 = Znth i values 0 := by
  rw [Znth_pop_replaced_values size values i hs hl hi]
  simp only [pop_replacement_source,if_neg hne]

theorem heap_map_relation_remove_root_replacement (M : partial_map) (key_values data_values : List Int)
    (size : Int) (hs : 1 < size) (hm : heap_map_relation M key_values data_values size) :
    heap_map_relation (partial_map_remove M (Znth 0 data_values 0))
      (pop_replaced_values size key_values) (pop_replaced_values size data_values) (size-1) := by
  rcases hm with ⟨hk,hd,hu,forward,back⟩
  refine ⟨Zlength_pop_replaced_values size key_values hs hk,Zlength_pop_replaced_values size data_values hs hd,?_,?_,?_⟩
  · intro i j hi hj he
    rw [Znth_pop_replaced_values size data_values i hs hd hi,Znth_pop_replaced_values size data_values j hs hd hj] at he
    have hri := pop_replacement_source_range size i hs hi
    have hrj := pop_replacement_source_range size j hs hj
    exact pop_replacement_source_injective size i j hs hi hj (hu _ _ (by omega) (by omega) he)
  · intro i hi
    rw [Znth_pop_replaced_values size key_values i hs hk hi,Znth_pop_replaced_values size data_values i hs hd hi]
    have hri := pop_replacement_source_range size i hs hi
    have hne : Znth (pop_replacement_source size i) data_values 0 ≠ Znth 0 data_values 0 := by
      intro he; have hh := hu _ 0 (by omega) (by omega) he; omega
    simpa only [partial_map_present,partial_map_get,partial_map_remove,if_neg hne] using forward _ (by omega)
  · intro dx kx h
    by_cases hroot : dx = Znth 0 data_values 0
    · simp [partial_map_present,partial_map_get,partial_map_remove,hroot] at h
    · have hold : partial_map_present M dx kx := by
        simpa only [partial_map_present,partial_map_get,partial_map_remove,if_neg hroot] using h
      obtain ⟨i,hi,hdi,hki⟩ := back dx kx hold
      have hn0 : i ≠ 0 := by intro he; rw [he] at hdi; exact hroot hdi.symm
      by_cases hlast : i = size-1
      · refine ⟨0,by omega,?_,?_⟩
        · rw [pop_lookup_zero size data_values hs hd,← hlast]; exact hdi
        · rw [pop_lookup_zero size key_values hs hk,← hlast]; exact hki
      · exact ⟨i,by omega,(pop_lookup_nonzero size data_values i hs hd (by omega) hn0).trans hdi,
          (pop_lookup_nonzero size key_values i hs hk (by omega) hn0).trans hki⟩

theorem pop_root_replacement_sift_down_state (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size : Int) (popped : Int × Int) (hs : 1 < size)
    (hmarked : PopMarkedState M key_values data_values pos_values data_bound size popped) :
    SiftDownState (partial_map_remove M (item_data popped)) (pop_replaced_values size key_values)
      (pop_replaced_values size data_values) (replace_Znth (Znth (size-1) data_values 0) 0 pos_values) data_bound (size-1) 0 := by
  rcases hmarked with ⟨hne,hmn,hn,hc,hm,ho,hb,hpl,valid,back,forward,hrootk,hrootd,hrootabs,hrootvalid⟩
  have hk := hm.1
  have hd := hm.2.1
  have hu := hm.2.2.1
  have lastvalid := valid (size-1) (by omega)
  have lastne : Znth (size-1) data_values 0 ≠ Znth 0 data_values 0 := by
    intro he; have hh := hu (size-1) 0 (by omega) (by omega) he; omega
  refine ⟨⟨by omega,by omega,?_,hb,(Zlength_replace_Znth _ _ _).trans hpl,?_,?_,?_⟩,by omega,?_,Or.inl rfl⟩
  · rw [← hrootd]
    exact heap_map_relation_remove_root_replacement M key_values data_values size hs hm
  · intro i hi
    rw [Znth_pop_replaced_values size data_values i hs hd hi]
    have hb := pop_replacement_source_range size i hs hi
    exact valid _ (by omega)
  · intro i hi
    by_cases h0 : i = 0
    · rw [h0,pop_lookup_zero size data_values hs hd]
      exact Znth_replace_Znth_Same absent pos_values _ 0 (by omega)
    · rw [pop_lookup_nonzero size data_values i hs hd hi h0]
      have hiv := valid i (by omega)
      have hneq : Znth (size-1) data_values 0 ≠ Znth i data_values 0 := by
        intro he; have hh := hu (size-1) i (by omega) (by omega) he; omega
      rw [Znth_replace_Znth_Diff absent pos_values _ _ 0 (by omega) (by omega) hneq]
      exact back i (by omega) h0
  · intro dx hdx
    by_cases hroot : dx = Znth 0 data_values 0
    · rw [hroot,Znth_replace_Znth_Diff absent pos_values _ _ 0 (by omega) (by omega) lastne,hrootd]
      exact Or.inl hrootabs
    · by_cases hlast : dx = Znth (size-1) data_values 0
      · rw [hlast]
        exact Or.inr ⟨0,by omega,pop_lookup_zero size data_values hs hd,Znth_replace_Znth_Same absent pos_values _ 0 (by omega)⟩
      · rw [Znth_replace_Znth_Diff absent pos_values _ dx 0 (by omega) (by omega) (Ne.symm hlast)]
        rcases forward dx hdx with ha | ⟨i,hi,hdi,hpi⟩
        · exact Or.inl ha
        · have h0 : i ≠ 0 := by intro he; rw [he] at hdi; exact hroot hdi.symm
          have hlast' : i ≠ size-1 := by intro he; rw [he] at hdi; exact hlast hdi.symm
          exact Or.inr ⟨i,by omega,(pop_lookup_nonzero size data_values i hs hd (by omega) h0).trans hdi,hpi⟩
  · refine ⟨by omega,by omega,?_⟩
    intro child hc'
    have hpar := heap_parent_positive_bounds child (size-1) hc'.1 hc'.2.1
    rw [pop_lookup_nonzero size key_values (heap_parent child) hs hk (by omega) hc'.2.2,
      pop_lookup_nonzero size key_values child hs hk (by omega) (by omega)]
    exact ho child ⟨hc'.1,by omega⟩

theorem sift_up_swap_state (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size child parent : Int) (hstate : SiftUpState M key_values data_values pos_values data_bound size child)
    (hc : 0 < child) (hp : parent = heap_parent child)
    (hlt : Znth parent key_values 0 > Znth child key_values 0) :
    SiftUpState M (heap_swap_values parent child key_values) (heap_swap_values parent child data_values)
      (heap_swap_pos data_values pos_values parent child) data_bound size parent := by
  rcases hstate with ⟨ha,hchild,hex,hchildren⟩
  have hlen := ha.2.2.1.1
  have hb := heap_parent_positive_bounds child size hc hchild.2
  rw [← hp] at hb
  let swapped := heap_swap_values parent child key_values
  have hs := Znth_swap_Znth key_values parent child 0 (by omega) (by omega) (by omega)
  change Znth parent swapped 0 = Znth child key_values 0 ∧ Znth child swapped 0 = Znth parent key_values 0 ∧
    (∀ k, (0 ≤ k ∧ k < Zlength key_values) → k ≠ parent → k ≠ child → Znth k swapped 0 = Znth k key_values 0) at hs
  refine ⟨heap_array_state_swap_values M key_values data_values pos_values data_bound size parent child ha (by omega) hchild (by omega),⟨hb.1,hb.2.2⟩,?_,?_⟩
  · refine ⟨hb.1,by omega,?_⟩
    intro node hh
    have hnrange : 0 ≤ node ∧ node < Zlength key_values := by omega
    have hpb := heap_parent_positive_bounds node size hh.1 hh.2.1
    by_cases hnc : node = child
    · subst node
      rw [← hp,hs.1,hs.2.1]; omega
    · have hsame := hs.2.2 node hnrange hh.2.2 hnc
      have hold := hex.2.2 node ⟨hh.1,hh.2.1,hnc⟩
      by_cases hpp : heap_parent node = parent
      · rw [hpp,hs.1,hsame]
        rw [hpp] at hold; omega
      · by_cases hpc : heap_parent node = child
        · rw [hpc,hs.2.1,hsame]
          have h := hchildren node ⟨hh.1,hh.2.1,hpc⟩
          simpa only [← hp] using h
        · rw [hs.2.2 (heap_parent node) (by omega) hpp hpc,hsame]
          exact hold
  · intro node hh
    have hpb := heap_parent_positive_bounds node size hh.1 hh.2.1
    have hnp : node ≠ parent := by omega
    by_cases hp0 : parent = 0
    · have hg : heap_parent parent = parent := by rw [hp0]; rfl
      rw [hg,hs.1]
      by_cases hnc : node = child
      · subst node; rw [hs.2.1]; omega
      · rw [hs.2.2 node (by omega) hnp hnc]
        have hold := hex.2.2 node ⟨hh.1,hh.2.1,hnc⟩
        rw [hh.2.2] at hold; omega
    · have hgp := heap_parent_positive_bounds parent size (by omega) hb.2.2
      rw [hs.2.2 (heap_parent parent) (by omega) (by omega) (by omega)]
      have hparent := hex.2.2 parent ⟨by omega,by omega,by omega⟩
      by_cases hnc : node = child
      · subst node; rw [hs.2.1]; exact hparent
      · rw [hs.2.2 node (by omega) hnp hnc]
        have hold := hex.2.2 node ⟨hh.1,hh.2.1,hnc⟩
        rw [hh.2.2] at hold; omega

theorem sift_down_swap_state (M : partial_map) (key_values data_values pos_values : List Int)
    (data_bound size current selected : Int) (hstate : SiftDownState M key_values data_values pos_values data_bound size current)
    (hsel : SelectedChild key_values size current selected)
    (hlt : Znth current key_values 0 > Znth selected key_values 0) :
    SiftDownState M (heap_swap_values current selected key_values) (heap_swap_values current selected data_values)
      (heap_swap_pos data_values pos_values current selected) data_bound size selected := by
  rcases hstate with ⟨ha,hcurrent,hex,hhole⟩
  rcases hsel with ⟨_,_,hisel,hsel0,hselb,hparent,hchoice,hdom⟩
  have hc := ha.2.2.1.1
  let swapped := heap_swap_values current selected key_values
  have hswap := Znth_swap_Znth key_values current selected 0 (by omega) (by omega) (by omega)
  change Znth current swapped 0 = Znth selected key_values 0 ∧ Znth selected swapped 0 = Znth current key_values 0 ∧
    (∀ k, (0 ≤ k ∧ k < Zlength key_values) → k ≠ current → k ≠ selected → Znth k swapped 0 = Znth k key_values 0) at hswap
  refine ⟨heap_array_state_swap_values M key_values data_values pos_values data_bound size current selected ha hcurrent ⟨hsel0,hselb⟩ (by omega),⟨hsel0,hselb⟩,?_,?_⟩
  · refine ⟨hsel0,hselb,?_⟩
    intro child hh
    have hp := heap_parent_positive_bounds child size hh.1 hh.2.1
    by_cases hpi : heap_parent child = current
    · rw [hpi,hswap.1]
      by_cases hcs : child = selected
      · subst child; rw [hswap.2.1]; omega
      · rw [hswap.2.2 child (by omega) (by omega) hcs]
        exact hdom child ⟨hh.1,hh.2.1,hpi⟩
    · by_cases hci : child = current
      · subst child
        rw [hswap.2.2 (heap_parent current) (by omega) hpi hh.2.2,hswap.1]
        rcases hhole with hzero | hdom'
        · omega
        · exact hdom' selected ⟨by omega,hselb,hparent⟩
      · have hcs : child ≠ selected := by intro he; subst child; exact hpi hparent
        rw [hswap.2.2 (heap_parent child) (by omega) hpi hh.2.2,
          hswap.2.2 child (by omega) hci hcs]
        exact hex.2.2 child ⟨hh.1,hh.2.1,hpi⟩
  · right
    intro child hh
    have hp := heap_parent_positive_bounds child size hh.1 hh.2.1
    rw [hparent,hswap.1,hswap.2.2 child (by omega) (by omega) (by omega)]
    have hold := hex.2.2 child ⟨hh.1,hh.2.1,by omega⟩
    simpa only [hh.2.2] using hold

end SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key
export priority_queue_decrease_key_lib (heap_capacity absent heap_item item_key item_data pair_list partial_map partial_map_get partial_map_add partial_map_update partial_map_update_or_add partial_map_remove partial_map_absent partial_map_present partial_map_contains partial_map_item partial_map_minimum heap_data_at heap_contains_data heap_data_absent heap_data_present heap_key_of heap_data_valid heap_data_unique heap_map_relation heap_parent heap_left_child heap_right_child heap_selected_child heap_ordered heap_pos_backlinks heap_pos_forward_links heap_pos_consistent heap_representation store_heap heap_index_of decrease_key_pre partial_map_decrease_key_pre update_or_push_pre partial_map_update_or_add_pre partial_map_update_or_add_size HeapOrderExceptUp PushHoleChildrenPreserved HeapOrderExceptDown PopHoleParentDominatesChildren SelectedChild HeapArrayState SiftUpState SiftDownState store_sift_up store_sift_down PushWriteState DecreaseKeyWriteState PopRootState heap_pos_backlinks_except PopMarkedState pop_replaced_values pop_replacement_source heap_swap_values heap_swap_pos swap_source)
end SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key
