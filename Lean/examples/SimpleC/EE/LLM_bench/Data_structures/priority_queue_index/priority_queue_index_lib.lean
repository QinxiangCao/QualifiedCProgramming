import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import AUXLib.Arithmetic
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib
open AUXLib AUXLib.Sorting
open SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

structure multiset (A : Type) where
  Build_multiset ::
  mlist : List A
export multiset (mlist)

-- Coq makes the record constructor type parameter explicit; keep constructor patterns usable.
@[match_pattern] abbrev Build_multiset (A : Type) (mlist : List A) : multiset A := multiset.Build_multiset mlist

def list_to_multiset {A : Type} (l : List A) : multiset A := ⟨l⟩

def multiset_size {A : Type} (S : multiset A) : Int := Zlength (mlist S)

def multiset_equiv {A : Type} (S1 S2 : multiset A) : Prop := Permutation (mlist S1) (mlist S2)

def multiset_insert {A : Type} (S : multiset A) (x : A) : multiset A := list_to_multiset (x :: mlist S)

noncomputable def multiset_remove {A : Type} (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (remove_one (mlist S))
where
  remove_one : List A → List A
    | [] => []
    | y :: ys => @ite (List A) (x = y) (Classical.propDecidable _) ys (y :: remove_one ys)


def heap_item (key data : Int) : Int × Int := (key,data)
def item_key (item : Int × Int) : Int := item.1
def item_data (item : Int × Int) : Int := item.2
def pair_list (key_values data_values : List Int) : List (Int × Int) := key_values.zip data_values

def multiset_min (S : multiset (Int × Int)) : Int × Int :=
  match mlist S with
  | [] => heap_item 0 0
  | x :: xs => xs.foldr (fun y best => if item_key y ≤ item_key best then y else best) x

def multiset_minimum (S : multiset (Int × Int)) (item : Int × Int) : Prop :=
  item ∈ mlist S ∧ ∀ x, x ∈ mlist S → item_key item ≤ item_key x

def heap_capacity : Int := 100000
def heap_parent (child : Int) : Int := Z.quot (child - 1) 2
def heap_left_child (index : Int) : Int := index * 2 + 1
def heap_right_child (index : Int) : Int := index * 2 + 2
def heap_selected_child (key_values : List Int) (size index : Int) : Int :=
  let left := heap_left_child index
  let right := heap_right_child index
  if right < size then
    if Znth left key_values 0 ≤ Znth right key_values 0 then left else right
  else left

def heap_relation (S : multiset (Int × Int)) (key_values data_values : List Int) : Prop :=
  Permutation (mlist S) (pair_list key_values data_values)
def heap_ordered (key_values : List Int) (size : Int) : Prop :=
  ∀ child, (0 < child ∧ child < size) → Znth (heap_parent child) key_values 0 ≤ Znth child key_values 0

def heap_representation (S : multiset (Int × Int)) (key_values data_values : List Int) (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ heap_capacity ∧ multiset_size S = size ∧ Zlength key_values = size ∧
  Zlength data_values = size ∧ heap_relation S key_values data_values ∧ heap_ordered key_values size
noncomputable def heap_spare (p size : Int) : Assertion := intArray.undef_seg p size (size + 1)
noncomputable def heap_tail (p size : Int) : Assertion :=
  if size < heap_capacity then heap_spare p size ** intArray.undef_seg p (size+1) heap_capacity
  else intArray.undef_seg p size heap_capacity
noncomputable def store_heap (key data : Int) (S : multiset (Int × Int)) (size : Int) : Assertion :=
  EX key_values : List Int, EX data_values : List Int,
    “ heap_representation S key_values data_values size ” &&
    (intArray.full key size key_values ** heap_tail key size ** intArray.full data size data_values ** heap_tail data size)
noncomputable def heap_retired_pair (key data index : Int) (item : Int × Int) : Assertion :=
  intArray.seg key index (index+1) [item_key item] ** intArray.seg data index (index+1) [item_data item]
def KeyWriteState (before : multiset (Int × Int)) (key_base data_base key_written : List Int) (size key_x : Int) : Prop :=
  heap_representation before key_base data_base size ∧ key_written = key_base ++ [key_x]
def HeapOrderExceptUp (key_values : List Int) (size child : Int) : Prop :=
  0 ≤ child ∧ child < size ∧ ∀ node, (0 < node ∧ node < size ∧ node ≠ child) →
    Znth (heap_parent node) key_values 0 ≤ Znth node key_values 0

def PushHoleChildrenPreserved (key_values : List Int) (size child : Int) : Prop :=
  ∀ node, (0 < node ∧ node < size ∧ heap_parent node = child) →
    Znth (heap_parent child) key_values 0 ≤ Znth node key_values 0

def PushSource (key_written data_written : List Int) (before : multiset (Int × Int)) (size data_x key_x : Int) : Prop :=
  Zlength key_written = size+1 ∧ Zlength data_written = size+1 ∧
  Permutation (pair_list key_written data_written) (heap_item key_x data_x :: mlist before) ∧
  heap_ordered (sublist 0 size key_written) size

def PushLoopState (key_written data_written key_current data_current : List Int) (size child data_x key_x : Int) : Prop :=
  0 ≤ size ∧ Zlength key_written = size+1 ∧ Zlength data_written = size+1 ∧
  Zlength key_current = size+1 ∧ Zlength data_current = size+1 ∧ 0 ≤ child ∧ child ≤ size ∧
  Znth child key_current 0 = key_x ∧ Znth child data_current 0 = data_x ∧
  Permutation (pair_list key_written data_written) (pair_list key_current data_current) ∧
  HeapOrderExceptUp key_current (size+1) child ∧ PushHoleChildrenPreserved key_current (size+1) child

def PushResult (before : multiset (Int × Int)) (key_result data_result : List Int) (size data_x key_x : Int) : Prop :=
  0 ≤ size ∧ Zlength key_result = size+1 ∧ Zlength data_result = size+1 ∧
  Permutation (pair_list key_result data_result) (heap_item key_x data_x :: mlist before) ∧
  heap_ordered key_result (size+1)

def BuildPrefixState («prefix» : multiset (Int × Int)) (key_input data_input : List Int) (processed : Int) : Prop :=
  1 ≤ processed ∧ processed ≤ Zlength key_input ∧ processed ≤ Zlength data_input ∧
  multiset_equiv «prefix» (list_to_multiset (pair_list (sublist 0 processed key_input) (sublist 0 processed data_input)))
def PrefixMinimum (key_values data_values : List Int) (size : Int) (item : Int × Int) : Prop :=
  0 < size ∧ size ≤ Zlength key_values ∧ size ≤ Zlength data_values ∧
  item = heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) ∧
  ∀ i, (0 ≤ i ∧ i < size) → item_key item ≤ Znth i key_values 0

def HeapOrderExceptDown (key_values : List Int) (size index : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ ∀ child, (0 < child ∧ child < size ∧ heap_parent child ≠ index) →
  Znth (heap_parent child) key_values 0 ≤ Znth child key_values 0

def PopHoleParentDominatesChildren (key_values : List Int) (size index : Int) : Prop :=
  index = 0 ∨ ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) →
    Znth (heap_parent index) key_values 0 ≤ Znth child key_values 0

def PopSelectedChild (key_values : List Int) (size index selected : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ index < selected ∧ 0 ≤ selected ∧ selected < size ∧
  heap_parent selected = index ∧ selected = heap_selected_child key_values size index ∧
  ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) → Znth selected key_values 0 ≤ Znth child key_values 0

def PopRemainingElements (before_key before_data current_key current_data : List Int) (size : Int) : Prop :=
  1 ≤ size ∧ size ≤ Zlength before_key ∧ size ≤ Zlength before_data ∧
  size ≤ Zlength current_key ∧ size ≤ Zlength current_data ∧
  Permutation (pair_list (sublist 0 (size-1) current_key) (sublist 0 (size-1) current_data))
    (pair_list (sublist 1 size before_key) (sublist 1 size before_data))

def PopLoopState (before_key before_data current_key current_data : List Int) (size index : Int) : Prop :=
  1 < size ∧ Zlength before_key = size ∧ Zlength before_data = size ∧
  Zlength current_key = size ∧ Zlength current_data = size ∧ 0 ≤ index ∧ index < size-1 ∧
  heap_ordered before_key size ∧ Znth index current_key 0 = Znth (size-1) before_key 0 ∧
  Znth index current_data 0 = Znth (size-1) before_data 0 ∧
  PopRemainingElements before_key before_data current_key current_data size ∧
  HeapOrderExceptDown current_key (size-1) index ∧ PopHoleParentDominatesChildren current_key (size-1) index

def PopReadyState (before_key before_data current_key current_data : List Int) (size : Int) (item : Int × Int) : Prop :=
  1 < size ∧ Zlength before_key = size ∧ Zlength before_data = size ∧ Zlength current_key = size ∧
  Zlength current_data = size ∧ heap_ordered before_key size ∧ PrefixMinimum before_key before_data size item ∧
  PopRemainingElements before_key before_data current_key current_data size ∧ heap_ordered current_key (size-1)

def PopResult (S : multiset (Int × Int)) (before_key before_data result_key result_data : List Int) (size : Int) (item : Int × Int) : Prop :=
  1 ≤ size ∧ Zlength before_key = size ∧ Zlength before_data = size ∧ Zlength result_key = size ∧
  Zlength result_data = size ∧ heap_ordered (sublist 0 (size-1) result_key) (size-1) ∧
  Permutation (pair_list (sublist 0 (size-1) result_key) (sublist 0 (size-1) result_data)) (mlist (multiset_remove S item))
theorem multiset_equiv_size (A : Type) (S1 S2 : multiset A) (h : multiset_equiv S1 S2) :
    multiset_size S1 = multiset_size S2 := congrArg Int.ofNat h.length_eq

theorem multiset_remove_spec {A : Type} (S : multiset A) (x : A) :
    (x ∈ mlist S → multiset_size (multiset_remove S x) = multiset_size S - 1 ∧
      Permutation (mlist S) (x :: mlist (multiset_remove S x))) ∧
    (x ∉ mlist S → multiset_remove S x = S) := by
  classical
  rcases S with ⟨l⟩
  induction l with
  | nil => simp [multiset_remove, multiset_remove.remove_one, list_to_multiset]
  | cons y ys ih =>
    by_cases he : x = y
    · subst y
      simp [multiset_remove, multiset_remove.remove_one, list_to_multiset, multiset_size, Zlength]
    · simp only [multiset_remove, multiset_remove.remove_one, if_neg he, list_to_multiset, multiset_size] at *
      constructor
      · intro hm
        have hh : x ∈ ys := (List.mem_cons.mp hm).resolve_left he
        obtain ⟨hl, hp⟩ := ih.1 hh
        exact ⟨by simp only [Zlength_cons]; omega,
          (hp.cons y).trans (List.Perm.swap x y _)⟩
      · intro hm
        have hh : x ∉ ys := fun h => hm (List.mem_cons_of_mem y h)
        have hh' := ih.2 hh
        have heq := congrArg mlist hh'
        simpa only [mlist] using congrArg (fun l => multiset.Build_multiset (y :: l)) heq


theorem heap_parent_positive_bounds__push_sift_up (child size : Int) (hc : 0 < child) (hs : child ≤ size) :
    0 ≤ heap_parent child ∧ heap_parent child < child ∧ heap_parent child ≤ size := by
  unfold heap_parent Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega


theorem heap_children_characterization__pop_child_selection (index child : Int)
    (hi : 0 ≤ index) (hc : 0 < child) (hp : heap_parent child = index) :
    child = heap_left_child index ∨ child = heap_right_child index := by
  unfold heap_parent Z.quot at hp
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hp
  unfold heap_left_child heap_right_child
  omega


private theorem parent_left (i : Int) (hi : 0 ≤ i) : heap_parent (heap_left_child i) = i := by
  unfold heap_parent heap_left_child Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

private theorem parent_right (i : Int) (hi : 0 ≤ i) : heap_parent (heap_right_child i) = i := by
  unfold heap_parent heap_right_child Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega


theorem heap_parent_nonnegative_lt__pop_swap_transition (child : Int) (hc : 0 < child) :
    0 ≤ heap_parent child ∧ heap_parent child < child :=
  let h := heap_parent_positive_bounds__push_sift_up child child hc (by omega)
  ⟨h.1,h.2.1⟩


theorem pop_next_index_arithmetic__pop_swap_transition (current : List Int) (size index selected : Int)
    (hi : 0 ≤ index) (hs : selected < size) (he : selected = heap_selected_child current size index) :
    0 ≤ heap_left_child index ∧ heap_left_child index < size ∧
      0 ≤ heap_right_child index ∧ heap_right_child index ≤ size := by
  dsimp only [heap_selected_child] at he
  split at he <;> try split at he
  all_goals unfold heap_left_child heap_right_child at *
  all_goals omega


private theorem prefix_len {A : Type} (l : List A) (n : Int) (hn : 0 ≤ n ∧ n ≤ Zlength l) :
    Zlength (sublist 0 n l) = n := by
  unfold Zlength
  rw [sublist_length 0 n l (by omega) hn.2]
  simp only [Int.sub_zero,Int.ofNat_eq_coe]
  omega


private theorem Znth_prefix {A : Type} (l : List A) (d : A) (n i : Int) (hi : 0 ≤ i ∧ i < n) :
    Znth i (sublist 0 n l) d = Znth i l d := by
  simpa only [Int.add_zero] using Znth_sublist d 0 i n l (by omega) (by omega)


private theorem zlist_ext {A : Type} (l1 l2 : List A) (d : A) (hl : Zlength l1 = Zlength l2)
    (he : ∀ i, (0 ≤ i ∧ i < Zlength l1) → Znth i l1 d = Znth i l2 d) : l1 = l2 := by
  have hl' : l1.length = l2.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
  apply List.ext_getElem hl'
  intro i hi1 hi2
  have h := he i ⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi1,
    List.getElem?_eq_getElem hi2,Option.getD_some] using h


theorem sublist0_replace_Znth_inside__pop_swap_transition (l : List Int) (hi i value : Int)
    (hi' : 0 ≤ i ∧ i < hi) (hl : hi ≤ Zlength l) :
    sublist 0 hi (replace_Znth i value l) = replace_Znth i value (sublist 0 hi l) := by
  have hlen : Zlength (replace_Znth i value l) = Zlength l := Zlength_replace_Znth _ _ _
  have hp : Zlength (sublist 0 hi l) = hi := prefix_len l hi (by omega)
  apply zlist_ext _ _ 0
  · rw [prefix_len _ hi (by omega),Zlength_replace_Znth,hp]
  · intro k hk
    rw [prefix_len _ hi (by omega)] at hk
    rw [Znth_prefix _ 0 hi k hk]
    by_cases he : k = i
    · subst k
      rw [Znth_replace_Znth_Same 0 l i _ (by omega),Znth_replace_Znth_Same 0 _ i _ (by omega)]
    · rw [Znth_replace_Znth_Diff 0 l i k _ (by omega) (by omega) (Ne.symm he),
        Znth_replace_Znth_Diff 0 _ i k _ (by omega) (by omega) (Ne.symm he),Znth_prefix l 0 hi k hk]


theorem sublist_replace_last__pop_finalization (A : Type) (d v : A) (l : List A) (n : Int)
    (hn : 0 < n) (hl : Zlength l = n) :
    sublist 0 (n-1) (replace_Znth (n-1) v l) = sublist 0 (n-1) l := by
  have hlen : Zlength (replace_Znth (n-1) v l) = n := (Zlength_replace_Znth _ _ _).trans hl
  apply zlist_ext _ _ d
  · rw [prefix_len _ (n-1) (by omega),prefix_len l (n-1) (by omega)]
  · intro i hi
    rw [prefix_len _ (n-1) (by omega)] at hi
    rw [Znth_prefix _ d (n-1) i hi,Znth_prefix _ d (n-1) i hi]
    exact Znth_replace_Znth_Diff d l (n-1) i v (by omega) (by omega) (by omega)


theorem heap_ordered_sublist0__pop_finalization (concrete : List Int) (size : Int)
    (ho : heap_ordered concrete size) : heap_ordered (sublist 0 size concrete) size := by
  intro child hc
  have hp := heap_parent_nonnegative_lt__pop_swap_transition child hc.1
  rw [Znth_prefix concrete 0 size (heap_parent child) (by omega),Znth_prefix concrete 0 size child (by omega)]
  exact ho child hc


private theorem app_Znth1 (d : Int) (l1 l2 : List Int) (i : Int)
    (h : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1 ++ l2) d = Znth i l1 d := by
  have hn : i.toNat < l1.length := by simp only [Zlength, Int.ofNat_eq_coe] at h; omega
  simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_append_left hn]


private theorem sublist_one (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    sublist i (i+1) l = [Znth i l 0] := by
  exact sublist_single 0 i l hi


private theorem sublist_prefix_snoc (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l 0] := by
  rw [sublist_split 0 (i+1) i l (by omega) (by omega),sublist_one l i hi]


theorem replace_Znth_swap_form {A : Type} (l1 l2 l3 : List A) (xi xj : A) :
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
    l1 ++ (xj :: (l2 ++ (xi :: l3))) := by
  rw [replace_Znth_boundary_local]
  have he : l1 ++ (xj :: (l2 ++ (xj :: l3))) = (l1 ++ xj :: l2) ++ xj :: l3 := by simp
  rw [he, show Zlength l1 + 1 + Zlength l2 = Zlength (l1 ++ xj :: l2) by simp [Zlength] <;> omega]
  rw [replace_Znth_boundary_local]
  simp


private theorem perm_replace_head {A : Type} (l : List A) (k : Nat) (x d : A) (hk : k < l.length) :
    Permutation (x :: l) (l.getD k d :: replace_nth k l x) := by
  induction l generalizing k x with
  | nil => simp at hk
  | cons y l ih =>
    cases k with
    | zero => exact List.Perm.swap y x l
    | succ k =>
      simp only [List.getD_cons_succ, replace_nth]
      exact (List.Perm.swap y x l).trans
        ((ih k x (by simpa using hk)).cons y |>.trans (List.Perm.swap _ _ _))


private theorem permutation_swap_nat {A : Type} (l : List A) (i j : Nat) (d : A)
    (hij : i < j) (hj : j < l.length) :
    Permutation l (replace_nth j (replace_nth i l (l.getD j d)) (l.getD i d)) := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_zero, List.getD_cons_succ] using
          perm_replace_head l j x d (by simpa using hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_succ] using
          (ih i j (by omega) (by simpa using hj)).cons x


theorem permutation_swap_Znth_lt {A : Type} (l : List A) (i j : Int) (d : A)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  apply permutation_swap_nat
  · omega
  · simp only [Zlength,Int.ofNat_eq_coe] at h; omega


theorem replace_nth_comm {A : Type} (ni nj : Nat) (l : List A) (a b : A) (h : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a := by
  induction l generalizing ni nj with
  | nil => simp [replace_nth]
  | cons x l ih =>
    cases ni <;> cases nj <;> simp_all [replace_nth]


theorem replace_Znth_comm {A : Type} (l : List A) (i j : Int) (a b : A)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) := by
  apply replace_nth_comm; omega


theorem permutation_swap_Znth {A : Type} (l : List A) (i j : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  by_cases he : i = j
  · subst j; simp only [replace_Znth_Znth]; exact List.Perm.refl _
  · by_cases hlt : i < j
    · exact permutation_swap_Znth_lt l i j d ⟨hi.1,hlt,hj.2⟩
    · rw [replace_Znth_comm l i j _ _ hi.1 hj.1 he]
      exact permutation_swap_Znth_lt l j i d ⟨hj.1,by omega,hi.2⟩


theorem Znth_swap_Znth {A : Type} (l : List A) (i j : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hne : i ≠ j) :
    let swapped := replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)
    Znth i swapped d = Znth j l d ∧ Znth j swapped d = Znth i l d ∧
    ∀ k, (0 ≤ k ∧ k < Zlength l) → k ≠ i → k ≠ j → Znth k swapped d = Znth k l d := by
  dsimp only
  have hl : Zlength (replace_Znth i (Znth j l d) l) = Zlength l := Zlength_replace_Znth _ _ _
  refine ⟨?_,?_,?_⟩
  · rw [Znth_replace_Znth_Diff d _ j i _ (by omega) (by omega) (Ne.symm hne), Znth_replace_Znth_Same d l i _ hi]
  · exact Znth_replace_Znth_Same d _ j _ (by omega)
  · intro k hk hki hkj
    rw [Znth_replace_Znth_Diff d _ j k _ (by omega) (by omega) (Ne.symm hkj),
      Znth_replace_Znth_Diff d l i k _ hi hk (Ne.symm hki)]


theorem heap_tail_to_undef_seg (p size : Int) (hr : 0 ≤ size ∧ size ≤ heap_capacity) :
    heap_tail p size |-- intArray.undef_seg p size heap_capacity := by
  unfold heap_tail
  split
  · unfold heap_spare
    sep_apply (intArray.undef_seg_merge_to_undef_seg p size (size+1) heap_capacity (by omega))
    cancel
  · cancel

theorem undef_seg_to_heap_tail (p size : Int) (hr : 0 ≤ size ∧ size ≤ heap_capacity) :
    intArray.undef_seg p size heap_capacity |-- heap_tail p size := by
  unfold heap_tail
  split
  · unfold heap_spare
    sep_apply (intArray.undef_seg_split_to_undef_seg p size (size+1) heap_capacity (by omega))
    cancel
  · cancel

theorem concrete_arrays_to_store_heap__build_finalization (key data : Int) (S : multiset (Int × Int))
    (key_values data_values : List Int) (size : Int) (hb : 0 ≤ size ∧ size ≤ heap_capacity)
    (hr : heap_representation S key_values data_values size) :
    intArray.full key size key_values ** intArray.undef_seg key size heap_capacity **
    intArray.full data size data_values ** intArray.undef_seg data size heap_capacity |-- store_heap key data S size := by
  unfold store_heap
  Exists key_values data_values
  sep_apply (undef_seg_to_heap_tail key size hb)
  sep_apply (undef_seg_to_heap_tail data size hb)
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hr

theorem fold_right_item_min_member (xs : List (Int × Int)) (base : Int × Int) :
    xs.foldr (fun y best => if item_key y ≤ item_key best then y else best) base ∈ base :: xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    split
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp ih with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

theorem fold_right_item_min_lower_bound (xs : List (Int × Int)) (base value : Int × Int)
    (h : value ∈ base :: xs) :
    item_key (xs.foldr (fun y best => if item_key y ≤ item_key best then y else best) base) ≤ item_key value := by
  induction xs with
  | nil => have he : value = base := by simpa using h
           subst value; exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldr_cons]
    have hh : value = x ∨ value ∈ base :: xs := by
      simp only [List.mem_cons] at h ⊢
      rcases h with he | he | hm
      · exact Or.inr (Or.inl he)
      · exact Or.inl he
      · exact Or.inr (Or.inr hm)
    rcases hh with he | hm
    · subst value; split <;> omega
    · have hb := ih hm; split <;> omega

theorem multiset_min_is_minimum (S : multiset (Int × Int)) (h : mlist S ≠ []) :
    multiset_minimum S (multiset_min S) := by
  rcases S with ⟨l⟩
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x xs => exact ⟨fold_right_item_min_member xs x, fun v hv => fold_right_item_min_lower_bound xs x v hv⟩
theorem multiset_min_member (S : multiset (Int × Int)) (h : mlist S ≠ []) : multiset_min S ∈ mlist S :=
  (multiset_min_is_minimum S h).1
theorem multiset_min_lower_bound (S : multiset (Int × Int)) (value : Int × Int) (h : mlist S ≠ [])
    (hm : value ∈ mlist S) : item_key (multiset_min S) ≤ item_key value := (multiset_min_is_minimum S h).2 value hm
theorem multiset_remove_min_size (S : multiset (Int × Int)) (h : mlist S ≠ []) :
    multiset_size (multiset_remove S (multiset_min S)) = multiset_size S - 1 :=
  ((multiset_remove_spec S (multiset_min S)).1 (multiset_min_member S h)).1

theorem Zlength_combine_eq {A B : Type} (l1 : List A) (l2 : List B) (hl : Zlength l1 = Zlength l2) :
    Zlength (l1.zip l2) = Zlength l1 := by
  simp only [Zlength, List.length_zip, Int.ofNat_eq_coe] at *
  omega

theorem Znth_combine_eq {A B : Type} (i : Int) (l1 : List A) (l2 : List B) (d1 : A) (d2 : B)
    (hi : 0 ≤ i ∧ i < Zlength l1) (hl : Zlength l1 = Zlength l2) :
    Znth i (l1.zip l2) (d1,d2) = (Znth i l1 d1, Znth i l2 d2) := by
  have h1 : i.toNat < l1.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  have h2 : i.toNat < l2.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.zip_eq_zipWith,List.getElem?_zipWith,
    List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2,Option.bind_some,Option.map_some,Option.getD_some]

theorem pair_list_app_single (key_values data_values : List Int) (key_x data_x : Int)
    (hl : Zlength key_values = Zlength data_values) :
    pair_list (key_values ++ [key_x]) (data_values ++ [data_x]) =
    pair_list key_values data_values ++ [heap_item key_x data_x] := by
  have hlen : key_values.length = data_values.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
  exact List.zip_append hlen

theorem pair_list_sublist_snoc (key_values data_values : List Int) (i : Int)
    (hl : Zlength key_values = Zlength data_values) (hi : 0 ≤ i ∧ i < Zlength key_values) :
    pair_list (sublist 0 (i+1) key_values) (sublist 0 (i+1) data_values) =
    pair_list (sublist 0 i key_values) (sublist 0 i data_values) ++ [heap_item (Znth i key_values 0) (Znth i data_values 0)] := by
  rw [sublist_prefix_snoc key_values i hi,sublist_prefix_snoc data_values i (by omega)]
  exact pair_list_app_single _ _ _ _ (by rw [prefix_len _ i (by omega),prefix_len _ i (by omega)])

theorem pair_list_sublist_self (key_values data_values : List Int) (n : Int)
    (hk : Zlength key_values = n) (hd : Zlength data_values = n) :
    pair_list (sublist 0 n key_values) (sublist 0 n data_values) = pair_list key_values data_values := by
  rw [sublist_self key_values n hk.symm,sublist_self data_values n hd.symm]

theorem pair_list_cons_split (key_values data_values : List Int) (size : Int) (hs : 0 < size)
    (hk : Zlength key_values = size) (hd : Zlength data_values = size) :
    pair_list key_values data_values = heap_item (Znth 0 key_values 0) (Znth 0 data_values 0) ::
      pair_list (sublist 1 size key_values) (sublist 1 size data_values) := by
  have hks := sublist_split 0 size 1 key_values (by omega) (by omega)
  rw [sublist_self key_values size hk.symm,show sublist 0 1 key_values = [Znth 0 key_values 0] from sublist_one key_values 0 (by omega)] at hks
  have hds := sublist_split 0 size 1 data_values (by omega) (by omega)
  rw [sublist_self data_values size hd.symm,show sublist 0 1 data_values = [Znth 0 data_values 0] from sublist_one data_values 0 (by omega)] at hds
  conv => lhs; rw [hks,hds]
  rfl

theorem pair_list_sublist (key_values data_values : List Int) (lo hi : Int)
    (hl : Zlength key_values = Zlength data_values) (hr : 0 ≤ lo ∧ lo ≤ hi) (hb : hi ≤ Zlength key_values) :
    pair_list (sublist lo hi key_values) (sublist lo hi data_values) = sublist lo hi (pair_list key_values data_values) := by
  simp only [pair_list,sublist,List.zip_eq_zipWith,List.take_zipWith,List.drop_zipWith]

theorem combine_replace_Znth_both (i : Int) (key_values data_values : List Int) (key_x data_x : Int)
    (hi : 0 ≤ i ∧ i < Zlength key_values) (hl : Zlength key_values = Zlength data_values) :
    pair_list (replace_Znth i key_x key_values) (replace_Znth i data_x data_values) =
    replace_Znth i (heap_item key_x data_x) (pair_list key_values data_values) := by
  have hh (n : Nat) (ks ds : List Int) :
      (replace_nth n ks key_x).zip (replace_nth n ds data_x) = replace_nth n (ks.zip ds) (key_x,data_x) := by
    induction n generalizing ks ds with
    | zero => cases ks <;> cases ds <;> rfl
    | succ n ih => cases ks <;> cases ds <;> simp [replace_nth,ih]
  exact hh i.toNat key_values data_values

theorem pair_list_swap_Znth (key_values data_values : List Int) (i j : Int)
    (hl : Zlength key_values = Zlength data_values)
    (hi : 0 ≤ i ∧ i < Zlength key_values) (hj : 0 ≤ j ∧ j < Zlength key_values) :
    Permutation (pair_list key_values data_values)
      (pair_list (replace_Znth j (Znth i key_values 0) (replace_Znth i (Znth j key_values 0) key_values))
        (replace_Znth j (Znth i data_values 0) (replace_Znth i (Znth j data_values 0) data_values))) := by
  rw [combine_replace_Znth_both j _ _ _ _ (by rw [Zlength_replace_Znth]; exact hj)
      (by rw [Zlength_replace_Znth,Zlength_replace_Znth]; exact hl),combine_replace_Znth_both i _ _ _ _ hi hl]
  rw [show heap_item (Znth i key_values 0) (Znth i data_values 0) = Znth i (pair_list key_values data_values) (0,0) from (Znth_combine_eq i _ _ 0 0 hi hl).symm,
      show heap_item (Znth j key_values 0) (Znth j data_values 0) = Znth j (pair_list key_values data_values) (0,0) from (Znth_combine_eq j _ _ 0 0 hj hl).symm]
  have hlen : Zlength (pair_list key_values data_values) = Zlength key_values := Zlength_combine_eq _ _ hl
  exact permutation_swap_Znth _ i j (0,0) (by omega) (by omega)
theorem push_appended_source__push_initialization (S : multiset (Int × Int)) (key_base data_base : List Int)
    (size data_x key_x : Int) (h : heap_representation S key_base data_base size) :
    PushSource (key_base ++ [key_x]) (data_base ++ [data_x]) S size data_x key_x := by
  rcases h with ⟨hn,hc,hm,hk,hd,hp,ho⟩
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega,
    by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega,?_,?_⟩
  · rw [pair_list_app_single _ _ _ _ (by omega)]
    exact (hp.symm.append (List.Perm.refl [_])).trans List.perm_append_comm
  · rw [← hk,sublist_app_exact1]; simpa only [hk] using ho

theorem push_appended_loop_state__push_initialization (S : multiset (Int × Int)) (key_base data_base : List Int)
    (size data_x key_x : Int) (h : heap_representation S key_base data_base size) :
    PushLoopState (key_base ++ [key_x]) (data_base ++ [data_x]) (key_base ++ [key_x]) (data_base ++ [data_x]) size size data_x key_x := by
  rcases h with ⟨hn,hc,hm,hk,hd,hp,ho⟩
  have hklen : Zlength (key_base ++ [key_x]) = size+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  have hdlen : Zlength (data_base ++ [data_x]) = size+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  refine ⟨hn,hklen,hdlen,hklen,hdlen,hn,by omega,?_,?_,List.Perm.refl _,?_,?_⟩
  · rw [app_Znth2 0 key_base [key_x] size (by omega),hk]; simp [Znth]
  · rw [app_Znth2 0 data_base [data_x] size (by omega),hd]; simp [Znth]
  · refine ⟨hn,by omega,?_⟩
    intro node hh
    have hb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    rw [app_Znth1 0 key_base [key_x] (heap_parent node) (by omega),app_Znth1 0 key_base [key_x] node (by omega)]
    exact ho node ⟨hh.1,by omega⟩
  · intro node hh
    have hb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    omega

theorem push_break_establishes_result__push_sift_up (before : multiset (Int × Int))
    (key_written data_written key_current data_current : List Int) (size child parent data_x key_x : Int)
    (hs : PushSource key_written data_written before size data_x key_x)
    (hl : PushLoopState key_written data_written key_current data_current size child data_x key_x)
    (hp : parent = heap_parent child) (hd : Znth parent key_current 0 ≤ Znth child key_current 0) :
    PushResult before key_current data_current size data_x key_x := by
  rcases hs with ⟨_,_,hsp,_⟩
  rcases hl with ⟨hn,_,_,hk,hdata,_,_,_,_,hcp,he,_⟩
  refine ⟨hn,hk,hdata,hcp.symm.trans hsp,?_⟩
  intro node hh
  by_cases hnc : node = child
  · subst node; simpa [hp] using hd
  · exact he.2.2 node ⟨hh.1,hh.2,hnc⟩

theorem push_zero_exit_result__push_finalization (before : multiset (Int × Int))
    (key_written data_written key_current data_current : List Int) (size data_x key_x : Int)
    (hs : PushSource key_written data_written before size data_x key_x)
    (hl : PushLoopState key_written data_written key_current data_current size 0 data_x key_x) :
    PushResult before key_current data_current size data_x key_x := by
  rcases hs with ⟨_,_,hsp,_⟩
  rcases hl with ⟨hn,_,_,hk,hd,_,_,_,_,hcp,he,_⟩
  exact ⟨hn,hk,hd,hcp.symm.trans hsp,fun node hh => he.2.2 node ⟨hh.1,hh.2,by omega⟩⟩

theorem push_result_representation__push_finalization (before : multiset (Int × Int)) (key_result data_result : List Int)
    (size data_x key_x : Int) (hc : size < heap_capacity) (h : PushResult before key_result data_result size data_x key_x) :
    heap_representation (multiset_insert before (heap_item key_x data_x)) key_result data_result (size+1) := by
  rcases h with ⟨hn,hk,hd,hp,ho⟩
  refine ⟨by omega,by omega,?_,hk,hd,hp.symm,ho⟩
  exact (congrArg Int.ofNat hp.symm.length_eq).trans ((Zlength_combine_eq _ _ (by omega)).trans hk)

theorem store_heap_equiv_transport__build_finalization (S1 S2 : multiset (Int × Int)) (key_values data_values : List Int)
    (size : Int) (hp : multiset_equiv S1 S2) (hr : heap_representation S1 key_values data_values size) :
    heap_representation S2 key_values data_values size := by
  rcases hr with ⟨hn,hc,hs,hk,hd,hp',ho⟩
  exact ⟨hn,hc,(multiset_equiv_size _ S1 S2 hp).symm.trans hs,hk,hd,hp.symm.trans hp',ho⟩

theorem build_prefix_complete__build_finalization («prefix» : multiset (Int × Int)) (key_input data_input : List Int)
    (processed : Int) (h : BuildPrefixState «prefix» key_input data_input processed)
    (hp : processed = Zlength key_input) (hl : Zlength key_input = Zlength data_input) :
    multiset_equiv «prefix» (list_to_multiset (pair_list key_input data_input)) := by
  rcases h with ⟨_,_,_,hh⟩
  simpa only [sublist_self key_input processed hp,sublist_self data_input processed (hp.trans hl)] using hh

theorem build_initial_prefix__build_progress (key_input data_input : List Int) (n : Int)
    (hk : Zlength key_input = n) (hd : Zlength data_input = n) (hn : 1 ≤ n) :
    BuildPrefixState (list_to_multiset [heap_item (Znth 0 key_input 0) (Znth 0 data_input 0)]) key_input data_input 1 ∧
    heap_representation (list_to_multiset [heap_item (Znth 0 key_input 0) (Znth 0 data_input 0)])
      (sublist 0 1 key_input) (sublist 0 1 data_input) 1 := by
  have hks := sublist_one key_input 0 (by omega)
  have hds := sublist_one data_input 0 (by omega)
  simp only [Int.zero_add] at hks hds
  refine ⟨⟨by omega,by omega,by omega,?_⟩,by omega,by decide,rfl,?_,?_,?_,?_⟩
  · change ([_] : List (Int × Int)).Perm (pair_list _ _); rw [hks,hds]; exact List.Perm.refl _
  · rw [hks]; rfl
  · rw [hds]; rfl
  · change ([_] : List (Int × Int)).Perm (pair_list _ _); rw [hks,hds]; exact List.Perm.refl _
  · intro child hc; omega

theorem build_prefix_extend__build_progress («prefix» : multiset (Int × Int)) (key_input data_input : List Int)
    (i data_x key_x : Int) (hi : 1 ≤ i) (hil : i < Zlength key_input) (hl : Zlength key_input = Zlength data_input)
    (hd : data_x = Znth i data_input 0) (hk : key_x = Znth i key_input 0)
    (h : BuildPrefixState «prefix» key_input data_input i) :
    BuildPrefixState (multiset_insert «prefix» (heap_item key_x data_x)) key_input data_input (i+1) := by
  refine ⟨by omega,by omega,by omega,?_⟩
  change (heap_item key_x data_x :: mlist «prefix»).Perm (pair_list _ _)
  rw [pair_list_sublist_snoc _ _ i hl (by omega),← hk,← hd]
  exact (h.2.2.2.cons _).trans (List.perm_append_singleton _ _).symm

theorem In_Znth_Zlength {A : Type} (l : List A) (x d : A) (hm : x ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l d = x := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩,?_⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using he

theorem heap_ordered_root_lower_bound__pop_initialization (key_values : List Int) (size index : Int)
    (ho : heap_ordered key_values size) (hi : 0 ≤ index ∧ index < size) :
    Znth 0 key_values 0 ≤ Znth index key_values 0 := by
  have h (n : Nat) : ∀ i : Int, i.toNat = n → (0 ≤ i ∧ i < size) → Znth 0 key_values 0 ≤ Znth i key_values 0 := by
    intro i hn hb
    induction n using Nat.strongRecOn generalizing i with
    | ind n ih =>
      by_cases h0 : i = 0
      · subst i; omega
      · have hp := heap_parent_positive_bounds__push_sift_up i size (by omega) (by omega)
        have hr := ih (heap_parent i).toNat (by omega) (heap_parent i) rfl ⟨hp.1,by omega⟩
        exact Int.le_trans hr (ho i ⟨by omega,hb.2⟩)
  exact h index.toNat index rfl hi

theorem heap_root_is_multiset_minimum__pop_initialization (S : multiset (Int × Int))
    (key_values data_values : List Int) (size : Int) (hs : 1 ≤ size)
    (hr : heap_representation S key_values data_values size) :
    let item := heap_item (Znth 0 key_values 0) (Znth 0 data_values 0)
    PrefixMinimum key_values data_values size item ∧ multiset_minimum S item := by
  rcases hr with ⟨hn,hc,hms,hk,hd,hp,ho⟩
  dsimp only
  have hsplit := pair_list_cons_split key_values data_values size (by omega) hk hd
  refine ⟨⟨by omega,by omega,by omega,rfl,fun i hi => heap_ordered_root_lower_bound__pop_initialization key_values size i ho hi⟩,?_,?_⟩
  · apply hp.mem_iff.mpr
    rw [hsplit]; exact List.mem_cons_self
  · intro x hx
    obtain ⟨i,hi,hix⟩ := In_Znth_Zlength (pair_list key_values data_values) x (0,0) (hp.mem_iff.mp hx)
    have hlen : Zlength (pair_list key_values data_values) = size := (Zlength_combine_eq _ _ (by omega)).trans hk
    unfold pair_list at hix
    rw [Znth_combine_eq i key_values data_values 0 0 (by omega) (by omega)] at hix
    rw [← hix]
    exact heap_ordered_root_lower_bound__pop_initialization key_values size i ho (by omega)

private theorem generic_sublist_prefix_snoc {A : Type} (l : List A) (d : A) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l d] := by
  rw [sublist_split 0 (i+1) i l (by omega) (by omega),sublist_single d i l hi]
theorem pop_root_replacement_remaining_permutation__pop_initialization {A : Type} (before : List A) (size : Int) (d : A)
    (hs : 1 < size) (hl : Zlength before = size) :
    Permutation (sublist 0 (size-1) (replace_Znth 0 (Znth (size-1) before d) before)) (sublist 1 size before) := by
  cases before with
  | nil => simp only [Zlength_nil] at hl; omega
  | cons x l =>
    have hllen : Zlength l = size-1 := by simp only [Zlength_cons] at hl; omega
    change Permutation (sublist 0 (size-1) (Znth (size-1) (x::l) d :: l)) (sublist 1 size (x::l))
    rw [Znth_cons d (size-1) x l (by omega),sublist_cons1 (size-1) _ l (by omega)]
    have he : sublist 1 size (x::l) = l := by
      unfold sublist
      have hn : size.toNat = l.length+1 := by simp only [Zlength,Int.ofNat_eq_coe] at hllen; omega
      simp [hn]
    rw [he]
    have ht := generic_sublist_prefix_snoc l d (size-2) (by omega)
    have he' : sublist 0 (size-2+1) l = l := sublist_self l _ (by omega)
    rw [he'] at ht
    rw [show size-1-1=size-2 by omega]
    exact (List.perm_append_singleton _ _).symm.trans (List.Perm.of_eq ht.symm)

theorem build_split_next_cell__build_progress (heap i n : Int) (input : List Int)
    (hi : 0 ≤ i ∧ i < n) (hl : n ≤ Zlength input) :
    intArray.seg heap i n (sublist i n input) |-- heap_spare heap i ** intArray.seg heap (i+1) n (sublist (i+1) n input) := by
  unfold heap_spare
  rw [sublist_split i n (i+1) input (by omega) (by omega),sublist_one input i (by omega),List.singleton_append]
  sep_apply ((intArray.seg_unfold heap i n (sublist (i+1) n input) (Znth i input (0 : Int))).1)
  sep_apply (intArray.seg_single heap i (Znth i input (0 : Int)))
  sep_apply (intArray.seg_to_undef_seg heap i (i+1) [Znth i input (0 : Int)])
  cancel

theorem singleton_full_split_spare__pop_singleton (p : Int) (before : List Int)
    (hl : Zlength before = 1) :
    intArray.full p 1 before |-- intArray.full p 0 [] ** intArray.undef_seg p 0 1 := by
  sep_apply (intArray.full_split_to_seg p 0 1 before (by omega))
  rw [Zsublist_nil before 0 0 (by omega)]
  sep_apply (intArray.seg_to_full p 0 0 [])
  sep_apply (intArray.seg_to_undef_seg p 0 1 (sublist 0 1 before))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero,Int.zero_add]
  cancel

theorem pop_select_left__pop_child_selection (current : List Int) (size index : Int)
    (hi : 0 ≤ index) (hl : heap_left_child index < size)
    (hs : heap_right_child index ≥ size ∨ Znth (heap_left_child index) current 0 ≤ Znth (heap_right_child index) current 0) :
    PopSelectedChild current size index (heap_left_child index) := by
  have hli : index < heap_left_child index := by unfold heap_left_child; omega
  refine ⟨hi,by omega,hli,by omega,hl,parent_left index hi,?_,?_⟩
  · dsimp only [heap_selected_child]
    split
    · split
      · rfl
      · rcases hs with hs | hs <;> omega
    · rfl
  · intro c hc
    rcases heap_children_characterization__pop_child_selection index c hi hc.1 hc.2.2 with he | he
    · rw [he] <;> omega
    · rw [he] at hc ⊢; rcases hs with hs | hs <;> omega

theorem pop_select_right__pop_child_selection (current : List Int) (size index : Int)
    (hi : 0 ≤ index) (hr : heap_right_child index < size)
    (hs : Znth (heap_right_child index) current 0 < Znth (heap_left_child index) current 0) :
    PopSelectedChild current size index (heap_right_child index) := by
  have hri : index < heap_right_child index := by unfold heap_right_child; omega
  refine ⟨hi,by omega,hri,by omega,hr,parent_right index hi,?_,?_⟩
  · simp only [heap_selected_child,if_pos hr,if_neg (by omega : ¬ Znth (heap_left_child index) current 0 ≤ Znth (heap_right_child index) current 0)]
  · intro c hc
    rcases heap_children_characterization__pop_child_selection index c hi hc.1 hc.2.2 with he | he
    · rw [he] <;> omega
    · rw [he] <;> omega


theorem push_swap_advances_loop__push_sift_up (key_written data_written key_current data_current : List Int)
    (size child parent data_x key_x : Int)
    (hl : PushLoopState key_written data_written key_current data_current size child data_x key_x)
    (hc : 0 < child) (hp : parent = heap_parent child)
    (hlt : Znth parent key_current 0 > Znth child key_current 0) :
    let key_swapped := replace_Znth child (Znth parent key_current 0) (replace_Znth parent (Znth child key_current 0) key_current)
    let data_swapped := replace_Znth child (Znth parent data_current 0) (replace_Znth parent (Znth child data_current 0) data_current)
    Znth child key_swapped 0 = Znth parent key_current 0 ∧
    Znth child data_swapped 0 = Znth parent data_current 0 ∧
    PushLoopState key_written data_written key_swapped data_swapped size parent data_x key_x := by
  rcases hl with ⟨hn,hw,hdw,hlen,hdlen,hc0,hcs,hcx,hdx,hperm,hex,hchildren⟩
  have hb := heap_parent_positive_bounds__push_sift_up child size hc hcs
  rw [← hp] at hb
  let swapped := replace_Znth child (Znth parent key_current 0) (replace_Znth parent (Znth child key_current 0) key_current)
  let dswapped := replace_Znth child (Znth parent data_current 0) (replace_Znth parent (Znth child data_current 0) data_current)
  have hs := Znth_swap_Znth key_current parent child 0 (by omega) (by omega) (by omega)
  have hds := Znth_swap_Znth data_current parent child 0 (by omega) (by omega) (by omega)
  change Znth parent swapped 0 = _ ∧ Znth child swapped 0 = _ ∧ _ at hs
  change Znth parent dswapped 0 = _ ∧ Znth child dswapped 0 = _ ∧ _ at hds
  have hlen' : Zlength swapped = size+1 := by dsimp only [swapped]; rw [Zlength_replace_Znth,Zlength_replace_Znth,hlen]
  have hdlen' : Zlength dswapped = size+1 := by dsimp only [dswapped]; rw [Zlength_replace_Znth,Zlength_replace_Znth,hdlen]
  have hp' : Permutation (pair_list key_written data_written) (pair_list swapped dswapped) :=
    hperm.trans (pair_list_swap_Znth key_current data_current parent child (by omega) (by omega) (by omega))
  refine ⟨hs.2.1,hds.2.1,hn,hw,hdw,hlen',hdlen',hb.1,hb.2.2,hs.1.trans hcx,hds.1.trans hdx,hp',?_,?_⟩
  · refine ⟨hb.1,by omega,?_⟩
    intro node hh
    have hnrange : 0 ≤ node ∧ node < Zlength key_current := by omega
    have hpb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    by_cases hnc : node = child
    · subst node
      rw [← hp,hs.1,hs.2.1] <;> omega
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
    have hpb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    have hnp : node ≠ parent := by omega
    by_cases hp0 : parent = 0
    · have hg : heap_parent parent = parent := by rw [hp0]; rfl
      rw [hg,hs.1]
      by_cases hnc : node = child
      · subst node; rw [hs.2.1] <;> omega
      · rw [hs.2.2 node (by omega) hnp hnc]
        have hold := hex.2.2 node ⟨hh.1,hh.2.1,hnc⟩
        rw [hh.2.2] at hold; omega
    · have hgp := heap_parent_positive_bounds__push_sift_up parent size (by omega) hb.2.2
      rw [hs.2.2 (heap_parent parent) (by omega) (by omega) (by omega)]
      have hparent := hex.2.2 parent ⟨by omega,by omega,by omega⟩
      by_cases hnc : node = child
      · subst node; rw [hs.2.1]; exact hparent
      · rw [hs.2.2 node (by omega) hnp hnc]
        have hold := hex.2.2 node ⟨hh.1,hh.2.1,hnc⟩
        rw [hh.2.2] at hold; omega

theorem pop_root_replacement_pair_remaining_permutation__pop_initialization (before_key before_data : List Int)
    (size : Int) (hs : 1 < size) (hk : Zlength before_key = size) (hd : Zlength before_data = size) :
    Permutation (pair_list (sublist 0 (size-1) (replace_Znth 0 (Znth (size-1) before_key 0) before_key))
      (sublist 0 (size-1) (replace_Znth 0 (Znth (size-1) before_data 0) before_data)))
    (pair_list (sublist 1 size before_key) (sublist 1 size before_data)) := by
  have hk' := Zlength_replace_Znth before_key 0 (Znth (size-1) before_key 0)
  have hd' := Zlength_replace_Znth before_data 0 (Znth (size-1) before_data 0)
  rw [pair_list_sublist _ _ 0 (size-1) (by omega) (by omega) (by omega),
      pair_list_sublist _ _ 1 size (by omega) (by omega) (by omega),
      combine_replace_Znth_both 0 _ _ _ _ (by omega) (by omega)]
  have hlen : Zlength (pair_list before_key before_data) = size := (Zlength_combine_eq _ _ (by omega)).trans hk
  rw [show heap_item (Znth (size-1) before_key 0) (Znth (size-1) before_data 0) =
    Znth (size-1) (pair_list before_key before_data) (0,0) from (Znth_combine_eq (size-1) _ _ 0 0 (by omega) (by omega)).symm]
  exact pop_root_replacement_remaining_permutation__pop_initialization _ size (0,0) hs hlen

theorem pop_root_replacement_loop_state__pop_initialization (before_key before_data : List Int)
    (size : Int) (hs : 1 < size) (hk : Zlength before_key = size) (hd : Zlength before_data = size)
    (ho : heap_ordered before_key size) :
    PopLoopState before_key before_data (replace_Znth 0 (Znth (size-1) before_key 0) before_key)
      (replace_Znth 0 (Znth (size-1) before_data 0) before_data) size 0 := by
  have hklen := (Zlength_replace_Znth before_key 0 (Znth (size-1) before_key 0)).trans hk
  have hdlen := (Zlength_replace_Znth before_data 0 (Znth (size-1) before_data 0)).trans hd
  refine ⟨hs,hk,hd,hklen,hdlen,by omega,by omega,ho,?_,?_,?_,?_,Or.inl rfl⟩
  · exact Znth_replace_Znth_Same 0 before_key 0 _ (by omega)
  · exact Znth_replace_Znth_Same 0 before_data 0 _ (by omega)
  · exact ⟨by omega,by omega,by omega,by omega,by omega,pop_root_replacement_pair_remaining_permutation__pop_initialization _ _ size hs hk hd⟩
  · refine ⟨by omega,by omega,?_⟩
    intro child hc
    have hp := heap_parent_nonnegative_lt__pop_swap_transition child hc.1
    rw [Znth_replace_Znth_Diff 0 before_key 0 (heap_parent child) _ (by omega) (by omega) (Ne.symm hc.2.2),
      Znth_replace_Znth_Diff 0 before_key 0 child _ (by omega) (by omega) (by omega)]
    exact ho child ⟨hc.1,by omega⟩

theorem remove_minimum_singleton_empty__pop_singleton (S : multiset (Int × Int)) (item : Int × Int)
    (hs : multiset_size S = 1) (hm : multiset_minimum S item) : mlist (multiset_remove S item) = [] := by
  have hh := ((multiset_remove_spec S item).1 hm.1).1
  apply List.eq_nil_of_length_eq_zero
  simp only [multiset_size,Zlength,Int.ofNat_eq_coe] at hs hh
  omega

theorem singleton_store_heap_after_remove__pop_singleton (key data : Int) (S : multiset (Int × Int))
    (before_key before_data : List Int) (item : Int × Int)
    (hr : heap_representation S before_key before_data 1) (hm : multiset_minimum S item) :
    intArray.full key 1 before_key ** intArray.undef_seg key 1 heap_capacity **
    intArray.full data 1 before_data ** intArray.undef_seg data 1 heap_capacity |--
    store_heap key data (multiset_remove S item) 0 := by
  rcases hr with ⟨hn,hc,hs,hk,hd,hp,ho⟩
  have hnil := remove_minimum_singleton_empty__pop_singleton S item hs hm
  have hrep : heap_representation (multiset_remove S item) [] [] 0 := by
    refine ⟨by omega,by decide,?_,rfl,rfl,?_,?_⟩
    · change Zlength (mlist (multiset_remove S item)) = 0; rw [hnil]; rfl
    · change (mlist (multiset_remove S item)).Perm []; rw [hnil]
    · intro child hh; omega
  unfold store_heap
  Exists ([] : List Int) ([] : List Int)
  simp only [heap_tail,if_pos (by decide : (0 : Int) < heap_capacity)]
  unfold heap_spare
  generalize hcapacity : heap_capacity = capacity at ⊢
  sep_apply (singleton_full_split_spare__pop_singleton key before_key hk)
  sep_apply (singleton_full_split_spare__pop_singleton data before_data hd)
  simp only [Int.zero_add]
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hrep

theorem pop_comparison_ready__pop_ready_exit (before_key before_data current_key current_data : List Int)
    (size : Int) (item : Int × Int) (index selected : Int)
    (hp : PrefixMinimum before_key before_data size item)
    (hl : PopLoopState before_key before_data current_key current_data size index)
    (hs : PopSelectedChild current_key (size-1) index selected)
    (hd : Znth index current_key 0 ≤ Znth selected current_key 0) :
    PopReadyState before_key before_data current_key current_data size item := by
  rcases hl with ⟨hn,hbk,hbd,hck,hcd,hi,hil,ho,hvk,hvd,hr,he,hchildren⟩
  refine ⟨hn,hbk,hbd,hck,hcd,ho,hp,hr,?_⟩
  intro c hc
  by_cases heq : heap_parent c = index
  · rw [heq]
    exact Int.le_trans hd (hs.2.2.2.2.2.2.2 c ⟨hc.1,hc.2,heq⟩)
  · exact he.2.2 c ⟨hc.1,hc.2,heq⟩

theorem pop_leaf_ready__pop_ready_exit (before_key before_data current_key current_data : List Int)
    (size : Int) (item : Int × Int) (index : Int) (hp : PrefixMinimum before_key before_data size item)
    (hl : PopLoopState before_key before_data current_key current_data size index)
    (hleft : heap_left_child index ≥ size-1) :
    PopReadyState before_key before_data current_key current_data size item := by
  rcases hl with ⟨hn,hbk,hbd,hck,hcd,hi,hil,ho,hvk,hvd,hr,he,hchildren⟩
  refine ⟨hn,hbk,hbd,hck,hcd,ho,hp,hr,?_⟩
  intro c hc
  apply he.2.2 c
  refine ⟨hc.1,hc.2,?_⟩
  intro heq
  rcases heap_children_characterization__pop_child_selection index c hi hc.1 heq with h | h
  · omega
  · unfold heap_left_child heap_right_child at *; omega

theorem build_append_next_cell__build_progress (heap i n : Int) («prefix» input : List Int)
    (hi : 0 ≤ i ∧ i < n) (hp : Zlength «prefix» = i) (hl : n ≤ Zlength input) :
    intArray.full heap i «prefix» ** intArray.seg heap i n (sublist i n input) |--
    intArray.full heap (i+1) («prefix» ++ [Znth i input 0]) ** intArray.seg heap (i+1) n (sublist (i+1) n input) := by
  rw [sublist_split i n (i+1) input (by omega) (by omega),sublist_one input i (by omega),List.singleton_append]
  sep_apply ((intArray.seg_unfold heap i n (sublist (i+1) n input) (Znth i input (0 : Int))).1)
  sep_apply (intArray.seg_single heap i (Znth i input (0 : Int)))
  sep_apply (intArray.full_to_seg heap i «prefix»)
  sep_apply (intArray.seg_merge_to_full heap 0 i (i+1) «prefix» [Znth i input (0 : Int)] (by omega))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem full_retire_last_with_tail__pop_finalization (p size : Int) (values : List Int)
    (hs : 0 < size) (hc : size ≤ heap_capacity) (hl : Zlength values = size) :
    intArray.full p size values ** intArray.undef_seg p size heap_capacity |--
    intArray.full p (size-1) (sublist 0 (size-1) values) ** heap_tail p (size-1) := by
  sep_apply (intArray.full_split_to_seg p (size-1) size values (by omega))
  sep_apply (intArray.seg_to_full p 0 (size-1) (sublist 0 (size-1) values))
  sep_apply (intArray.seg_to_undef_seg p (size-1) size (sublist (size-1) size values))
  rw [heap_tail,if_pos (by omega : size-1 < heap_capacity)]
  unfold heap_spare
  rw [show size-1+1=size by omega]
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem pop_ready_write_result__pop_finalization (S : multiset (Int × Int))
    (before_key before_data current_key current_data : List Int) (size : Int) (item : Int × Int)
    (hr : heap_representation S before_key before_data size) (hm : multiset_minimum S item)
    (hp : PopReadyState before_key before_data current_key current_data size item) :
    PopResult S before_key before_data current_key current_data size item := by
  rcases hr with ⟨hn,hcap,hms,hbk,hbd,hrel,ho⟩
  rcases hp with ⟨hs,_,_,hck,hcd,_,hmin,hrem,horder⟩
  have hsplit := pair_list_cons_split before_key before_data size (by omega) hbk hbd
  rw [← hmin.2.2.2.1] at hsplit
  have hremove := (multiset_remove_spec S item).1 hm.1
  have htail : Permutation (pair_list (sublist 1 size before_key) (sublist 1 size before_data))
      (mlist (multiset_remove S item)) := by
    apply (List.perm_cons item).mp
    rw [← hsplit]
    exact hrel.symm.trans hremove.2
  exact ⟨by omega,hbk,hbd,hck,hcd,heap_ordered_sublist0__pop_finalization current_key (size-1) horder,hrem.2.2.2.2.2.trans htail⟩

theorem pop_result_store_retired_pair__pop_finalization (key data : Int) (S : multiset (Int × Int))
    (before_key before_data result_key result_data : List Int) (size : Int) (item : Int × Int)
    (hc : size ≤ heap_capacity) (h : PopResult S before_key before_data result_key result_data size item) :
    intArray.full key size result_key ** intArray.undef_seg key size heap_capacity **
    intArray.full data size result_data ** intArray.undef_seg data size heap_capacity |--
    store_heap key data (multiset_remove S item) (size-1) := by
  rcases h with ⟨hs,hbk,hbd,hk,hd,ho,hp⟩
  have hkpre := prefix_len result_key (size-1) (by omega)
  have hdpre := prefix_len result_data (size-1) (by omega)
  have hrep : heap_representation (multiset_remove S item) (sublist 0 (size-1) result_key) (sublist 0 (size-1) result_data) (size-1) := by
    refine ⟨by omega,by omega,?_,hkpre,hdpre,hp.symm,ho⟩
    exact (congrArg Int.ofNat hp.symm.length_eq).trans ((Zlength_combine_eq _ _ (by omega)).trans hkpre)
  unfold store_heap
  Exists (sublist 0 (size-1) result_key) (sublist 0 (size-1) result_data)
  sep_apply (full_retire_last_with_tail__pop_finalization key size result_key (by omega) hc hk)
  sep_apply (full_retire_last_with_tail__pop_finalization data size result_data (by omega) hc hd)
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hrep

theorem pop_swap_advances_loop__pop_swap_transition (before_key before_data current_key current_data : List Int)
    (size index selected : Int) (hl : PopLoopState before_key before_data current_key current_data size index)
    (hsel : PopSelectedChild current_key (size-1) index selected)
    (hlt : Znth index current_key 0 > Znth selected current_key 0) :
    let key_swapped := replace_Znth selected (Znth index current_key 0) (replace_Znth index (Znth selected current_key 0) current_key)
    let data_swapped := replace_Znth selected (Znth index current_data 0) (replace_Znth index (Znth selected current_data 0) current_data)
    Znth index current_key 0 = Znth selected key_swapped 0 ∧
    Znth index current_data 0 = Znth selected data_swapped 0 ∧
    PopLoopState before_key before_data key_swapped data_swapped size selected := by
  rcases hl with ⟨hs,hbk,hbd,hc,hd,hi,hidx,ho,hv,hdv,hrem,hex,hhole⟩
  rcases hsel with ⟨_,_,hisel,hsel0,hselb,hparent,hchoice,hdom⟩
  let swapped := replace_Znth selected (Znth index current_key 0) (replace_Znth index (Znth selected current_key 0) current_key)
  let dswapped := replace_Znth selected (Znth index current_data 0) (replace_Znth index (Znth selected current_data 0) current_data)
  have hswap := Znth_swap_Znth current_key index selected 0 (by omega) (by omega) (by omega)
  have hdswap := Znth_swap_Znth current_data index selected 0 (by omega) (by omega) (by omega)
  change Znth index swapped 0 = _ ∧ Znth selected swapped 0 = _ ∧ _ at hswap
  change Znth index dswapped 0 = _ ∧ Znth selected dswapped 0 = _ ∧ _ at hdswap
  have hlen : Zlength swapped = size := by dsimp only [swapped]; rw [Zlength_replace_Znth,Zlength_replace_Znth,hc]
  have hdlen : Zlength dswapped = size := by dsimp only [dswapped]; rw [Zlength_replace_Znth,Zlength_replace_Znth,hd]
  refine ⟨hswap.2.1.symm,hdswap.2.1.symm,hs,hbk,hbd,hlen,hdlen,hsel0,hselb,ho,
    hswap.2.1.trans hv,hdswap.2.1.trans hdv,?_,?_,?_⟩
  · refine ⟨hrem.1,hrem.2.1,hrem.2.2.1,by change size ≤ Zlength swapped; omega,
      by change size ≤ Zlength dswapped; omega,?_⟩
    have hprelen := prefix_len current_key (size-1) (by omega)
    have hdprelen := prefix_len current_data (size-1) (by omega)
    have hp := pair_list_swap_Znth (sublist 0 (size-1) current_key) (sublist 0 (size-1) current_data)
      index selected (by omega) (by omega) (by omega)
    rw [Znth_prefix current_key 0 (size-1) index (by omega),Znth_prefix current_key 0 (size-1) selected (by omega),
      Znth_prefix current_data 0 (size-1) index (by omega),Znth_prefix current_data 0 (size-1) selected (by omega)] at hp
    have hpre (l : List Int) (hll : Zlength l = size) :
        sublist 0 (size-1) (replace_Znth selected (Znth index l 0) (replace_Znth index (Znth selected l 0) l)) =
        replace_Znth selected (Znth index l 0) (replace_Znth index (Znth selected l 0) (sublist 0 (size-1) l)) := by
      rw [sublist0_replace_Znth_inside__pop_swap_transition _ (size-1) selected _ (by omega) (by rw [Zlength_replace_Znth] <;> omega),
        sublist0_replace_Znth_inside__pop_swap_transition l (size-1) index _ (by omega) (by omega)]
    change Permutation (pair_list (sublist 0 (size-1) swapped) (sublist 0 (size-1) dswapped)) _
    dsimp only [swapped,dswapped]
    rw [hpre current_key hc,hpre current_data hd]
    exact hp.symm.trans hrem.2.2.2.2.2
  · refine ⟨hsel0,hselb,?_⟩
    intro child hh
    have hp := heap_parent_nonnegative_lt__pop_swap_transition child hh.1
    by_cases hpi : heap_parent child = index
    · rw [hpi,hswap.1]
      by_cases hcs : child = selected
      · subst child; rw [hswap.2.1] <;> omega
      · rw [hswap.2.2 child (by omega) (by omega) hcs]
        exact hdom child ⟨hh.1,hh.2.1,hpi⟩
    · by_cases hci : child = index
      · subst child
        rw [hswap.2.2 (heap_parent index) (by omega) hpi hh.2.2,hswap.1]
        rcases hhole with hzero | hdom'
        · omega
        · exact hdom' selected ⟨by omega,hselb,hparent⟩
      · have hcs : child ≠ selected := by intro he; subst child; exact hpi hparent
        rw [hswap.2.2 (heap_parent child) (by omega) hpi hh.2.2,
          hswap.2.2 child (by omega) hci hcs]
        exact hex.2.2 child ⟨hh.1,hh.2.1,hpi⟩
  · right
    intro child hh
    have hp := heap_parent_nonnegative_lt__pop_swap_transition child hh.1
    rw [hparent,hswap.1,hswap.2.2 child (by omega) (by omega) (by omega)]
    have hold := hex.2.2 child ⟨hh.1,hh.2.1,by omega⟩
    simpa only [hh.2.2] using hold

end SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue_index
export priority_queue_index_lib (multiset Build_multiset mlist list_to_multiset multiset_size multiset_equiv multiset_insert multiset_remove heap_item item_key item_data pair_list multiset_min multiset_minimum heap_capacity heap_parent heap_left_child heap_right_child heap_selected_child heap_relation heap_ordered heap_representation heap_spare heap_tail store_heap heap_retired_pair KeyWriteState HeapOrderExceptUp PushHoleChildrenPreserved PushSource PushLoopState PushResult BuildPrefixState PrefixMinimum HeapOrderExceptDown PopHoleParentDominatesChildren PopSelectedChild PopRemainingElements PopLoopState PopReadyState PopResult)
end SimpleC.EE.LLM_bench.Data_structures.priority_queue_index
