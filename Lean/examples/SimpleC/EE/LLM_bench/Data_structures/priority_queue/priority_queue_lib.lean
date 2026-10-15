import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import AUXLib.Arithmetic
import AUXLib.ListLib.LengthCompat
import AUXLib.Morphisms

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib
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
def multiset_empty {A : Type} : multiset A := list_to_multiset []
def multiset_size {A : Type} (S : multiset A) : Int := Zlength (mlist S)
def multiset_equiv {A : Type} (S1 S2 : multiset A) : Prop := Permutation (mlist S1) (mlist S2)
def multiset_insert {A : Type} (S : multiset A) (x : A) : multiset A := list_to_multiset (x :: mlist S)
def multiset_union {A : Type} (S1 S2 : multiset A) : multiset A := list_to_multiset (mlist S1 ++ mlist S2)
def multiset_map {A B : Type} (f : A → B) (S : multiset A) : multiset B := list_to_multiset ((mlist S).map f)
def multiset_member_by {A : Type} (eq_dec : DecidableEq A) (S : multiset A) (x : A) : Bool :=
  (mlist S).any (fun y => @ite Bool (x = y) (eq_dec x y) true false)
def multiset_count_by {A : Type} (eq_dec : DecidableEq A) (S : multiset A) (x : A) : Nat :=
  (mlist S).foldr (fun y n => @ite Nat (y = x) (eq_dec y x) (n + 1) n) 0

noncomputable def multiset_remove {A : Type} (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (remove_one (mlist S))
where
  remove_one : List A → List A
    | [] => []
    | y :: ys => @ite (List A) (x = y) (Classical.propDecidable _) ys (y :: remove_one ys)

theorem mlist_list_to_multiset (A : Type) (l : List A) : mlist (list_to_multiset l) = l := rfl
theorem list_to_multiset_mlist (A : Type) (S : multiset A) : list_to_multiset (mlist S) = S := rfl
theorem multiset_size_from_list (A : Type) (l : List A) : multiset_size (list_to_multiset l) = Zlength l := rfl
theorem multiset_size_empty (A : Type) : multiset_size (multiset_empty (A := A)) = 0 := rfl
theorem multiset_insert_mlist (A : Type) (S : multiset A) (x : A) :
    mlist (multiset_insert S x) = x :: mlist S := rfl
theorem multiset_insert_size (A : Type) (S : multiset A) (x : A) :
    multiset_size (multiset_insert S x) = multiset_size S + 1 := by
  simp [multiset_size, multiset_insert, list_to_multiset, Zlength]
theorem multiset_insert_member (A : Type) (S : multiset A) (x : A) :
    x ∈ mlist (multiset_insert S x) := List.mem_cons_self
theorem multiset_insert_contents (A : Type) (S : multiset A) (x : A) :
    Permutation (mlist (multiset_insert S x)) (x :: mlist S) := List.Perm.refl _
theorem multiset_union_mlist (A : Type) (S1 S2 : multiset A) :
    mlist (multiset_union S1 S2) = mlist S1 ++ mlist S2 := rfl
theorem multiset_union_size (A : Type) (S1 S2 : multiset A) :
    multiset_size (multiset_union S1 S2) = multiset_size S1 + multiset_size S2 := by
  simp [multiset_size, multiset_union, list_to_multiset, Zlength]
instance multiset_equiv_Equivalence (A : Type) : AUXLib.Equivalence (@multiset_equiv A) where
  refl _ := List.Perm.refl _
  symm _ _ h := h.symm
  trans _ _ _ h1 h2 := h1.trans h2

theorem multiset_equiv_size (A : Type) (S1 S2 : multiset A) (h : multiset_equiv S1 S2) :
    multiset_size S1 = multiset_size S2 := congrArg Int.ofNat h.length_eq
theorem multiset_equiv_insert (A : Type) (S1 S2 : multiset A) (x : A) (h : multiset_equiv S1 S2) :
    multiset_equiv (multiset_insert S1 x) (multiset_insert S2 x) := h.cons x
theorem multiset_equiv_union (A : Type) (S1 S1' S2 S2' : multiset A)
    (h1 : multiset_equiv S1 S1') (h2 : multiset_equiv S2 S2') :
    multiset_equiv (multiset_union S1 S2) (multiset_union S1' S2') := h1.append h2
theorem multiset_union_comm (A : Type) (S1 S2 : multiset A) :
    multiset_equiv (multiset_union S1 S2) (multiset_union S2 S1) := List.perm_append_comm
theorem multiset_union_assoc (A : Type) (S1 S2 S3 : multiset A) :
    multiset_equiv (multiset_union (multiset_union S1 S2) S3) (multiset_union S1 (multiset_union S2 S3)) := by
  change ((mlist S1 ++ mlist S2) ++ mlist S3).Perm (mlist S1 ++ (mlist S2 ++ mlist S3))
  rw [List.append_assoc]
theorem multiset_equiv_in (A : Type) (S1 S2 : multiset A) (x : A) (h : multiset_equiv S1 S2) :
    x ∈ mlist S1 ↔ x ∈ mlist S2 := h.mem_iff

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

def multiset_max (S : multiset Int) : Int :=
  match mlist S with
  | [] => 0
  | x :: xs => xs.foldr max x

def multiset_maximum (S : multiset Int) (value : Int) : Prop :=
  value ∈ mlist S ∧ ∀ x, x ∈ mlist S → x ≤ value

theorem fold_right_Zmax_member (xs : List Int) (base : Int) : xs.foldr max base ∈ base :: xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    by_cases h : x ≤ xs.foldr max base
    · rw [Int.max_eq_right h]
      rcases List.mem_cons.mp ih with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem x hm))
    · rw [Int.max_eq_left (by omega)]
      exact List.mem_cons.mpr (Or.inr List.mem_cons_self)

theorem fold_right_Zmax_upper_bound (xs : List Int) (base value : Int)
    (h : value ∈ base :: xs) : value ≤ xs.foldr max base := by
  induction xs with
  | nil =>
    have hh : value = base := by simpa using h
    simp only [List.foldr_nil]; omega
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with he | hm
    · subst value
      exact Int.le_trans (ih List.mem_cons_self) (Int.le_max_right _ _)
    · rcases List.mem_cons.mp hm with he | hm
      · subst value; exact Int.le_max_left _ _
      · exact Int.le_trans (ih (List.mem_cons_of_mem base hm)) (Int.le_max_right _ _)

theorem multiset_max_is_maximum (S : multiset Int) (h : mlist S ≠ []) :
    multiset_maximum S (multiset_max S) := by
  rcases S with ⟨l⟩
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x xs => exact ⟨fold_right_Zmax_member xs x, fun v hv => fold_right_Zmax_upper_bound xs x v hv⟩
theorem multiset_max_member (S : multiset Int) (h : mlist S ≠ []) : multiset_max S ∈ mlist S :=
  (multiset_max_is_maximum S h).1
theorem multiset_max_upper_bound (S : multiset Int) (value : Int) (h : mlist S ≠ [])
    (hm : value ∈ mlist S) : value ≤ multiset_max S := (multiset_max_is_maximum S h).2 value hm

theorem multiset_max_equiv (S1 S2 : multiset Int) (h : multiset_equiv S1 S2) (hne : mlist S1 ≠ []) :
    multiset_max S1 = multiset_max S2 := by
  have hm := multiset_max_member S1 hne
  have hm2 := h.mem_iff.mp hm
  have hne2 : mlist S2 ≠ [] := by intro hn; rw [hn] at hm2; exact List.not_mem_nil hm2
  have hb1 := multiset_max_upper_bound S2 (multiset_max S1) hne2 hm2
  have hb2 := multiset_max_upper_bound S1 (multiset_max S2) hne (h.mem_iff.mpr (multiset_max_member S2 hne2))
  omega

theorem multiset_remove_max_size (S : multiset Int) (h : mlist S ≠ []) :
    multiset_size (multiset_remove S (multiset_max S)) = multiset_size S - 1 :=
  ((multiset_remove_spec S (multiset_max S)).1 (multiset_max_member S h)).1

def heap_capacity : Int := 100000
def heap_parent (child : Int) : Int := Z.quot (child - 1) 2
def heap_left_child (index : Int) : Int := index * 2 + 1
def heap_right_child (index : Int) : Int := index * 2 + 2
def heap_selected_child (concrete : List Int) (size index : Int) : Int :=
  let left := heap_left_child index
  let right := heap_right_child index
  if right < size then
    if Znth left concrete 0 < Znth right concrete 0 then right else left
  else left

def heap_ordered (concrete : List Int) (size : Int) : Prop :=
  ∀ child, (0 < child ∧ child < size) → Znth (heap_parent child) concrete 0 ≥ Znth child concrete 0

def heap_relation (S : multiset Int) (concrete : List Int) : Prop := Permutation (mlist S) concrete

def heap_representation (S : multiset Int) (concrete : List Int) (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ heap_capacity ∧ multiset_size S = size ∧ Zlength concrete = size ∧
    heap_relation S concrete ∧ heap_ordered concrete size

noncomputable def store_heap (p : Int) (S : multiset Int) (size : Int) : Assertion :=
  EX concrete : List Int, “ heap_representation S concrete size ” && intArray.full p size concrete
noncomputable def heap_spare (p size : Int) : Assertion := intArray.undef_seg p size (size + 1)
noncomputable def heap_retired_cell (p index value : Int) : Assertion := intArray.seg p index (index + 1) [value]

theorem heap_relation_size (S : multiset Int) (concrete : List Int) (h : heap_relation S concrete) :
    multiset_size S = Zlength concrete := congrArg Int.ofNat h.length_eq
theorem heap_representation_relation (S : multiset Int) (concrete : List Int) (size : Int)
    (h : heap_representation S concrete size) : heap_relation S concrete := h.2.2.2.2.1
theorem heap_representation_ordered (S : multiset Int) (concrete : List Int) (size : Int)
    (h : heap_representation S concrete size) : heap_ordered concrete size := h.2.2.2.2.2

def PrefixMaximum (concrete : List Int) (size value : Int) : Prop :=
  0 < size ∧ size ≤ Zlength concrete ∧ Znth 0 concrete 0 = value ∧
    ∀ i, (0 ≤ i ∧ i < size) → Znth i concrete 0 ≤ value

def HeapOrderExceptUp (concrete : List Int) (size child : Int) : Prop :=
  0 ≤ child ∧ child < size ∧ ∀ node, (0 < node ∧ node < size ∧ node ≠ child) →
    Znth (heap_parent node) concrete 0 ≥ Znth node concrete 0

def PushHoleChildrenPreserved (concrete : List Int) (size child : Int) : Prop :=
  ∀ node, (0 < node ∧ node < size ∧ heap_parent node = child) →
    Znth (heap_parent child) concrete 0 ≥ Znth node concrete 0

def PushSource (written : List Int) (before : multiset Int) (size x : Int) : Prop :=
  Zlength written = size + 1 ∧ Permutation written (x :: mlist before) ∧
    heap_ordered (sublist 0 size written) size

def PushLoopState (written current : List Int) (size child x : Int) : Prop :=
  0 ≤ size ∧ Zlength written = size + 1 ∧ Zlength current = size + 1 ∧
    0 ≤ child ∧ child ≤ size ∧ Znth child current 0 = x ∧ Permutation written current ∧
    HeapOrderExceptUp current (size + 1) child ∧ PushHoleChildrenPreserved current (size + 1) child

def PushResult (before : multiset Int) (result : List Int) (size x : Int) : Prop :=
  0 ≤ size ∧ Zlength result = size + 1 ∧ Permutation result (x :: mlist before) ∧ heap_ordered result (size + 1)

def BuildPrefixState («prefix» : multiset Int) (input : List Int) (processed : Int) : Prop :=
  1 ≤ processed ∧ processed ≤ Zlength input ∧ multiset_equiv «prefix» (list_to_multiset (sublist 0 processed input))

def HeapOrderExceptDown (concrete : List Int) (size index : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ ∀ child, (0 < child ∧ child < size ∧ heap_parent child ≠ index) →
    Znth (heap_parent child) concrete 0 ≥ Znth child concrete 0

def PopHoleParentDominatesChildren (current : List Int) (size index : Int) : Prop :=
  index = 0 ∨ ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) →
    Znth (heap_parent index) current 0 ≥ Znth child current 0

def PopSelectedChild (current : List Int) (size index selected : Int) : Prop :=
  0 ≤ index ∧ index < size ∧ index < selected ∧ 0 ≤ selected ∧ selected < size ∧
    heap_parent selected = index ∧ selected = heap_selected_child current size index ∧
    ∀ child, (0 < child ∧ child < size ∧ heap_parent child = index) → Znth selected current 0 ≥ Znth child current 0

def PopRemainingElements (before current : List Int) (size : Int) : Prop :=
  1 ≤ size ∧ size ≤ Zlength before ∧ size ≤ Zlength current ∧
    Permutation (sublist 0 (size - 1) current) (sublist 1 size before)

def PopLoopState (before current : List Int) (size index : Int) : Prop :=
  1 < size ∧ Zlength before = size ∧ Zlength current = size ∧ 0 ≤ index ∧ index < size - 1 ∧
    heap_ordered before size ∧ Znth index current 0 = Znth (size - 1) before 0 ∧
    Znth (size - 1) current 0 = Znth (size - 1) before 0 ∧ PopRemainingElements before current size ∧
    HeapOrderExceptDown current (size - 1) index ∧ PopHoleParentDominatesChildren current (size - 1) index

def PopReadyState (before current : List Int) (size result : Int) : Prop :=
  1 < size ∧ Zlength before = size ∧ Zlength current = size ∧ heap_ordered before size ∧
    PrefixMaximum before size result ∧ Znth (size - 1) current 0 = Znth (size - 1) before 0 ∧
    PopRemainingElements before current size ∧ heap_ordered current (size - 1)

def PopResult (S : multiset Int) (before result : List Int) (size value : Int) : Prop :=
  1 ≤ size ∧ Zlength before = size ∧ Zlength result = size ∧ value = multiset_max S ∧
    heap_ordered (sublist 0 (size - 1) result) (size - 1) ∧
    Permutation (sublist 0 (size - 1) result) (mlist (multiset_remove S value))

def HeapSortState (input : List Int) (active : multiset Int) (suffix : List Int) : Prop :=
  Permutation input (mlist active ++ suffix) ∧ Sorting.increasing suffix ∧
    ∀ active_value suffix_value, active_value ∈ mlist active → suffix_value ∈ suffix → active_value ≤ suffix_value

theorem heap_parent_positive_bounds__push_sift_up (child size : Int) (hc : 0 < child) (hs : child ≤ size) :
    0 ≤ heap_parent child ∧ heap_parent child < child ∧ heap_parent child ≤ size := by
  unfold heap_parent Z.quot
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  omega

theorem push_appended_source__push_initialization (S : multiset Int) (base : List Int) (size x : Int)
    (h : heap_representation S base size) : PushSource (base ++ [x]) S size x := by
  rcases h with ⟨hn,hc,hm,hl,hp,ho⟩
  refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega, ?_, ?_⟩
  · exact (hp.symm.append (List.Perm.refl [x])).trans List.perm_append_comm
  · rw [← hl, sublist_app_exact1]; simpa only [hl] using ho

private theorem app_Znth1 (d : Int) (l1 l2 : List Int) (i : Int)
    (h : 0 ≤ i ∧ i < Zlength l1) : Znth i (l1 ++ l2) d = Znth i l1 d := by
  have hn : i.toNat < l1.length := by simp only [Zlength, Int.ofNat_eq_coe] at h; omega
  simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_append_left hn]

theorem push_appended_loop_state__push_initialization (S : multiset Int) (base : List Int) (size x : Int)
    (h : heap_representation S base size) : PushLoopState (base ++ [x]) (base ++ [x]) size size x := by
  rcases h with ⟨hn,hc,hm,hl,hp,ho⟩
  have hlen : Zlength (base ++ [x]) = size+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  refine ⟨hn,hlen,hlen,hn,by omega,?_,List.Perm.refl _,?_,?_⟩
  · rw [app_Znth2 0 base [x] size (by omega), hl]; simp [Znth]
  · refine ⟨hn,by omega,?_⟩
    intro node hh
    have hb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    rw [app_Znth1 0 base [x] (heap_parent node) (by omega), app_Znth1 0 base [x] node (by omega)]
    exact ho node ⟨hh.1,by omega⟩
  · intro node hh
    have hb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    omega

theorem push_break_establishes_result__push_sift_up (before : multiset Int) (written current : List Int)
    (size child parent x : Int) (hs : PushSource written before size x)
    (hl : PushLoopState written current size child x) (hp : parent = heap_parent child)
    (hd : Znth parent current 0 ≥ Znth child current 0) : PushResult before current size x := by
  rcases hs with ⟨_, hsp, _⟩
  rcases hl with ⟨hn,_,hc,_,_,_,hcp,he,_⟩
  refine ⟨hn,hc,hcp.symm.trans hsp,?_⟩
  intro node hh
  by_cases hn : node = child
  · subst node; simpa [hp] using hd
  · exact he.2.2 node ⟨hh.1,hh.2,hn⟩

theorem push_zero_exit_result__push_finalization (before : multiset Int) (written current : List Int)
    (size x : Int) (hs : PushSource written before size x) (hl : PushLoopState written current size 0 x) :
    PushResult before current size x := by
  rcases hs with ⟨_,hsp,_⟩
  rcases hl with ⟨hn,_,hc,_,_,_,hcp,he,_⟩
  exact ⟨hn,hc,hcp.symm.trans hsp,fun node hh => he.2.2 node ⟨hh.1,hh.2,by omega⟩⟩

theorem push_result_representation__push_finalization (before : multiset Int) (result : List Int)
    (size x : Int) (hc : size < heap_capacity) (h : PushResult before result size x) :
    heap_representation (multiset_insert before x) result (size+1) := by
  rcases h with ⟨hn,hl,hp,ho⟩
  refine ⟨by omega,by omega,?_,hl,hp.symm,ho⟩
  exact (heap_relation_size (multiset_insert before x) result hp.symm).trans hl

theorem replace_Znth_swap_form__push_sift_up (l1 l2 l3 : List Int) (xi xj : Int) :
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
    l1 ++ (xj :: (l2 ++ (xi :: l3))) := by
  rw [replace_Znth_boundary_local]
  have he : l1 ++ (xj :: (l2 ++ (xj :: l3))) = (l1 ++ xj :: l2) ++ xj :: l3 := by simp
  rw [he, show Zlength l1 + 1 + Zlength l2 = Zlength (l1 ++ xj :: l2) by simp [Zlength] <;> omega]
  rw [replace_Znth_boundary_local]
  simp

private theorem perm_replace_head (l : List Int) (k : Nat) (x d : Int) (hk : k < l.length) :
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

private theorem permutation_swap_nat (l : List Int) (i j : Nat) (d : Int)
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

theorem permutation_swap_Znth_lt__push_sift_up (l : List Int) (i j d : Int)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  apply permutation_swap_nat
  · omega
  · simp only [Zlength,Int.ofNat_eq_coe] at h; omega

theorem replace_nth_comm_Z__push_sift_up (ni nj : Nat) (l : List Int) (a b : Int) (h : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a := by
  induction l generalizing ni nj with
  | nil => simp [replace_nth]
  | cons x l ih =>
    cases ni <;> cases nj <;> simp_all [replace_nth]

theorem replace_Znth_comm__push_sift_up (l : List Int) (i j a b : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) := by
  apply replace_nth_comm_Z__push_sift_up; omega

theorem permutation_swap_Znth__push_sift_up (l : List Int) (i j d : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  by_cases he : i = j
  · subst j; simp only [replace_Znth_Znth]; exact List.Perm.refl _
  · by_cases hlt : i < j
    · exact permutation_swap_Znth_lt__push_sift_up l i j d ⟨hi.1,hlt,hj.2⟩
    · rw [replace_Znth_comm__push_sift_up l i j _ _ hi.1 hj.1 he]
      exact permutation_swap_Znth_lt__push_sift_up l j i d ⟨hj.1,by omega,hi.2⟩

theorem Znth_swap_Znth__push_sift_up (l : List Int) (i j d : Int)
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

theorem push_swap_advances_loop__push_sift_up (written current : List Int) (size child parent x : Int)
    (hl : PushLoopState written current size child x) (hc : 0 < child) (hp : parent = heap_parent child)
    (hlt : Znth parent current 0 < Znth child current 0) :
    Znth child (replace_Znth child (Znth parent current 0) (replace_Znth parent (Znth child current 0) current)) 0 =
      Znth parent current 0 ∧
    PushLoopState written (replace_Znth child (Znth parent current 0) (replace_Znth parent (Znth child current 0) current)) size parent x := by
  rcases hl with ⟨hn,hw,hlen,hc0,hcs,hcx,hperm,hex,hchildren⟩
  have hb := heap_parent_positive_bounds__push_sift_up child size hc hcs
  rw [← hp] at hb
  let swapped := replace_Znth child (Znth parent current 0) (replace_Znth parent (Znth child current 0) current)
  have hs := Znth_swap_Znth__push_sift_up current parent child 0 (by omega) (by omega) (by omega)
  change Znth parent swapped 0 = _ ∧ Znth child swapped 0 = _ ∧ _ at hs
  have hlen' : Zlength swapped = size+1 := by dsimp only [swapped]; rw [Zlength_replace_Znth,Zlength_replace_Znth,hlen]
  have hp' : Permutation written swapped := hperm.trans (permutation_swap_Znth__push_sift_up current parent child 0 (by omega) (by omega))
  refine ⟨hs.2.1, hn,hw,hlen',hb.1,hb.2.2,hs.1.trans hcx,hp',?_,?_⟩
  · refine ⟨hb.1,by omega,?_⟩
    intro node hh
    have hnrange : 0 ≤ node ∧ node < Zlength current := by omega
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

theorem store_heap_equiv_transport__build_finalization (S1 S2 : multiset Int) (concrete : List Int) (size : Int)
    (hp : multiset_equiv S1 S2) (hr : heap_representation S1 concrete size) :
    heap_representation S2 concrete size := by
  rcases hr with ⟨hn,hc,hs,hl,hp',ho⟩
  exact ⟨hn,hc,(multiset_equiv_size Int S1 S2 hp).symm.trans hs,hl,hp.symm.trans hp',ho⟩

theorem build_prefix_complete__build_finalization («prefix» : multiset Int) (input : List Int) (processed : Int)
    (h : BuildPrefixState «prefix» input processed) (hp : processed = Zlength input) :
    multiset_equiv «prefix» (list_to_multiset input) := by
  rcases h with ⟨_,_,hh⟩
  simpa only [hp,sublist_self] using hh

private theorem sublist_one (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    sublist i (i+1) l = [Znth i l 0] := by
  exact sublist_single 0 i l hi

theorem build_initial_prefix__build_progress (input : List Int) (n : Int)
    (hl : Zlength input = n) (hn : 1 ≤ n) :
    BuildPrefixState (list_to_multiset [Znth 0 input 0]) input 1 ∧
    heap_representation (list_to_multiset [Znth 0 input 0]) (sublist 0 1 input) 1 := by
  have hs := sublist_one input 0 (by omega)
  simp only [Int.zero_add] at hs
  refine ⟨⟨by omega,by omega,?_⟩,by omega,by decide,by rfl,?_,?_,?_⟩
  · rw [hs]; exact List.Perm.refl _
  · rw [hs]; rfl
  · rw [hs]; exact List.Perm.refl _
  · intro child hc; omega

private theorem sublist_prefix_snoc (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    sublist 0 (i+1) l = sublist 0 i l ++ [Znth i l 0] := by
  rw [sublist_split 0 (i+1) i l (by omega) (by omega),sublist_one l i hi]

theorem build_prefix_extend__build_progress («prefix» : multiset Int) (input : List Int) (i x : Int)
    (hi : 1 ≤ i) (hil : i < Zlength input) (hx : x = Znth i input 0)
    (h : BuildPrefixState «prefix» input i) : BuildPrefixState (multiset_insert «prefix» x) input (i+1) := by
  refine ⟨by omega,by omega,?_⟩
  change (x :: mlist «prefix»).Perm (sublist 0 (i+1) input)
  rw [sublist_prefix_snoc input i (by omega),← hx]
  exact (h.2.2.cons x).trans (List.perm_append_singleton x _).symm

theorem heap_ordered_root_upper_bound__pop_initialization (concrete : List Int) (size index : Int)
    (ho : heap_ordered concrete size) (hi : 0 ≤ index ∧ index < size) :
    Znth index concrete 0 ≤ Znth 0 concrete 0 := by
  have h (n : Nat) : ∀ i : Int, i.toNat = n → (0 ≤ i ∧ i < size) → Znth i concrete 0 ≤ Znth 0 concrete 0 := by
    intro i hn hb
    induction n using Nat.strongRecOn generalizing i with
    | ind n ih =>
      by_cases h0 : i = 0
      · subst i; omega
      · have hp := heap_parent_positive_bounds__push_sift_up i size (by omega) (by omega)
        have hr := ih (heap_parent i).toNat (by omega) (heap_parent i) rfl ⟨hp.1,by omega⟩
        exact Int.le_trans (ho i ⟨by omega,hb.2⟩) hr
  exact h index.toNat index rfl hi

private theorem Znth_mem (l : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l 0 ∈ l := by
  have hn : i.toNat < l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

private theorem mem_Znth (l : List Int) (v : Int) (hm : v ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l 0 = v := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩,?_⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using he

theorem heap_root_is_multiset_max__pop_initialization (S : multiset Int) (concrete : List Int) (size : Int)
    (hs : 1 ≤ size) (hr : heap_representation S concrete size) :
    PrefixMaximum concrete size (Znth 0 concrete 0) ∧ Znth 0 concrete 0 = multiset_max S ∧
      multiset_maximum S (Znth 0 concrete 0) := by
  rcases hr with ⟨hn,hc,hms,hl,hp,ho⟩
  have hne : mlist S ≠ [] := by intro he; simp only [multiset_size,he,Zlength_nil] at hms; omega
  have hroot := hp.mem_iff.mpr (Znth_mem concrete 0 (by omega))
  have hmax := multiset_max_is_maximum S hne
  have hb1 := hmax.2 _ hroot
  obtain ⟨i,hi,hiv⟩ := mem_Znth concrete (multiset_max S) (hp.mem_iff.mp hmax.1)
  have hb2 := heap_ordered_root_upper_bound__pop_initialization concrete size i ho (by omega)
  have he : Znth 0 concrete 0 = multiset_max S := by omega
  refine ⟨⟨by omega,by omega,rfl,fun i hi => heap_ordered_root_upper_bound__pop_initialization concrete size i ho hi⟩,he,?_⟩
  rw [he]; exact hmax

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

theorem pop_select_left__pop_child_selection (current : List Int) (size index : Int)
    (hi : 0 ≤ index) (hl : heap_left_child index < size)
    (hs : heap_right_child index ≥ size ∨ Znth (heap_left_child index) current 0 ≥ Znth (heap_right_child index) current 0) :
    PopSelectedChild current size index (heap_left_child index) := by
  have hli : index < heap_left_child index := by unfold heap_left_child; omega
  refine ⟨hi,by omega,hli,by omega,hl,parent_left index hi,?_,?_⟩
  · dsimp only [heap_selected_child]
    split
    · split
      · rcases hs with hs | hs <;> omega
      · rfl
    · rfl
  · intro c hc
    rcases heap_children_characterization__pop_child_selection index c hi hc.1 hc.2.2 with he | he
    · rw [he] <;> omega
    · rw [he] at hc ⊢; rcases hs with hs | hs <;> omega

theorem pop_select_right__pop_child_selection (current : List Int) (size index : Int)
    (hi : 0 ≤ index) (hr : heap_right_child index < size)
    (hs : Znth (heap_left_child index) current 0 < Znth (heap_right_child index) current 0) :
    PopSelectedChild current size index (heap_right_child index) := by
  have hri : index < heap_right_child index := by unfold heap_right_child; omega
  refine ⟨hi,by omega,hri,by omega,hr,parent_right index hi,?_,?_⟩
  · simp only [heap_selected_child,if_pos hr,if_pos hs]
  · intro c hc
    rcases heap_children_characterization__pop_child_selection index c hi hc.1 hc.2.2 with he | he
    · rw [he] <;> omega
    · rw [he] <;> omega

theorem pop_comparison_ready__pop_ready_exit (before current : List Int) (size result index selected : Int)
    (hp : PrefixMaximum before size result) (hl : PopLoopState before current size index)
    (hs : PopSelectedChild current (size-1) index selected)
    (hd : Znth index current 0 ≥ Znth selected current 0) : PopReadyState before current size result := by
  rcases hl with ⟨hn,hb,hc,hi,hil,ho,hv,hvlast,hr,he,hchildren⟩
  refine ⟨hn,hb,hc,ho,hp,hvlast,hr,?_⟩
  intro c hc'
  by_cases heq : heap_parent c = index
  · rw [heq]
    exact Int.le_trans (hs.2.2.2.2.2.2.2 c ⟨hc'.1,hc'.2,heq⟩) hd
  · exact he.2.2 c ⟨hc'.1,hc'.2,heq⟩

theorem pop_leaf_ready__pop_ready_exit (before current : List Int) (size result index : Int)
    (hp : PrefixMaximum before size result) (hl : PopLoopState before current size index)
    (hleft : heap_left_child index ≥ size-1) : PopReadyState before current size result := by
  rcases hl with ⟨hn,hb,hc,hi,hil,ho,hv,hvlast,hr,he,hchildren⟩
  refine ⟨hn,hb,hc,ho,hp,hvlast,hr,?_⟩
  intro c hc'
  apply he.2.2 c
  refine ⟨hc'.1,hc'.2,?_⟩
  intro heq
  rcases heap_children_characterization__pop_child_selection index c hi hc'.1 heq with h | h
  · omega
  · unfold heap_left_child heap_right_child at *; omega

theorem replace_Znth_swap_form__pop_swap_transition (l1 l2 l3 : List Int) (xi xj : Int) :
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
    l1 ++ (xj :: (l2 ++ (xi :: l3))) := replace_Znth_swap_form__push_sift_up l1 l2 l3 xi xj

theorem permutation_swap_Znth_lt__pop_swap_transition (l : List Int) (i j d : Int)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  permutation_swap_Znth_lt__push_sift_up l i j d h

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

theorem pop_root_replacement_remaining_permutation__pop_initialization (before : List Int) (size : Int)
    (hs : 1 < size) (hl : Zlength before = size) :
    Permutation (sublist 0 (size-1) (replace_Znth 0 (Znth (size-1) before 0) before)) (sublist 1 size before) := by
  cases before with
  | nil => simp only [Zlength_nil] at hl; omega
  | cons x l =>
    have hllen : Zlength l = size-1 := by simp only [Zlength_cons] at hl; omega
    change Permutation (sublist 0 (size-1) (Znth (size-1) (x::l) 0 :: l)) (sublist 1 size (x::l))
    rw [Znth_cons 0 (size-1) x l (by omega),sublist_cons1 (size-1) _ l (by omega)]
    have he : sublist 1 size (x::l) = l := by
      unfold sublist
      have hn : size.toNat = l.length+1 := by simp only [Zlength,Int.ofNat_eq_coe] at hllen; omega
      simp [hn]
    rw [he]
    have ht := sublist_prefix_snoc l (size-2) (by omega)
    have he' : sublist 0 (size-2+1) l = l := sublist_self l _ (by omega)
    rw [he'] at ht
    rw [show size-1-1=size-2 by omega]
    exact (List.perm_append_singleton _ _).symm.trans (List.Perm.of_eq ht.symm)

theorem pop_root_replacement_loop_state__pop_initialization (before : List Int) (size : Int)
    (hs : 1 < size) (hl : Zlength before = size) (ho : heap_ordered before size) :
    PopLoopState before (replace_Znth 0 (Znth (size-1) before 0) before) size 0 := by
  have hlen : Zlength (replace_Znth 0 (Znth (size-1) before 0) before) = size := (Zlength_replace_Znth _ _ _).trans hl
  refine ⟨hs,hl,hlen,by omega,by omega,ho,?_,?_,?_,?_,Or.inl rfl⟩
  · exact Znth_replace_Znth_Same 0 before 0 _ (by omega)
  · exact Znth_replace_Znth_Diff 0 before 0 (size-1) _ (by omega) (by omega) (by omega)
  · exact ⟨by omega,by omega,by omega,pop_root_replacement_remaining_permutation__pop_initialization before size hs hl⟩
  · refine ⟨by omega,by omega,?_⟩
    intro child hc
    have hp := heap_parent_nonnegative_lt__pop_swap_transition child hc.1
    rw [Znth_replace_Znth_Diff 0 before 0 (heap_parent child) _ (by omega) (by omega) (Ne.symm hc.2.2),
      Znth_replace_Znth_Diff 0 before 0 child _ (by omega) (by omega) (by omega)]
    exact ho child ⟨hc.1,by omega⟩

theorem remove_max_singleton_empty__pop_singleton (S : multiset Int) (hs : multiset_size S = 1) :
    mlist (multiset_remove S (multiset_max S)) = [] := by
  have hne : mlist S ≠ [] := by intro he; simp only [multiset_size,he,Zlength_nil] at hs; omega
  have hsize := multiset_remove_max_size S hne
  have hz : Zlength (mlist (multiset_remove S (multiset_max S))) = 0 := by change multiset_size _ = 0; omega
  apply List.eq_nil_of_length_eq_zero
  simp only [Zlength,Int.ofNat_eq_coe] at hz; omega

private theorem head_tail_sublist (l : List Int) (size value : Int) (hs : 0 < size)
    (hl : Zlength l = size) (hv : Znth 0 l 0 = value) : l = value :: sublist 1 size l := by
  have h := sublist_split 0 size 1 l (by omega) (by omega)
  rw [sublist_self l size hl.symm,show sublist 0 1 l = [Znth 0 l 0] from sublist_one l 0 (by omega),hv] at h
  exact h

theorem pop_ready_write_result__pop_finalization (S : multiset Int) (before current : List Int) (size value : Int)
    (hv : value = multiset_max S) (hr : heap_representation S before size)
    (hp : PopReadyState before current size value) : PopResult S before current size value := by
  rcases hr with ⟨hn,hcap,hms,hb,hrel,ho⟩
  rcases hp with ⟨hs,_,hc,_,hmax,hlast,hrem,horder⟩
  have hsplit := head_tail_sublist before size value (by omega) hb hmax.2.2.1
  have hmember : value ∈ mlist S := hrel.mem_iff.mpr (by rw [hsplit]; exact List.mem_cons_self)
  have hremove := (multiset_remove_spec S value).1 hmember
  have htail : Permutation (sublist 1 size before) (mlist (multiset_remove S value)) := by
    apply (List.perm_cons value).mp
    rw [← hsplit]
    exact hrel.symm.trans hremove.2
  exact ⟨by omega,hb,hc,hv,heap_ordered_sublist0__pop_finalization current (size-1) horder,hrem.2.2.2.trans htail⟩

theorem heap_sort_initial_state__heap_sort_setup (input : List Int) :
    HeapSortState input (list_to_multiset input) [] := by
  refine ⟨?_,True.intro,?_⟩
  · simp only [list_to_multiset,mlist,List.append_nil]; exact List.Perm.refl _
  · intro _ _ _ h; exact False.elim (List.not_mem_nil h)

theorem heap_sort_extract_step__heap_sort_transition (input : List Int) (active : multiset Int) (suffix : List Int)
    (extracted : Int) (he : extracted = multiset_max active) (hm : multiset_maximum active extracted)
    (hs : HeapSortState input active suffix) :
    multiset_size (multiset_remove active (multiset_max active)) = multiset_size active-1 ∧
    HeapSortState input (multiset_remove active (multiset_max active)) (extracted::suffix) := by
  rw [← he]
  rcases hs with ⟨hp,ho,hcross⟩
  have hr := (multiset_remove_spec active extracted).1 hm.1
  refine ⟨hr.1,?_,?_,?_⟩
  · exact hp.trans ((hr.2.append_right suffix).trans List.perm_middle.symm)
  · exact increasing_cons_local extracted suffix ((lowerbound_iff extracted suffix).mpr (fun v hv => hcross _ _ hm.1 hv)) ho
  · intro a b ha hb
    have ha' := hr.2.mem_iff.mpr (List.mem_cons_of_mem extracted ha)
    rcases List.mem_cons.mp hb with hb | hb
    · subst b; exact hm.2 a ha'
    · exact hcross a b ha' hb

theorem heap_sort_empty_state_output__heap_sort_finalization (input : List Int) (active : multiset Int)
    (suffix : List Int) (hn : multiset_size active = 0) (hs : HeapSortState input active suffix) :
    mlist active = [] ∧ Permutation input suffix ∧ Sorting.increasing suffix := by
  have hnil : mlist active = [] := by apply List.eq_nil_of_length_eq_zero; simp only [multiset_size,Zlength,Int.ofNat_eq_coe] at hn; omega
  refine ⟨hnil,?_,hs.2.1⟩
  simpa only [hnil,List.nil_append] using hs.1

theorem build_split_next_cell__build_progress (heap i n : Int) (input : List Int)
    (hi : 0 ≤ i ∧ i < n) (hl : n ≤ Zlength input) :
    intArray.seg heap i n (sublist i n input) |-- heap_spare heap i ** intArray.seg heap (i+1) n (sublist (i+1) n input) := by
  unfold heap_spare
  rw [sublist_split i n (i+1) input (by omega) (by omega),sublist_one input i (by omega),List.singleton_append]
  sep_apply ((intArray.seg_unfold heap i n (sublist (i+1) n input) (Znth i input (0 : Int))).1)
  sep_apply (intArray.seg_single heap i (Znth i input (0 : Int)))
  sep_apply (intArray.seg_to_undef_seg heap i (i+1) [Znth i input (0 : Int)])
  cancel

theorem singleton_full_split_retired__pop_singleton (p : Int) (before : List Int) (value : Int)
    (hl : Zlength before = 1) (hv : Znth 0 before 0 = value) :
    intArray.full p 1 before |-- intArray.full p 0 [] ** heap_spare p 0 := by
  unfold heap_spare
  sep_apply (intArray.full_split_to_seg p 0 1 before (by omega))
  rw [Zsublist_nil before 0 0 (by omega)]
  sep_apply (intArray.seg_to_full p 0 0 [])
  sep_apply (intArray.seg_to_undef_seg p 0 1 (sublist 0 1 before))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero,Int.zero_add]
  cancel

theorem pop_result_store_retired__pop_finalization (p : Int) (S : multiset Int) (before result : List Int)
    (size value : Int) (hcap : size ≤ heap_capacity) (h : PopResult S before result size value) :
    intArray.full p size result |-- store_heap p (multiset_remove S value) (size-1) ** intArray.undef_seg p (size-1) size := by
  rcases h with ⟨hs,hb,hr,hv,ho,hperm⟩
  have hp : Zlength (sublist 0 (size-1) result) = size-1 := prefix_len result (size-1) (by omega)
  have hrep : heap_representation (multiset_remove S value) (sublist 0 (size-1) result) (size-1) :=
    ⟨by omega,by omega,(heap_relation_size _ _ hperm.symm).trans hp,hp,hperm.symm,ho⟩
  unfold store_heap
  Exists (sublist 0 (size-1) result)
  sep_apply (intArray.full_split_to_seg p (size-1) size result (by omega))
  sep_apply (intArray.seg_to_full p 0 (size-1) (sublist 0 (size-1) result))
  sep_apply (intArray.seg_to_undef_seg p (size-1) size (sublist (size-1) size result))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hrep

theorem heap_sort_spare_is_write_slot__heap_sort_write (p i : Int) :
    heap_spare p (i-1) |-- intArray.undef_seg p (i-1) i := by
  unfold heap_spare
  rw [show i-1+1=i by omega]
  cancel

theorem heap_sort_written_slot_split__heap_sort_write (p i n extracted : Int) (suffix : List Int)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    intArray.seg p (i-1) n (extracted::suffix) |--
      heap_retired_cell p (i-1) extracted ** intArray.seg p i n suffix := by
  unfold heap_retired_cell
  sep_apply ((intArray.seg_unfold p (i-1) n suffix extracted).1)
  sep_apply (intArray.seg_single p (i-1) extracted)
  rw [show i-1+1=i by omega]
  cancel

theorem heap_sort_zero_store_join__heap_sort_finalization (p n : Int) (active : multiset Int) (suffix : List Int)
    (hn : 0 ≤ n) : store_heap p active 0 ** intArray.seg p 0 n suffix |-- intArray.full p n suffix := by
  unfold store_heap
  Intros concrete
  have hr : heap_representation active concrete 0 := by assumption
  have hc : concrete = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hh := hr.2.2.2.1
    simp only [Zlength,Int.ofNat_eq_coe] at hh
    omega
  subst concrete
  sep_apply (intArray.full_to_seg p 0 [])
  sep_apply (intArray.seg_merge_to_full p 0 0 n [] suffix (by omega))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero,List.nil_append]
  cancel

theorem pop_swap_advances_loop__pop_swap_transition (before current : List Int) (size index selected : Int)
    (hl : PopLoopState before current size index) (hsel : PopSelectedChild current (size-1) index selected)
    (hlt : Znth index current 0 < Znth selected current 0) :
    PopLoopState before
      (replace_Znth selected (Znth index current 0) (replace_Znth index (Znth selected current 0) current)) size selected := by
  rcases hl with ⟨hs,hb,hc,hi,hidx,ho,hv,hlast,hrem,hex,hhole⟩
  rcases hsel with ⟨_,_,hisel,hsel0,hselb,hparent,hchoice,hdom⟩
  let swapped := replace_Znth selected (Znth index current 0) (replace_Znth index (Znth selected current 0) current)
  have hswap := Znth_swap_Znth__push_sift_up current index selected 0 (by omega) (by omega) (by omega)
  change Znth index swapped 0 = _ ∧ Znth selected swapped 0 = _ ∧ _ at hswap
  have hlen : Zlength swapped = size := by
    dsimp only [swapped]; rw [Zlength_replace_Znth,Zlength_replace_Znth,hc]
  refine ⟨hs,hb,hlen,hsel0,hselb,ho,hswap.2.1.trans hv,?_,?_,?_,?_⟩
  · rw [hswap.2.2 (size-1) (by omega) (by omega) (by omega)]; exact hlast
  · refine ⟨hrem.1,hrem.2.1,by change size ≤ Zlength swapped; omega,?_⟩
    have hprelen := prefix_len current (size-1) (by omega)
    have hp := permutation_swap_Znth__push_sift_up (sublist 0 (size-1) current) index selected 0 (by omega) (by omega)
    rw [Znth_prefix current 0 (size-1) index (by omega),Znth_prefix current 0 (size-1) selected (by omega)] at hp
    have hpre : sublist 0 (size-1) swapped =
        replace_Znth selected (Znth index current 0) (replace_Znth index (Znth selected current 0) (sublist 0 (size-1) current)) := by
      dsimp only [swapped]
      rw [sublist0_replace_Znth_inside__pop_swap_transition _ (size-1) selected _ (by omega) (by rw [Zlength_replace_Znth] <;> omega),
        sublist0_replace_Znth_inside__pop_swap_transition current (size-1) index _ (by omega) (by omega)]
    rw [hpre]
    exact hp.symm.trans hrem.2.2.2
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

end SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib
namespace SimpleC.EE.LLM_bench.Data_structures.priority_queue
export priority_queue_lib (multiset Build_multiset mlist list_to_multiset multiset_empty multiset_size multiset_equiv
  multiset_insert multiset_union multiset_map multiset_member_by multiset_count_by multiset_remove
  multiset_max multiset_maximum heap_capacity heap_parent heap_left_child heap_right_child heap_selected_child
  heap_ordered heap_relation heap_representation store_heap heap_spare heap_retired_cell PrefixMaximum
  HeapOrderExceptUp PushHoleChildrenPreserved PushSource PushLoopState PushResult BuildPrefixState
  HeapOrderExceptDown PopHoleParentDominatesChildren PopSelectedChild PopRemainingElements PopLoopState
  PopReadyState PopResult HeapSortState)
export AUXLib.Sorting (increasing)
end SimpleC.EE.LLM_bench.Data_structures.priority_queue
