import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_lib
open AUXLib
export AUXLib.Sorting (increasing_aux increasing lowerbound strict_lowerbound)
export AUXLib.Sorting (insert upperbound_insert_nil upperbound_insert_cons increasing_aux_insert increasing_insert increasing_aux_middle increasing_middle last_val_local last_val_local_in increasing_aux_snoc_local increasing_snoc_local increasing_cons_local replace_Znth_length_local replace_Znth_boundary_local replace_Znth_boundary_app_local perm_insert perm_swap_with_prefix)
def prefix_suffix_sorted (preList suffix : List Int) : Prop :=
  ∀ x, x ∈ preList → lowerbound x suffix

theorem prefix_suffix_sorted_perm_local (l1 l2 l3 : List Int)
    (hs : prefix_suffix_sorted l1 l2) (hp : Permutation l2 l3) :
    prefix_suffix_sorted l1 l3 := by
  intro x hx
  apply Sorting.lowerbound_iff x l3 |>.2
  intro y hy
  exact (Sorting.lowerbound_iff x l2).1 (hs x hx) y (hp.mem_iff.mpr hy)

theorem prefix_suffix_sorted_prefix_perm_local (l1 l2 l3 : List Int)
    (hp : Permutation l1 l2) (hs : prefix_suffix_sorted l1 l3) :
    prefix_suffix_sorted l2 l3 := fun x hx => hs x (hp.mem_iff.mpr hx)

theorem prefix_suffix_sorted_singleton_le_local (l : List Int) (x y : Int)
    (hs : prefix_suffix_sorted l [x]) (hxy : x ≤ y) : prefix_suffix_sorted l [y] := by
  intro z hz
  exact ⟨Int.le_trans (hs z hz).1 hxy, trivial⟩

theorem prefix_suffix_sorted_snoc_singleton_local (l : List Int) (x y : Int)
    (hs : prefix_suffix_sorted l [y]) (hxy : x ≤ y) : prefix_suffix_sorted (l ++ [x]) [y] := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hs z hz
  · have : z = x := List.mem_singleton.mp hz
    subst z
    exact ⟨hxy, trivial⟩

theorem prefix_suffix_sorted_extend_suffix_local (l : List Int) (x : Int) (l2 : List Int)
    (hs : prefix_suffix_sorted l [x]) (hr : prefix_suffix_sorted l l2) :
    prefix_suffix_sorted l (x :: l2) := fun y hy => ⟨(hs y hy).1, hr y hy⟩

theorem prefix_suffix_sorted_last_local (l1 : List Int) (x : Int) (l2 : List Int)
    (hs : prefix_suffix_sorted l1 (x :: l2)) :
    match l1 with | [] => True | y :: l' => last_val_local y l' ≤ x := by
  cases l1 with
  | nil => trivial
  | cons y l => exact (hs _ (last_val_local_in y l)).1

theorem prefix_suffix_sorted_snoc_local (l1 : List Int) (x : Int) (l2 : List Int)
    (hs : prefix_suffix_sorted l1 (x :: l2)) (hb : lowerbound x l2) :
    prefix_suffix_sorted (l1 ++ [x]) l2 := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact (hs y hy).2
  · have : y = x := List.mem_singleton.mp hy
    subst y
    exact hb

end SimpleC.EE.LLM_bench.Algorithms.bubble_sort.bubble_sort_lib
namespace SimpleC.EE.LLM_bench.Algorithms.bubble_sort
export bubble_sort_lib (increasing_aux increasing lowerbound strict_lowerbound prefix_suffix_sorted insert)
end SimpleC.EE.LLM_bench.Algorithms.bubble_sort
