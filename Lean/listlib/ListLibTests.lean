import ListLib
import Std.Tactic

namespace ListLibTests

open ListLib

#check ListLib.list_snoc_destruct
#check ListLib.app_eq_app

#check ListLib.Znth
#check ListLib.Znth_error
#check ListLib.tl_error
#check ListLib.nth
#check ListLib.firstn
#check ListLib.skipn
#check ListLib.In
#check ListLib.incl
#check ListLib.NoDup
#check ListLib.Permutation
#check ListLib.Forall
#check ListLib.Forall2
#check ListLib.replace_nth
#check ListLib.replace_Znth
#check ListLib.Nsublist
#check ListLib.sublist
#check ListLib.Zlength
#check ListLib.Znth0_cons
#check ListLib.Znth_cons
#check ListLib.Znth_error_cons_0
#check ListLib.Znth_error_cons
#check ListLib.Znth_repeat
#check ListLib.Znth_repeat_lt
#check ListLib.replace_Znth_cons
#check ListLib.replace_Znth_Znth
#check ListLib.Znth_replace_Znth_Same
#check ListLib.Znth_replace_Znth_Diff
#check ListLib.Zsublist_nil
#check ListLib.Zsublist_of_nil
#check ListLib.Zsublist_Zsublist
#check ListLib.Zsublist_Zsublist0
#check ListLib.Zsublist_Zsublist00
#check ListLib.nth_firstn
#check (ListLib.nth_firstn :
  ∀ {A : Type} (l : List A) (n m : Nat) (d : A),
    n < m → ListLib.nth n (ListLib.firstn m l) d = ListLib.nth n l d)
#check ListLib.firstn_skipSn
#check ListLib.length_sublist
#check ListLib.length_sublist'
#check ListLib.nth_sublist
#check ListLib.tl_error_last
#check ListLib.tl_error_app_skipn_connected

#check ListLib.Zlength_nonneg
#check ListLib.Zlength_correct
#check ListLib.Zlength_nil
#check ListLib.Zlength_cons
#check ListLib.Zlength_app
#check ListLib.Zlength_app_cons
#check ListLib.app_Znth1
#check ListLib.app_Znth2
#check ListLib.Znth_indep
#check ListLib.replace_nth_app_l
#check ListLib.replace_nth_app_r
#check ListLib.replace_Znth_app_l
#check ListLib.replace_Znth_app_r
#check ListLib.replace_Znth_nothing
#check ListLib.Znth_error_range
#check ListLib.Znth_error_Some_cons
#check ListLib.sublist_length
#check ListLib.sublist_app_exact1
#check ListLib.sublist_split_app_l
#check ListLib.sublist_single
#check ListLib.sublist_split
#check ListLib.Zlength_sublist
#check ListLib.Zlength_sublist0
#check ListLib.sublist_self
#check ListLib.Zlength_sublist'
#check ListLib.sublist_split_app_r
#check ListLib.sublist_cons1
#check ListLib.sublist_cons2
#check ListLib.Znth_sublist
#check ListLib.Znth_sublist0
#check ListLib.Znth_sublist_lt
#check ListLib.Znth_sublist_ge
#check ListLib.list_eq_ext
#check ListLib.length_nonnil
#check ListLib.sublist_nil
#check ListLib.Nsublist_single
#check ListLib.sublist_one_ele
#check ListLib.sublist_one_ele'
#check ListLib.sublist_single'
#check ListLib.Nsublist_self
#check ListLib.Nsublist_split_app_l
#check ListLib.Nsublist_split_app_r
#check ListLib.Nsublist_split
#check ListLib.Zsublist_one_ele

#check ListLib.Forall2_split
#check ListLib.Forall2_congr
#check ListLib.Forall2_cons_nil_l
#check ListLib.Forall2_cons_nil_inv_l
#check ListLib.Forall2_cons_inv_l
#check ListLib.Forall2_cons_nil_r
#check ListLib.Forall2_cons_nil_inv_r
#check ListLib.Forall2_cons_inv_r
#check ListLib.Forall2_nth_iff
#check ListLib.Forall2_map1
#check ListLib.Forall2_map2
#check ListLib.Forall2_and
#check ListLib.Forall2_and_inv
#check ListLib.Forall2_and_Forall_l
#check ListLib.Forall2_and_Forall_r
#check ListLib.Forall_in_cons

#check ListLib.Nodup_exists_repetition
#check ListLib.Nodup_split_constructors
#check ListLib.Nodup_app_comm
#check ListLib.Nodup_all_sublists

#check ListLib.is_prefix
#check ListLib.is_suffix
#check ListLib.is_sublist
#check ListLib.presuffix
#check ListLib.partial_match_res
#check ListLib.partial_bound_res
#check ListLib.proper_presuffix
#check ListLib.presuffix_bound
#check ListLib.max_proper_presuffix
#check ListLib.prefix_ind_iff_positional
#check ListLib.suffix_ind_iff_positional
#check ListLib.sublist_ind_iff_positional
#check ListLib.prefix_snoc
#check ListLib.sublist_snor
#check ListLib.prefix_of_nil_inv
#check ListLib.sublist_of_nil_inv
#check ListLib.is_suffix_snoc_snoc_iff
#check ListLib.prefix_length
#check ListLib.suffix_length
#check ListLib.presuffix_length
#check ListLib.prefix_iff
#check ListLib.prefix_iff'
#check ListLib.suffix_iff
#check ListLib.suffix_iff'
#check ListLib.is_prefix_snoc_iff
#check ListLib.prefix_trans
#check ListLib.suffix_trans
#check ListLib.presuffix_trans
#check ListLib.prefix_total_order
#check ListLib.suffix_total_order
#check ListLib.partial_match_total_order
#check ListLib.partial_match_iff
#check ListLib.partial_match_snoc_iff
#check ListLib.prefix_iff_sublist
#check ListLib.suffix_iff_sublist
#check ListLib.nil_prefix
#check ListLib.nil_suffix
#check ListLib.nil_presuffix
#check ListLib.presuffix_nil_iff
#check ListLib.partial_match_nil
#check ListLib.presuffix_partial_match
#check ListLib.prefix_app_iff
#check ListLib.suffix_app_iff
#check ListLib.prefix_sublist_iff
#check ListLib.suffix_sublist_cons_iff

#check ListLib.is_indexed_elements
#check ListLib.is_indexed_elements_nil
#check ListLib.is_indexed_elements_cons
#check ListLib.is_indexed_elements_cons_iff
#check ListLib.is_indexed_elements_app
#check ListLib.is_indexed_elements_app_inv_r
#check ListLib.is_indexed_elements_app_inv_l
#check ListLib.is_indexed_elements_nil_inv_l
#check ListLib.is_indexed_elements_nil_inv_r
#check ListLib.is_indexed_elements_cons_inv_r
#check ListLib.is_indexed_elements_cons_inv_l
#check ListLib.sincr_aux
#check ListLib.sincr
#check ListLib.sincr_app_cons
#check ListLib.sincr_app_cons_inv1
#check ListLib.sincr_app_cons_inv2
#check ListLib.is_subsequence
#check ListLib.sincr_add_1
#check ListLib.sincr_sub_1
#check ListLib.sincr_cons
#check ListLib.sincr_cons_tail_Forall_lt
#check ListLib.sincr_cons_Forall_lt
#check ListLib.is_indexed_elements_range
#check ListLib.is_subsequence_inv
#check ListLib.is_subsequence_spec

example : ListLib.replace_nth 1 ([1, 2, 3] : List Int) 9 = [1, 9, 3] := rfl

example : ListLib.replace_nth 9 ([1, 2, 3] : List Int) 7 = [1, 2, 3] := rfl

example : ListLib.Nsublist 1 3 ([10, 20, 30, 40] : List Int) = [20, 30] := rfl

example : ListLib.sublist 1 3 ([10, 20, 30, 40] : List Int) = [20, 30] := rfl

example : ListLib.sublist (-2) 2 ([10, 20, 30] : List Int) = [10, 20] := rfl

example : ListLib.Znth_error ([10, 20, 30] : List Int) 1 = some 20 := rfl

example : ListLib.Znth_error ([10, 20, 30] : List Int) (-1) = none := rfl

example : ([1, 2] : List Int) is_a_prefix_of [1, 2, 3] := by
  exact ⟨[3], rfl⟩

example : ([2, 3] : List Int) is_a_suffix_of [1, 2, 3] := by
  exact ⟨[1], rfl⟩

example : ([2] : List Int) is_a_sublist_of [1, 2, 3] := by
  exact ⟨[1], [3], rfl⟩

example : ListLib.presuffix ([] : List Int) [1, 2, 3] := by
  exact ListLib.nil_presuffix [1, 2, 3]

example :
    ListLib.partial_match_res ([1, 2, 3] : List Int) [0, 1, 2] [1, 2] := by
  exact ⟨⟨[0], rfl⟩, ⟨[3], rfl⟩⟩

example : ListLib.sincr ([1, 3, 5] : List Int) := by
  simp [ListLib.sincr, ListLib.sincr_aux]

example : Not (ListLib.sincr ([1, 1] : List Int)) := by
  intro h
  simp [ListLib.sincr, ListLib.sincr_aux] at h

example :
    ListLib.is_indexed_elements ([1, 2, 3, 4] : List Int) [1, 3] [2, 4] := by
  unfold ListLib.is_indexed_elements
  constructor
  · rfl
  · constructor
    · rfl
    · constructor

example : ListLib.is_subsequence ([2, 4] : List Int) [1, 2, 3, 4] := by
  apply ListLib.is_subsequence_spec ([2, 4] : List Int) [1, 2, 3, 4] [1, 3]
  · simp [ListLib.sincr, ListLib.sincr_aux]
  · unfold ListLib.is_indexed_elements
    constructor
    · rfl
    · constructor
      · rfl
      · constructor

example :
    exists il, ListLib.sincr il /\
      ListLib.is_indexed_elements ([1, 2, 3, 4] : List Int) il [2, 4] := by
  apply ListLib.is_subsequence_inv
  change ListLib.is_subsequence ([2, 4] : List Int) [1, 2, 3, 4]
  simp [ListLib.is_subsequence]

#print axioms ListLib.prefix_iff
#print axioms ListLib.is_subsequence_spec

end ListLibTests
