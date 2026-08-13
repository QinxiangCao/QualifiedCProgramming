import AUXLib.ListLib

#check AUXLib.remove_eqdec
#check AUXLib.inb
#check AUXLib.inb_true_iff
#check AUXLib.inb_false_iff
#check AUXLib.In_dec
#check AUXLib.incl_dec
#check AUXLib.NoDup_dec
#check AUXLib.Forall2_split_app1
#check AUXLib.Forall2_split_app2
#check AUXLib.Forall2_merge
#check AUXLib.list_split_nth
#check AUXLib.firstn_skipSn
#check AUXLib.cons_length
#check AUXLib.combine_app
#check AUXLib.forall_in_cons
#check AUXLib.forall_in_app
#check AUXLib.prod_eq_dec
#check AUXLib.list_eq_dec
#check AUXLib.list_eqb
#check AUXLib.list_eqb_eq_nil
#check AUXLib.list_eqb_eq_cons
#check AUXLib.list_eqb_eq
#check AUXLib.list_eqb_refl
#check AUXLib.list_eqb_true
#check AUXLib.option_eqb
#check AUXLib.option_eqb_eq
#check AUXLib.lift_option
#check AUXLib.lift_option_map_some
#check AUXLib.lift_option_cons
#check AUXLib.lift_option_app
#check AUXLib.list_prod_split
#check AUXLib.list_prod_merge
#check AUXLib.incl_cons_iff
#check AUXLib.nperm
#check AUXLib.do_nperm
#check AUXLib.trivial_nperm
#check AUXLib.trivial_nperm_nperm
#check AUXLib.trivial_nperm_refl
#check AUXLib.find_index
#check AUXLib.find_index_nth
#check AUXLib.nth_find_index
#check AUXLib.map_nth_len
#check AUXLib.map_find_index_same
#check AUXLib.do_nperm_length
#check AUXLib.nperm_range
#check AUXLib.nperm_NoDup
#check AUXLib.nperm_map
#check AUXLib.find_index_range
#check AUXLib.inverse_nperm
#check AUXLib.inverse_nperm_nperm
#check AUXLib.inverse_nperm_compose_refl1
#check AUXLib.inverse_nperm_compose_refl2
#check AUXLib.do_nperm_permutation
#check AUXLib.Forall2_nperm_congr0
#check AUXLib.Forall2_nperm_congr
#check AUXLib.swap_nperm
#check AUXLib.swap_nperm_nperm
#check AUXLib.swap_nperm_do_nperm
#check AUXLib.Zlength_nonneg
#check AUXLib.Zlength_app
#check AUXLib.list_swap_nperm
#check AUXLib.list_swap_nperm_nperm
#check AUXLib.list_swap_nperm_do_nperm
#check AUXLib.NoDup_map_fst
#check AUXLib.Zseq
#check AUXLib.Zseq_length
#check AUXLib.Zseq_app
#check AUXLib.nat_list_insert
#check AUXLib.nat_sort
#check AUXLib.nat_list_insert_perm
#check AUXLib.nat_sort_perm
#check AUXLib.nat_sort_nperm
#check AUXLib.list_update_nth
#check AUXLib.list_eq_nth
#check AUXLib.Zseq_nth
#check AUXLib.combine_skipn
#check AUXLib.Zseq_firstn
#check AUXLib.Zseq_skipn
#check AUXLib.factorial
#check AUXLib.factorial_inc
#check AUXLib.zeros
#check AUXLib.sum
#check AUXLib.sum_app
#check AUXLib.sum_bound
#check AUXLib.sum_bound_lt
#check AUXLib.interval_list
#check AUXLib.interval_list_nil
#check AUXLib.interval_list_cons
#check AUXLib.interval_list_valid1
#check AUXLib.interval_list_valid2
#check AUXLib.interval_list_valid3
#check AUXLib.Zlist_max
#check AUXLib.interval_perm_keep
#check AUXLib.increasing
#check AUXLib.increasing_nil
#check AUXLib.increasing_cons
#check AUXLib.list_insert
#check AUXLib.sort
#check AUXLib.list_insert_In
#check AUXLib.sort_list_increasing
#check AUXLib.list_insert_perm
#check AUXLib.sort_list_perm
#check AUXLib.interval_list_compress
#check AUXLib.increasing_interval_list_range
#check AUXLib.interval_list_range
#check AUXLib.Zlength_replace_Znth
#check AUXLib.Zsublist_nil
#check AUXLib.Zsublist_of_nil
#check AUXLib.sublist_self
#check AUXLib.sublist_cons1
#check AUXLib.sublist_cons2
#check AUXLib.firstn_all2
#check AUXLib.repeat_length
#check AUXLib.repeat_app
#check AUXLib.app_Znth2
#check AUXLib.Znth_indep
#check AUXLib.replace_Znth_app_r
#check AUXLib.replace_Znth_nothing
#check AUXLib.sublist_length
#check AUXLib.sublist_app_exact1
#check AUXLib.sublist_single
#check AUXLib.sublist_split
#check AUXLib.sublist_split_app_r
#check AUXLib.Znth_sublist
#check AUXLib.Znth_sublist_lt

open AUXLib

example : remove_eqdec 2 [1, 2, 2, 3] = [1, 3] := by native_decide
example : inb 3 [1, 2, 3] = true := by native_decide
example : inb 4 [1, 2, 3] = false := by native_decide
example : list_eqb (fun x y : Nat => x == y) [1, 2] [1, 2] = true := by native_decide
example : list_eqb (fun x y : Nat => x == y) [1, 2] [1] = false := by native_decide
example : lift_option [some 1, some 2] = some [1, 2] := by native_decide
example : list_prod_merge [1, 2] [3] = none := by native_decide

example : do_nperm (swap_nperm 1 1 1) [10, 20, 30, 40, 50] 0 =
    [10, 40, 30, 20, 50] := by native_decide
example : do_nperm (list_swap_nperm 2 3) [10, 20, 30, 40, 50] 0 =
    [30, 40, 50, 10, 20] := by native_decide

example : Zseq (-2) 5 = [-2, -1, 0, 1, 2] := by native_decide
example (start : Int) (len : Nat) : (Zseq start len).length = len := by
  fail_if_success simp
  exact Zseq_length start len
example (start : Int) (len : Nat) : (Zseq start len).length = len := by
  simp only [Zseq_length]
example : nat_sort [3, 1, 2, 1] = [1, 1, 2, 3] := by native_decide
example : list_update_nth [10, 20] 5 30 = [10, 20, 30] := by native_decide
example : factorial (-4) = 1 := by native_decide
example : factorial 5 = 120 := by native_decide
example : zeros (-3) = [] := by native_decide
example : sum [3, -5, 7] = 5 := by native_decide
example : sort [3, -1, 2, -1] = [-1, -1, 2, 3] := by native_decide
example : replace_Znth (-7) 9 [1, 2, 3] = [9, 2, 3] := by native_decide
example : Zlength (replace_Znth 10 9 [1, 2, 3]) = 3 := by native_decide

example : [10, 20, 30] =
    firstn 0 [10, 20, 30] ++ nth 0 [10, 20, 30] 0 :: skipn 1 [10, 20, 30] :=
  firstn_skipSn 0 0 [10, 20, 30] (by decide)

example : [10, 20, 30] =
    firstn 2 [10, 20, 30] ++ nth 2 [10, 20, 30] 0 :: skipn 3 [10, 20, 30] :=
  firstn_skipSn 0 2 [10, 20, 30] (by decide)

example : [7] = firstn 0 [7] ++ nth 0 [7] 0 :: skipn 1 [7] :=
  firstn_skipSn 0 0 [7] (by decide)

example : sublist (-3) (-2) [1, 2, 3] = [] := by native_decide
example : sublist 3 2 [1, 2, 3, 4] = [] :=
  Zsublist_nil [1, 2, 3, 4] 3 2 (by omega)
example : sublist 4 9 ([] : List Int) = [] := Zsublist_of_nil 4 9
example : sublist 0 (Zlength [1, 2, 3]) [1, 2, 3] = [1, 2, 3] :=
  sublist_self [1, 2, 3] (Zlength [1, 2, 3]) rfl
example : sublist 0 3 [1, 2, 3, 4] = 1 :: sublist 0 2 [2, 3, 4] :=
  sublist_cons1 3 1 [2, 3, 4] (by omega)
example : sublist 1 3 [1, 2, 3, 4] = sublist 0 2 [2, 3, 4] :=
  sublist_cons2 1 3 1 [2, 3, 4] (by omega) (by native_decide)

example : firstn 7 [1, 2, 3] = [1, 2, 3] :=
  firstn_all2 7 [1, 2, 3] (by decide)
example : («repeat» 4 3).length = 3 := repeat_length 4 3
example : «repeat» 4 (2 + 3) = «repeat» 4 2 ++ «repeat» 4 3 :=
  repeat_app 4 2 3
example : Znth 3 ([1, 2] ++ [7, 8, 9]) 0 = Znth 1 [7, 8, 9] 0 :=
  app_Znth2 0 [1, 2] [7, 8, 9] 3 (by native_decide)
example : Znth 1 [5, 6] 0 = Znth 1 [5, 6] 99 :=
  Znth_indep [5, 6] 1 0 99 (by native_decide)
example : replace_Znth 3 8 ([1, 2] ++ [3, 4]) =
    replace_Znth 3 8 [1, 2] ++ replace_Znth 1 8 [3, 4] :=
  replace_Znth_app_r 3 8 [1, 2] [3, 4] (by native_decide)
example : replace_Znth 4 9 [1, 2] = [1, 2] :=
  replace_Znth_nothing 4 [1, 2] 9 (by native_decide)
example : (sublist 1 4 [0, 1, 2, 3, 4]).length = (4 - 1 : Int).toNat :=
  sublist_length 1 4 [0, 1, 2, 3, 4] (by omega) (by native_decide)
example : sublist 0 (Zlength [1, 2]) ([1, 2] ++ [3, 4]) = [1, 2] :=
  sublist_app_exact1 [1, 2] [3, 4]
example : sublist 2 3 [5, 6, 7, 8] = [Znth 2 [5, 6, 7, 8] 0] :=
  sublist_single 0 2 [5, 6, 7, 8] (by native_decide)
example : sublist 1 4 [0, 1, 2, 3, 4] =
    sublist 1 2 [0, 1, 2, 3, 4] ++ sublist 2 4 [0, 1, 2, 3, 4] :=
  sublist_split 1 4 2 [0, 1, 2, 3, 4] (by omega) (by native_decide)
example : sublist 3 5 ([0, 1] ++ [2, 3, 4, 5]) = sublist 1 3 [2, 3, 4, 5] :=
  sublist_split_app_r 3 5 2 [0, 1] [2, 3, 4, 5] (by native_decide) (by omega)
example : Znth 1 (sublist 2 5 [0, 1, 2, 3, 4, 5]) 9 = Znth 3 [0, 1, 2, 3, 4, 5] 9 :=
  Znth_sublist 9 2 1 5 [0, 1, 2, 3, 4, 5] (by omega) (by omega)
example : Znth 1 (sublist 2 5 [0, 1, 2, 3, 4, 5]) 9 = Znth 3 [0, 1, 2, 3, 4, 5] 9 :=
  Znth_sublist_lt 9 2 5 [0, 1, 2, 3, 4, 5] 1 (by omega) (by native_decide) (by omega)

private theorem interval_example : interval_list 1 0 5 [0, 2, 4] := by
  apply interval_list.interval_list_cons
  · apply interval_list.interval_list_cons
    · apply interval_list.interval_list_cons
      · exact .interval_list_nil
      · omega
      · omega
      · exact .nil
    · omega
    · omega
    · exact .cons (by omega) .nil
  · omega
  · omega
  · exact .cons (by omega) (.cons (by omega) .nil)

example : (0 : Int) + Zlength [0, 2, 4] * (1 + 1) <= 5 + 1 + 1 :=
  interval_list_range [0, 2, 4] 1 0 5 (by omega) (by omega) interval_example

example : nperm (swap_nperm 2 3 4) := swap_nperm_nperm 2 3 4
example : nperm (list_swap_nperm 2 3) := list_swap_nperm_nperm 2 3

example : 0 <= Zlength ([1, 2, 3] : List Int) :=
  Zlength_nonneg [1, 2, 3]

example : Zlength ([1, 2] ++ [3, 4] : List Int) =
    Zlength [1, 2] + Zlength [3, 4] :=
  Zlength_app [1, 2] [3, 4]

#print axioms AUXLib.inverse_nperm_compose_refl1
#print axioms AUXLib.sum_bound
#print axioms AUXLib.interval_perm_keep
#print axioms AUXLib.interval_list_range
