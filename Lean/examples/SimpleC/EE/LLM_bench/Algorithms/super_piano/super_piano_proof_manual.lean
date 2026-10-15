import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_goal
import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open super_piano_goal super_piano_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem annotation_nth_bounds (l : List Int)
    (hl : Forall (fun z => -1000 ≤ z) l) (hu : Forall (fun z => z ≤ 1000) l) :
    ∀ k, 0 ≤ k ∧ k < Zlength l → -1000 ≤ Znth k l 0 ∧ Znth k l 0 ≤ 1000 := by
  intro k hk
  have hi : k.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hk; omega
  have hm := List.getElem_mem (l := l) hi
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    using And.intro (hl.mem hm) (hu.mem hm)

private theorem list_eq_map_from_nth {A B : Type} (da : A) (db : B)
    (xs : List A) (ys : List B) (f : B → A)
    (hlen : Zlength xs = Zlength ys)
    (h : ∀ i, 0 ≤ i ∧ i < Zlength ys → Znth i xs da = f (Znth i ys db)) :
    xs = ys.map f := by
  have hlen' : xs.length = ys.length := by
    simpa only [Zlength, Int.ofNat_eq_coe, Int.natCast_inj] using hlen
  apply List.ext_getElem (by simp only [List.length_map]; exact hlen')
  intro i hi hj
  have hy : i < ys.length := by omega
  have he := h (i : Int) ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hy, Option.getD_some,
    List.getElem_map] using he

private theorem piano_nodes_of_arrays (slots : List Node) (vals starts los his bests : List Int)
    (h : NodeArrays slots vals starts los his bests) :
    PianoNodes vals starts los his bests = slots := by
  have hv := list_eq_map_from_nth 0 default_node vals slots node_value h.1 (fun i hi => (h.2.2.2.2.2 i hi).1)
  have hs := list_eq_map_from_nth 0 default_node starts slots node_start h.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.1)
  have hl := list_eq_map_from_nth 0 default_node los slots node_lo h.2.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.2.1)
  have hh := list_eq_map_from_nth 0 default_node his slots node_hi h.2.2.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.2.2.1)
  have hb := list_eq_map_from_nth 0 default_node bests slots node_best h.2.2.2.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.2.2.2)
  rw [hv, hs, hl, hh, hb]
  clear h hv hs hl hh hb
  induction slots with
  | nil => rfl
  | cons nd rest ih =>
    rcases nd with ⟨⟨⟨⟨v,s⟩,l⟩,h⟩,b⟩
    simpa only [PianoNodes, List.map_cons, List.zip_cons_cons, mkNode,
      node_value, node_start, node_lo, node_hi, node_best, List.cons.injEq, true_and]
      using ih


private theorem cell_to_seg (p i value : Int) :
    ((p+i*sizeof(INT)) # Int |-> value) |-- intArray.seg p i (i+1) [value] := by
  exact intArray.seg_single p i value

private theorem prefix_step (l pref : List Int) (i : Int) (hp : PrefixArrayPrefix l pref i) (hi : i < Zlength l) :
    PrefixArrayPrefix l (pref ++ [Znth i pref 0+Znth i l 0]) (i+1) := by
  obtain ⟨hi0,hil,hlen,hzero,hstep⟩ := hp
  have hget : ∀ j, 0 ≤ j ∧ j < Zlength pref →
      Znth j (pref ++ [Znth i pref 0+Znth i l 0]) 0 = Znth j pref 0 := by
    intro j hj
    exact ListLib.app_Znth1 0 pref _ j hj
  refine ⟨by omega,by omega,?_,?_,?_⟩
  · rw [Zlength_app,Zlength_cons,Zlength_nil,hlen]; omega
  · rw [hget 0 ⟨le_refl _,by omega⟩,hzero]
  · intro j hj
    by_cases he : j < i
    · rw [hget (j+1) ⟨by omega,by omega⟩,hget j ⟨by omega,by omega⟩]
      exact hstep j ⟨hj.1,he⟩
    · have heq : j = i := by omega
      subst j
      rw [app_Znth2 0 pref _ (i+1) (by omega),hlen]
      simp only [Int.sub_self,Znth0_cons]
      rw [hget i ⟨hi0,by omega⟩]


theorem proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6 := by
  unfold build_prefix_safety_wit_6
  left
  intro pre_pre n_pre arr_pre l pref i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH1 : (i < n_pre) := NewPreH1
  have PreH5 : ((0 : Int) <= i) := NewPreH5
  have PreH7 : (PrefixArrayPrefix l pref i) := NewPreH7
  have PreH8 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) := by
    intro k hk
    exact annotation_bounds k (by omega)
  have hp := PrefixArrayPrefix_entry_abs_bound l pref i i PreH7 (fun idx hh => PreH8 idx ⟨hh.1,by omega⟩) ⟨PreH5,le_refl _⟩
  have hl := PreH8 i ⟨PreH5,PreH1⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega


theorem proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1 := by
  unfold build_prefix_entail_wit_1
  left
  intro pre_pre n_pre arr_pre l ps NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) [0] ?_
  split_pure_spatial
  · sep_apply (cell_to_seg pre_pre 0 0)
    simp only [Int.zero_add]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | rfl
    | (refine ⟨by omega,by omega,rfl,rfl,?_⟩; intro j hj; omega)


theorem proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1 := by
  unfold build_prefix_return_wit_1
  left
  intro pre_pre n_pre arr_pre l pref i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH4 : ((Zlength (l)) = n_pre) := NewPreH4
  have PreH7 : (PrefixArrayPrefix l pref i) := NewPreH7
  have PreH8 : forall (idx_2 : Int) , ((((0 : Int) <= idx_2) ∧ (idx_2 < n_pre)) -> (((-1000) <= (Znth idx_2 l (0 : Int))) ∧ ((Znth idx_2 l (0 : Int)) <= 1000))) := by
    intro k hk
    exact annotation_bounds k (by omega)
  have he : i = n_pre := by omega
  subst i
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pref ?_
  split_pure_spatial
  · sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.undef_seg_empty pre_pre (n_pre+1))).1)
    have hseg : intArray.seg pre_pre 0 (n_pre+1) pref |-- intArray.full pre_pre (n_pre+1) pref := by
      simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.seg_to_full pre_pre 0 (n_pre+1) pref
    sep_apply hseg
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | (unfold PrefixSums; rw [PreH4]; exact PreH7)
    | (intro idx hi; have hb := PrefixArrayPrefix_entry_abs_bound l pref n_pre idx PreH7 PreH8 ⟨hi.1,by omega⟩; constructor <;> omega)


theorem proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2 := by
  unfold build_prefix_entail_wit_2
  left
  intro pre_pre n_pre arr_pre l pref_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH7 : (PrefixArrayPrefix l pref_2 i) := NewPreH7
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (pref_2 ++ [Znth (i-0) pref_2 0+Znth i l 0]) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (simpa only [Int.sub_zero] using prefix_step l pref_2 i PreH7 (by omega))


theorem proof_of_superPiano_safety_wit_50 : superPiano_safety_wit_50 := by
  unfold superPiano_safety_wit_50
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps ans st_slots vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42
  have nodes_PreH2 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH2
  have nodes_PreH23 := piano_nodes_of_arrays pop_slots vals starts los his bests NewPreH23
  simp only [nodes_PreH2, nodes_PreH23] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH11 : (n_pre <= 100000) := NewPreH11
  have PreH12 : (1 <= L_pre) := NewPreH12
  have PreH18 : ((Zlength (l)) = n_pre) := NewPreH18
  have PreH19 : (PrefixSums l ps) := NewPreH19
  have PreH29 : (FrontierState ps n_pre L_pre R_pre chosen t total (sublist ((0 : Int)) (hsize) (pop_slots))) := NewPreH29
  have PreH31 : (ValidNodeFields ps n_pre L_pre R_pre value start lo hi best) := NewPreH31
  have PreH41 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) := by
    intro k hk
    exact annotation_bounds k (by omega)
  have hv := ValidNodeFields_value_int_bound l ps n_pre L_pre R_pre value start lo hi best PreH19 PreH18 PreH11 PreH12 PreH41 PreH31
  have ht := frontier_total_int64_bound l ps n_pre L_pre R_pre chosen t total (sublist 0 hsize pop_slots) PreH19 PreH18 PreH11 PreH41 PreH29
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega


theorem proof_of_superPiano_safety_wit_65 : superPiano_safety_wit_65 := by
  unfold superPiano_safety_wit_65
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48
  have nodes_PreH8 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH8
  have nodes_PreH29 := piano_nodes_of_arrays pop_slots vals starts los his bests NewPreH29
  simp only [nodes_PreH8, nodes_PreH29] at *
  simp only [NewPreH1, NewPreH2]
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH18 : (n_pre <= 100000) := NewPreH17
  have PreH25 : ((Zlength (l)) = n_pre) := NewPreH24
  have PreH26 : (PrefixSums l query_ps) := NewPreH25
  have PreH48 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) := by
    intro k hk
    exact annotation_bounds k (by omega)
  have hh := PrefixSums_diff_int_bounds l query_ps n_pre retval_3 (start-1) PreH26 PreH25 PreH18 PreH48 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega


theorem proof_of_superPiano_safety_wit_91 : superPiano_safety_wit_91 := by
  unfold superPiano_safety_wit_91
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval_3 retval_4 retval_5 retval_6 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49 NewPreH50 NewPreH51 NewPreH52 NewPreH53 NewPreH54
  have nodes_PreH14 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH14
  have nodes_PreH35 := piano_nodes_of_arrays pop_slots vals starts los his bests NewPreH35
  simp only [nodes_PreH14, nodes_PreH35] at *
  simp only [NewPreH1, NewPreH2, NewPreH7, NewPreH8]
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH19 : (n_pre <= 100000) := NewPreH23
  have PreH26 : ((Zlength (l)) = n_pre) := NewPreH30
  have PreH27 : (PrefixSums l query_ps) := NewPreH31
  have PreH49 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) := by
    intro k hk
    exact annotation_bounds k (by omega)
  have hh := PrefixSums_diff_int_bounds l query_ps n_pre retval_6 (start-1) PreH27 PreH26 PreH19 PreH49 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega


theorem proof_of_superPiano_safety_wit_100 : superPiano_safety_wit_100 := by
  unfold superPiano_safety_wit_100
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval_3 retval retval_2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49
  have nodes_PreH9 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH9
  have nodes_PreH30 := piano_nodes_of_arrays pop_slots vals starts los his bests NewPreH30
  simp only [nodes_PreH9, nodes_PreH30] at *
  simp only [NewPreH1, NewPreH2]
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH25 : (n_pre <= 100000) := NewPreH18
  have PreH32 : ((Zlength (l)) = n_pre) := NewPreH25
  have PreH33 : (PrefixSums l query_ps) := NewPreH26
  have PreH55 : forall (idx : Int) , ((((0 : Int) <= idx) ∧ (idx < n_pre)) -> (((-1000) <= (Znth idx l (0 : Int))) ∧ ((Znth idx l (0 : Int)) <= 1000))) := by
    intro k hk
    exact annotation_bounds k (by omega)
  have hh := PrefixSums_diff_int_bounds l query_ps n_pre retval_3 (start-1) PreH33 PreH32 PreH25 PreH55 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals try simp only [INT_MAX,INT_MIN,Int.sub_zero] at *
  all_goals first | assumption | omega


theorem proof_of_superPiano_entail_wit_2 : superPiano_entail_wit_2 := by
  unfold superPiano_entail_wit_2
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 heap_cap ps_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH1 : (PrefixSums l ps_3) := NewPreH1
  have PreH11 : (PrefixSums l ps_2) := NewPreH11
  have he := PrefixSums_functional l ps_3 ps_2 PreH1 PreH11
  subst ps_3
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (zeros ((n_pre+1)*ST_LEVELS)) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (unfold zeros; simp only [Zlength,List.length_replicate]; exact Int.toNat_of_nonneg (by unfold ST_LEVELS; omega))


theorem proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4 := by
  unfold superPiano_entail_wit_4
  left
  intro R_pre L_pre k_pre n_pre arr_pre l total hsize t ans_2 st_slots_2 ps_2 heap_cap slots_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 retval retval_2 retval_3 retval_4 retval_5 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40
  have nodes_PreH30 := piano_nodes_of_arrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 NewPreH30
  simp only [nodes_PreH30] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH1 : (retval_5 = (heap_top_best (slots_2))) := by first | assumption | omega
  have PreH4 : (retval_4 = (heap_top_hi (slots_2))) := by first | assumption | omega
  have PreH7 : (retval_3 = (heap_top_lo (slots_2))) := by first | assumption | omega
  have PreH10 : (retval_2 = (heap_top_start (slots_2))) := by first | assumption | omega
  have PreH13 : (retval = (heap_top_value (slots_2))) := by first | assumption | omega
  have PreH16 : (t < k_pre) := NewPreH16
  have PreH36 : (FrontierState ps_2 n_pre L_pre R_pre chosen_2 t total (sublist ((0 : Int)) (hsize) (slots_2))) := NewPreH36
  have PreH38 : ((t < k_pre) -> ((0 : Int) < hsize)) := NewPreH38
  have hsize_pos : 0 < hsize := PreH38 PreH16
  have hlen : hsize ≤ Zlength slots_2 := by omega
  have ht := frontier_state_top_node_valid ps_2 n_pre L_pre R_pre chosen_2 t total slots_2 hsize hsize_pos hlen PreH36
  have hv : ValidNodeFields ps_2 n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5 := by
    rw [PreH10,PreH7,PreH4,PreH1,PreH13]
    exact ht
  have hv' := hv
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv'
  have hmin := hv'.2.2.2.2.2.1.trans (min_le_left _ _)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega


theorem proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5 := by
  unfold superPiano_entail_wit_5
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval retval_2 retval_3 retval_4 retval_5 retval_6 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49 NewPreH50 NewPreH51 NewPreH52 NewPreH53 NewPreH54
  have nodes_PreH14 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH14
  have nodes_PreH35 := piano_nodes_of_arrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 NewPreH35
  simp only [nodes_PreH14, nodes_PreH35] at *
  simp only [NewPreH1, NewPreH2, NewPreH7, NewPreH8]
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_both_children query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best retval retval_4 <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)


theorem proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6 := by
  unfold superPiano_entail_wit_6
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval retval_2 retval_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49
  have nodes_PreH9 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH9
  have nodes_PreH30 := piano_nodes_of_arrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 NewPreH30
  simp only [nodes_PreH9, nodes_PreH30] at *
  simp only [NewPreH2, NewPreH3]
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_left_only query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best retval <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)


theorem proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7 := by
  unfold superPiano_entail_wit_7
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44
  have nodes_PreH4 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH4
  have nodes_PreH25 := piano_nodes_of_arrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 NewPreH25
  simp only [nodes_PreH4, nodes_PreH25] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_singleton query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best  <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)


theorem proof_of_superPiano_entail_wit_11 : superPiano_entail_wit_11 := by
  unfold superPiano_entail_wit_11
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left has_right t hsize right_best hi best start right_value left_best lo left_value total value push_ps push_slots push_vals push_starts push_los push_his push_bests vals_out starts_out los_out his_out bests_out slots_out NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49 NewPreH50 NewPreH51 NewPreH52 NewPreH53 NewPreH54
  have nodes_PreH3 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH3
  have nodes_PreH19 := piano_nodes_of_arrays push_slots push_vals push_starts push_los push_his push_bests NewPreH19
  simp only [nodes_PreH3, nodes_PreH19] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) push_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_left_keeps_right_pending; assumption; assumption)


theorem proof_of_superPiano_entail_wit_12 : superPiano_entail_wit_12 := by
  unfold superPiano_entail_wit_12
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 value start lo hi best heap_cap t hsize total pop_slots vals_out starts_out los_out his_out bests_out slots_out query_ps query_st_slots retval retval_2 retval_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49
  have nodes_PreH9 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH9
  have nodes_PreH30 := piano_nodes_of_arrays pop_slots vals_2 starts_2 los_2 his_2 bests_2 NewPreH30
  simp only [nodes_PreH9, nodes_PreH30] at *
  simp only [NewPreH1, NewPreH2]
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_st_slots ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) query_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first
    | assumption
    | omega
    | (apply frontier_pop_to_split_right_only query_ps n_pre L_pre R_pre chosen_2 t total pop_slots hsize slots_out value start lo hi best retval <;> first | assumption | omega)
    | (apply valid_node_fields_left_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> first | assumption | omega)
    | (apply valid_node_fields_right_child query_ps n_pre L_pre R_pre value start lo hi best _ <;> assumption)


theorem proof_of_superPiano_entail_wit_13_1 : superPiano_entail_wit_13_1 := by
  unfold superPiano_entail_wit_13_1
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left has_right t hsize right_best hi best start right_value total lo left_best left_value value right_ps right_slots right_vals right_starts right_los right_his right_bests vals_out starts_out los_out his_out bests_out slots_out NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49 NewPreH50 NewPreH51 NewPreH52 NewPreH53 NewPreH54
  have nodes_PreH2 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH2
  have nodes_PreH18 := piano_nodes_of_arrays right_slots right_vals right_starts right_los right_his right_bests NewPreH18
  simp only [nodes_PreH2, nodes_PreH18] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH51 : (ValidNodeFields right_ps n_pre L_pre R_pre left_value start lo (best - 1) left_best) := NewPreH51
  have PreH52 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best) := NewPreH52
  have hv := PreH52
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  have hvl := PreH51
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hvl
  have hleft : -2147483648 ≤ left_value ∧ left_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre left_value start lo (best-1) left_best
    all_goals assumption
  have hright : -2147483648 ≤ right_value ∧ right_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre right_value start (best+1) hi right_best
    all_goals assumption
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) right_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_single_pending_forms_frontier; assumption; assumption)


theorem proof_of_superPiano_entail_wit_13_2 : superPiano_entail_wit_13_2 := by
  unfold superPiano_entail_wit_13_2
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left left_best left_value has_right t hsize right_best hi best start right_value total lo value right_ps right_slots right_vals right_starts right_los right_his right_bests vals_out starts_out los_out his_out bests_out slots_out NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47
  have nodes_PreH2 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH2
  have nodes_PreH18 := piano_nodes_of_arrays right_slots right_vals right_starts right_los right_his right_bests NewPreH18
  simp only [nodes_PreH2, nodes_PreH18] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH45 : (ValidNodeFields right_ps n_pre L_pre R_pre value start lo hi best) := NewPreH45
  have hv := PreH45
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  
  have hright : -2147483648 ≤ right_value ∧ right_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre right_value start (best+1) hi right_best
    all_goals assumption
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) right_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_single_pending_forms_frontier; assumption; assumption)


theorem proof_of_superPiano_entail_wit_13_3 : superPiano_entail_wit_13_3 := by
  unfold superPiano_entail_wit_13_3
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 slots_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 heap_cap has_left has_right left_best left_value right_best right_value t hsize total best start lo hi value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37
  have nodes_PreH14 := piano_nodes_of_arrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 NewPreH14
  simp only [nodes_PreH14] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH34 : (ValidNodeFields ps_2 n_pre L_pre R_pre value start lo hi best) := NewPreH34
  have hv := PreH34
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega


theorem proof_of_superPiano_entail_wit_13_4 : superPiano_entail_wit_13_4 := by
  unfold superPiano_entail_wit_13_4
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ans_2 st_slots_2 chosen_2 heap_cap has_left has_right t hsize left_best best lo start left_value total hi right_best right_value value push_ps push_slots push_vals push_starts push_los push_his push_bests vals_out starts_out los_out his_out bests_out slots_out NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45 NewPreH46 NewPreH47 NewPreH48 NewPreH49 NewPreH50
  have nodes_PreH3 := piano_nodes_of_arrays slots_out vals_out starts_out los_out his_out bests_out NewPreH3
  have nodes_PreH19 := piano_nodes_of_arrays push_slots push_vals push_starts push_los push_his push_bests NewPreH19
  simp only [nodes_PreH3, nodes_PreH19] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH47 : (ValidNodeFields push_ps n_pre L_pre R_pre value start lo hi best) := NewPreH47
  have hv := PreH47
  dsimp only [ValidNodeFields,ValidNode,node_value,node_start,node_lo,node_hi,node_best,mkNode] at hv
  have hmin := hv.2.2.2.2.2.1.trans (min_le_left _ _)
  
  have hleft : -2147483648 ≤ left_value ∧ left_value ≤ 2147483647 := by
    apply ValidNodeFields_value_int_bound l push_ps n_pre L_pre R_pre left_value start lo (best-1) left_best
    all_goals assumption
  refine Automation.exp_right_rule (CRules := naive_C_Rules) chosen_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_out ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) push_ps ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (apply frontier_split_push_single_pending_forms_frontier; assumption; assumption)


theorem proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14 := by
  unfold superPiano_entail_wit_14
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 st_slots_2 slots_2 vals_2 starts_2 los_2 his_2 bests_2 chosen_2 heap_cap has_left has_right left_best right_best left_value right_value t hsize total best start hi lo value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43 NewPreH44 NewPreH45
  have nodes_PreH14 := piano_nodes_of_arrays slots_2 vals_2 starts_2 los_2 his_2 bests_2 NewPreH14
  simp only [nodes_PreH14] at *
  have annotation_bounds := annotation_nth_bounds l (by assumption) (by assumption)
  have indexed_bounds : ∀ idx : Int, 0 ≤ idx ∧ idx < n_pre → -1000 ≤ Znth idx l 0 ∧ Znth idx l 0 ≤ 1000 := by
    intro idx hi
    exact annotation_bounds idx (by omega)
  have PreH12 : (SuperPianoAnswerByPrefix ps_2 n_pre L_pre R_pre k_pre ans_2) := NewPreH12
  have PreH29 : ((0 : Int) <= hsize) := NewPreH29
  have PreH32 : (FrontierState ps_2 n_pre L_pre R_pre ((ChordCode (n_pre) (start) (best)) :: chosen_2) (t + 1) total (sublist ((0 : Int)) (hsize) (slots_2))) := NewPreH32
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (ChordCode n_pre start best::chosen_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) vals_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) starts_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) los_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) his_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) bests_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ans_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) st_slots_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ps_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [INT_MAX,INT_MIN] at *
    all_goals first | assumption | omega | (intro hmore; exact frontier_state_nonempty_if_more_choices_remain ps_2 n_pre L_pre R_pre k_pre ans_2 (ChordCode n_pre start best::chosen_2) (t+1) total slots_2 hsize PreH12 PreH32 PreH29 (by omega) hmore)


attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

private theorem scratch_split (x k cap : Int) (hk : 0 ≤ k ∧ k ≤ cap) :
    intArray.undef_full x cap |-- intArray.undef_full x k ** intArray.undef_seg x k cap := by
  sep_apply (intArray.undef_full_split_to_undef_seg x k cap hk)
  sep_apply (intArray.undef_seg_to_undef_full x 0 k)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

private theorem scratch_cleanup (x k cap : Int) (l : List Int) (hk : 0 ≤ k ∧ k ≤ cap) :
    intArray.full x k l ** intArray.undef_seg x k cap |-- intArray.undef_full x cap := by
  sep_apply (intArray.full_to_undef_full x k l)
  sep_apply (intArray.undef_full_to_undef_seg x k)
  sep_apply (intArray.undef_seg_merge_to_undef_full x 0 k cap hk)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

theorem proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1 := by
  unfold superPiano_entail_wit_1
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps_2 ans_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  Exists ans_2 ps_2
  simp only [Int.zero_mul, Int.add_zero]
  sep_apply (scratch_split ( &( "prefix" ) ) (n_pre + 1) 100001 ⟨by omega, by omega⟩)
  sep_apply (scratch_split ( &( "st" ) ) ((n_pre + 1) * 17) 1700017 ⟨by omega, by omega⟩)
  sep_apply (scratch_split ( &( "heap_value" ) ) ((n_pre + k_pre) + 1) 200000 ⟨by omega, by omega⟩)
  sep_apply (scratch_split ( &( "heap_start" ) ) ((n_pre + k_pre) + 1) 200000 ⟨by omega, by omega⟩)
  sep_apply (scratch_split ( &( "heap_lo" ) ) ((n_pre + k_pre) + 1) 200000 ⟨by omega, by omega⟩)
  sep_apply (scratch_split ( &( "heap_hi" ) ) ((n_pre + k_pre) + 1) 200000 ⟨by omega, by omega⟩)
  sep_apply (scratch_split ( &( "heap_best" ) ) ((n_pre + k_pre) + 1) 200000 ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial


theorem proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3 := by
  unfold superPiano_entail_wit_3
  left
  intro R_pre L_pre k_pre n_pre arr_pre l heap_cap ps_2 ans_2 st_slots_2 table vals_2 starts_2 los_2 his_2 bests_2 slots_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hf : FrontierState ps_2 n_pre L_pre R_pre [] 0 0 (sublist 0 retval slots_2) := PreH5
  Exists ([] : List Int) vals_2 starts_2 los_2 his_2 bests_2 slots_2 ans_2 table ps_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial


theorem proof_of_superPiano_entail_wit_15 : superPiano_entail_wit_15 := by
  unfold superPiano_entail_wit_15
  left
  intro R_pre L_pre k_pre n_pre arr_pre l chosen total hsize t vals starts los his bests slots ans st_slots ps_2 heap_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hanswer := frontier_state_complete_implies_answer ps_2 n_pre L_pre R_pre k_pre chosen total (sublist 0 hsize slots) (by simpa only [show t = k_pre by omega] using PreH21)
  Exists ps_2
  simp only [Int.zero_mul, Int.add_zero]
  sep_apply (scratch_cleanup ( &( "prefix" ) ) (n_pre + 1) 100001 ps_2 ⟨by omega, by omega⟩)
  sep_apply (scratch_cleanup ( &( "st" ) ) ((n_pre + 1) * 17) 1700017 st_slots ⟨by omega, by omega⟩)
  sep_apply (scratch_cleanup ( &( "heap_value" ) ) (heap_cap) 200000 vals ⟨by omega, by omega⟩)
  sep_apply (scratch_cleanup ( &( "heap_start" ) ) (heap_cap) 200000 starts ⟨by omega, by omega⟩)
  sep_apply (scratch_cleanup ( &( "heap_lo" ) ) (heap_cap) 200000 los ⟨by omega, by omega⟩)
  sep_apply (scratch_cleanup ( &( "heap_hi" ) ) (heap_cap) 200000 his ⟨by omega, by omega⟩)
  sep_apply (scratch_cleanup ( &( "heap_best" ) ) (heap_cap) 200000 bests ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial


theorem proof_of_superPiano_return_wit_1 : superPiano_return_wit_1 := by
  unfold superPiano_return_wit_1
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps_2 heap_cap hsize total PreH1 PreH2 PreH3 PreH4 PreH5
  Exists ps_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial


theorem proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure := by
  unfold superPiano_partial_solve_wit_1_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps_2 ans heap_cap PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  Exists ps_2
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure := by
  unfold superPiano_partial_solve_wit_3_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l heap_cap ps ans st_slots table PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hp := PreH11
  dsimp only [PrefixSums, PrefixArrayPrefix] at hp
  have hb := annotation_nth_bounds l PreH16 PreH17
  have hbound : ∀ idx, 0 ≤ idx ∧ idx < Zlength ps → -100000000 ≤ Znth idx ps 0 ∧ Znth idx ps 0 ≤ 100000000 := by
    intro idx hi
    have he := PrefixArrayPrefix_entry_abs_bound l ps (Zlength l) idx PreH11 hb ⟨hi.1, by omega⟩
    constructor <;> omega
  have hboth : Forall (fun z : Int => -100000000 ≤ z ∧ z ≤ 100000000) ps := by
    apply Forall.iff_forall_mem.mpr
    intro z hz
    obtain ⟨idx, hi, he⟩ := List.mem_iff_getElem.mp hz
    have hr := hbound (idx : Int) ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, he] using hr
  have hlo : Forall (fun z : Int => -100000000 ≤ z) ps := Forall.iff_forall_mem.mpr (fun z hz => (hboth.mem hz).1)
  have hhi : Forall (fun z : Int => z ≤ 100000000) ps := Forall.iff_forall_mem.mpr (fun z hz => (hboth.mem hz).2)
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_4_pure : superPiano_partial_solve_wit_4_pure := by
  unfold superPiano_partial_solve_wit_4_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l total hsize t ans st_slots ps heap_cap slots vals starts los his bests chosen PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have he := piano_nodes_of_arrays slots vals starts los his bests PreH15
  simp only [he]
  have hpositive := PreH23 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_5_pure : superPiano_partial_solve_wit_5_pure := by
  unfold superPiano_partial_solve_wit_5_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l total hsize t ans st_slots ps heap_cap slots vals starts los his bests chosen retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have he := piano_nodes_of_arrays slots vals starts los his bests PreH18
  simp only [he]
  have hpositive := PreH26 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_6_pure : superPiano_partial_solve_wit_6_pure := by
  unfold superPiano_partial_solve_wit_6_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l total hsize t ans st_slots ps heap_cap slots vals starts los his bests chosen retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have he := piano_nodes_of_arrays slots vals starts los his bests PreH21
  simp only [he]
  have hpositive := PreH29 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_7_pure : superPiano_partial_solve_wit_7_pure := by
  unfold superPiano_partial_solve_wit_7_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l total hsize t ans st_slots ps heap_cap slots vals starts los his bests chosen retval retval_2 retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have he := piano_nodes_of_arrays slots vals starts los his bests PreH24
  simp only [he]
  have hpositive := PreH32 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_8_pure : superPiano_partial_solve_wit_8_pure := by
  unfold superPiano_partial_solve_wit_8_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l total hsize t ans st_slots ps heap_cap slots vals starts los his bests chosen retval retval_2 retval_3 retval_4 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have he := piano_nodes_of_arrays slots vals starts los his bests PreH27
  simp only [he]
  have hpositive := PreH35 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_9_pure : superPiano_partial_solve_wit_9_pure := by
  unfold superPiano_partial_solve_wit_9_pure
  left
  intro R_pre L_pre k_pre n_pre arr_pre l ps ans st_slots vals starts los his bests chosen value start lo hi best heap_cap t hsize total pop_slots PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have he := piano_nodes_of_arrays pop_slots vals starts los his bests PreH19
  simp only [he]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_frontier_top_value_return_wit_1 : frontier_top_value_return_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5
  have hfields := PreH4.2.2.2.2.2 0 (by omega)
  have htop : Znth 0 vals 0 = heap_top_value (PianoNodes vals starts los his bests) := hfields.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_frontier_top_start_return_wit_1 : frontier_top_start_return_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5
  have hfields := PreH4.2.2.2.2.2 0 (by omega)
  have htop : Znth 0 starts 0 = heap_top_start (PianoNodes vals starts los his bests) := hfields.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_frontier_top_lo_return_wit_1 : frontier_top_lo_return_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5
  have hfields := PreH4.2.2.2.2.2 0 (by omega)
  have htop : Znth 0 los 0 = heap_top_lo (PianoNodes vals starts los his bests) := hfields.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_frontier_top_hi_return_wit_1 : frontier_top_hi_return_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5
  have hfields := PreH4.2.2.2.2.2 0 (by omega)
  have htop : Znth 0 his 0 = heap_top_hi (PianoNodes vals starts los his bests) := hfields.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_frontier_top_best_return_wit_1 : frontier_top_best_return_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5
  have hfields := PreH4.2.2.2.2.2 0 (by omega)
  have htop : Znth 0 bests 0 = heap_top_best (PianoNodes vals starts los his bests) := hfields.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

theorem proof_of_superPiano_partial_solve_wit_19_pure : superPiano_partial_solve_wit_19_pure := by
  right
  intro R_pre L_pre k_pre n_pre arr_pre l ans st_slots chosen heap_cap has_left has_right t hsize right_best hi best start right_value left_best lo left_value total value push_ps push_slots push_vals push_starts push_los push_his push_bests PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85
  have he := piano_nodes_of_arrays push_slots push_vals push_starts push_los push_his push_bests PreH52
  rw [he]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_20_pure : superPiano_partial_solve_wit_20_pure := by
  right
  intro R_pre L_pre k_pre n_pre arr_pre l ans st_slots chosen heap_cap has_left has_right t hsize left_best best lo start left_value total hi right_best right_value value push_ps push_slots push_vals push_starts push_los push_his push_bests PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82
  have he := piano_nodes_of_arrays push_slots push_vals push_starts push_los push_his push_bests PreH52
  rw [he]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_21_pure : superPiano_partial_solve_wit_21_pure := by
  right
  intro R_pre L_pre k_pre n_pre arr_pre l ans st_slots chosen heap_cap has_left has_right t hsize right_best hi best start right_value total lo left_best left_value value right_ps right_slots right_vals right_starts right_los right_his right_bests PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81 PreH82 PreH83 PreH84 PreH85 PreH86 PreH87 PreH88
  have he := piano_nodes_of_arrays right_slots right_vals right_starts right_los right_his right_bests PreH52
  rw [he]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_superPiano_partial_solve_wit_22_pure : superPiano_partial_solve_wit_22_pure := by
  right
  intro R_pre L_pre k_pre n_pre arr_pre l ans st_slots chosen heap_cap has_left left_best left_value has_right t hsize right_best hi best start right_value total lo value right_ps right_slots right_vals right_starts right_los right_his right_bests PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55 PreH56 PreH57 PreH58 PreH59 PreH60 PreH61 PreH62 PreH63 PreH64 PreH65 PreH66 PreH67 PreH68 PreH69 PreH70 PreH71 PreH72 PreH73 PreH74 PreH75 PreH76 PreH77 PreH78 PreH79 PreH80 PreH81
  have he := piano_nodes_of_arrays right_slots right_vals right_starts right_los right_his right_bests PreH52
  rw [he]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

private theorem map_replace_nth {A B : Type} (f : A → B) (xs : List A) (n : Nat) (v : A) :
    (replace_nth n xs v).map f = replace_nth n (xs.map f) (f v) := by
  induction xs generalizing n with
  | nil => simp only [replace_nth,List.map_nil]
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => simp only [replace_nth,List.map_cons,ih]

private theorem map_replace_index {A B : Type} (f : A → B) (xs : List A) (i : Int) (v : A) :
    (replace_Znth i v xs).map f = replace_Znth i (f v) (xs.map f) :=
  map_replace_nth f xs i.toNat v

private theorem nodearrays_maps (slots : List Node) (vals starts los his bests : List Int)
    (h : NodeArrays slots vals starts los his bests) :
    vals = slots.map node_value ∧ starts = slots.map node_start ∧ los = slots.map node_lo ∧
      his = slots.map node_hi ∧ bests = slots.map node_best := by
  exact ⟨list_eq_map_from_nth 0 default_node vals slots node_value h.1 (fun i hi => (h.2.2.2.2.2 i hi).1),
    list_eq_map_from_nth 0 default_node starts slots node_start h.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.1),
    list_eq_map_from_nth 0 default_node los slots node_lo h.2.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.2.1),
    list_eq_map_from_nth 0 default_node his slots node_hi h.2.2.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.2.2.1),
    list_eq_map_from_nth 0 default_node bests slots node_best h.2.2.2.2.1 (fun i hi => (h.2.2.2.2.2 i hi).2.2.2.2)⟩

private theorem nodearrays_of_maps (slots : List Node) :
    NodeArrays slots (slots.map node_value) (slots.map node_start) (slots.map node_lo)
      (slots.map node_hi) (slots.map node_best) := by
  refine ⟨by simp only [Zlength,List.length_map],by simp only [Zlength,List.length_map],
    by simp only [Zlength,List.length_map],by simp only [Zlength,List.length_map],
    by simp only [Zlength,List.length_map],?_⟩
  intro i hi
  have hn : i.toNat < slots.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hn,
    Option.map_some,Option.getD_some,and_self]

private theorem nodearrays_replace (slots : List Node) (vals starts los his bests : List Int)
    (h : NodeArrays slots vals starts los his bests) (i : Int) (nd : Node) :
    NodeArrays (replace_Znth i nd slots) (replace_Znth i (node_value nd) vals)
      (replace_Znth i (node_start nd) starts) (replace_Znth i (node_lo nd) los)
      (replace_Znth i (node_hi nd) his) (replace_Znth i (node_best nd) bests) := by
  obtain ⟨hv,hs,hl,hh,hb⟩ := nodearrays_maps slots vals starts los his bests h
  have hu := nodearrays_of_maps (replace_Znth i nd slots)
  simpa only [map_replace_index,←hv,←hs,←hl,←hh,←hb] using hu

theorem proof_of_piano_set_node_return_wit_1 : piano_set_node_return_wit_1 := by
  right
  intro best_pre hi_pre lo_pre start_pre value_pre index_pre cap_pre bests his los starts vals PreH1 PreH2 PreH3
  have h := nodearrays_replace (PianoNodes vals starts los his bests) vals starts los his bests PreH3 index_pre (mkNode value_pre start_pre lo_pre hi_pre best_pre)
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact h

private theorem mapped_node_nth (f : Node → Int) (slots : List Node) (i : Int)
    (hd : f default_node = 0) : Znth i (slots.map f) 0 = f (Znth i slots default_node) := by
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases he : slots[i.toNat]? with
  | none => simp only [he,Option.map_none,Option.getD_none,hd]
  | some nd => simp only [he,Option.map_some,Option.getD_some]

private theorem nodearrays_fields_all (slots : List Node) (vals starts los his bests : List Int)
    (h : NodeArrays slots vals starts los his bests) (i : Int) :
    Znth i vals 0 = node_value (Znth i slots default_node) ∧
    Znth i starts 0 = node_start (Znth i slots default_node) ∧
    Znth i los 0 = node_lo (Znth i slots default_node) ∧
    Znth i his 0 = node_hi (Znth i slots default_node) ∧
    Znth i bests 0 = node_best (Znth i slots default_node) := by
  obtain ⟨hv,hs,hl,hh,hb⟩ := nodearrays_maps slots vals starts los his bests h
  rw [hv,hs,hl,hh,hb]
  exact ⟨mapped_node_nth _ _ _ rfl,mapped_node_nth _ _ _ rfl,mapped_node_nth _ _ _ rfl,
    mapped_node_nth _ _ _ rfl,mapped_node_nth _ _ _ rfl⟩

private theorem nodearrays_swap (slots : List Node) (vals starts los his bests : List Int)
    (h : NodeArrays slots vals starts los his bests) (a b : Int) :
    NodeArrays (PianoSwap slots a b)
      (replace_Znth b (Znth a vals 0) (replace_Znth a (Znth b vals 0) vals))
      (replace_Znth b (Znth a starts 0) (replace_Znth a (Znth b starts 0) starts))
      (replace_Znth b (Znth a los 0) (replace_Znth a (Znth b los 0) los))
      (replace_Znth b (Znth a his 0) (replace_Znth a (Znth b his 0) his))
      (replace_Znth b (Znth a bests 0) (replace_Znth a (Znth b bests 0) bests)) := by
  obtain ⟨ha1,ha2,ha3,ha4,ha5⟩ := nodearrays_fields_all slots vals starts los his bests h a
  obtain ⟨hb1,hb2,hb3,hb4,hb5⟩ := nodearrays_fields_all slots vals starts los his bests h b
  have hfirst := nodearrays_replace slots vals starts los his bests h a (Znth b slots default_node)
  have hsecond := nodearrays_replace _ _ _ _ _ _ hfirst b (Znth a slots default_node)
  simpa only [PianoSwap,ha1,ha2,ha3,ha4,ha5,hb1,hb2,hb3,hb4,hb5] using hsecond

theorem proof_of_piano_swap_node_return_wit_1 : piano_swap_node_return_wit_1 := by
  right
  intro b_pre a_pre cap_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5
  have h := nodearrays_swap (PianoNodes vals starts los his bests) vals starts los his bests PreH5 a_pre b_pre
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact h

private theorem power2_positive (j : Int) (hj : 0 ≤ j) : 0 < Power2 j := by
  cases j with
  | ofNat n => exact pow_pos (by decide : (0 : Int) < 2) n
  | negSucc n => omega

private theorem power2_succ (j : Int) (hj : 0 ≤ j) : Power2 (j+1) = 2*Power2 j := by
  cases j with
  | ofNat n =>
    change (2 : Int)^(n+1) = 2*2^n
    rw [pow_succ,Int.mul_comm]
  | negSucc n => omega

private theorem power2_bound (j : Int) (hj : 0 ≤ j ∧ j ≤ 16) : Power2 j ≤ 65536 := by
  cases j with
  | ofNat n =>
    change (2 : Int)^n ≤ 65536
    have hn : n≤16 := by simp only [Int.ofNat_eq_coe] at hj; omega
    exact (pow_le_pow_right₀ (by decide : 1≤(2 : Int)) hn).trans (by norm_num)
  | negSucc n => omega

private theorem argmax_single (ps : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength ps) :
    RangeArgmax ps i i i := by
  refine ⟨hi.1,le_refl _,le_refl _,hi.2,?_⟩
  intro j hj
  have he : j=i := by omega
  subst j; exact le_refl _

private theorem argmax_left (ps : List Int) (lo a_hi b_lo hi a b : Int)
    (hcover : b_lo ≤ a_hi+1) (hlo : lo ≤ b_lo) (hhi : a_hi ≤ hi)
    (ha : RangeArgmax ps lo a_hi a) (hb : RangeArgmax ps b_lo hi b)
    (hv : Znth b ps 0 ≤ Znth a ps 0) : RangeArgmax ps lo hi a := by
  rcases ha with ⟨h0,ha0,ha1,ha2,ham⟩
  rcases hb with ⟨_,hb0,hb1,hb2,hbm⟩
  refine ⟨h0,ha0,by omega,hb2,?_⟩
  intro j hj
  by_cases he : j ≤ a_hi
  · exact ham j (by omega)
  · have := hbm j (by omega); omega

private theorem argmax_right (ps : List Int) (lo a_hi b_lo hi a b : Int)
    (hcover : b_lo ≤ a_hi+1) (hlo : lo ≤ b_lo) (hhi : a_hi ≤ hi)
    (ha : RangeArgmax ps lo a_hi a) (hb : RangeArgmax ps b_lo hi b)
    (hv : Znth a ps 0 ≤ Znth b ps 0) : RangeArgmax ps lo hi b := by
  rcases ha with ⟨h0,ha0,ha1,ha2,ham⟩
  rcases hb with ⟨_,hb0,hb1,hb2,hbm⟩
  refine ⟨h0,by omega,hb1,hb2,?_⟩
  intro j hj
  by_cases he : j ≤ a_hi
  · have := ham j (by omega); omega
  · exact hbm j (by omega)

private theorem sparse_start (ps table : List Int) (n : Int) : PianoSparseProgress ps table n 0 0 := by
  intro row col hr hc hn hd
  omega

private theorem sparse_base_step (ps table : List Int) (n i : Int)
    (hps : Zlength ps=n) (hlen : Zlength table=n*ST_LEVELS) (hi : 0 ≤ i ∧ i<n)
    (hp : PianoSparseProgress ps table n 0 i) :
    PianoSparseProgress ps (replace_Znth (i*ST_LEVELS) i table) n 0 (i+1) := by
  intro row col hr hc hn hd
  have he : col=0 := by omega
  subst col
  simp only [show Power2 0=1 from rfl,Int.add_zero] at hn ⊢
  by_cases hri : row=i
  · subst row
    rw [Znth_replace_Znth_Same 0 table (i*ST_LEVELS) i (by unfold ST_LEVELS at *; omega)]
    simpa only [Int.add_sub_cancel] using argmax_single ps i (by omega)
  · rw [Znth_replace_Znth_Diff 0 table (i*ST_LEVELS) (row*ST_LEVELS) i
      (by unfold ST_LEVELS at *; omega) (by unfold ST_LEVELS at *; omega) (by unfold ST_LEVELS at *; omega)]
    simpa only [show Power2 0=1 from rfl,Int.add_zero] using hp row 0 hr hc (by simpa only [show Power2 0=1 from rfl] using hn) (by omega)

private theorem sparse_base_complete (ps table : List Int) (n : Int)
    (hp : PianoSparseProgress ps table n 0 n) : PianoSparseProgress ps table n 1 0 := by
  intro row col hr hc hn hd
  have he : col=0 := by omega
  subst col
  apply hp row 0 hr hc hn
  simp only [show Power2 0=1 from rfl] at hn
  omega

private theorem sparse_level_complete (ps table : List Int) (n level i : Int)
    (hi : n < i+Power2 level) (hp : PianoSparseProgress ps table n level i) :
    PianoSparseProgress ps table n (level+1) 0 := by
  intro row col hr hc hn hd
  apply hp row col hr hc hn
  by_cases he : col<level
  · exact Or.inl he
  · have heq : col=level := by omega
    subst col; exact Or.inr ⟨rfl,by omega⟩

private theorem sparse_complete (ps table : List Int) (n level : Int)
    (hl : ST_LEVELS ≤ level) (hp : PianoSparseProgress ps table n level 0) : PianoSparseTable ps table n := by
  intro row col hr hc hn
  exact hp row col hr hc hn (Or.inl (by omega))

private theorem sparse_read (ps table : List Int) (n level i half width : Int)
    (hl : 1 ≤ level ∧ level<ST_LEVELS) (hh : half=Power2 (level-1))
    (hw : width=Power2 level) (hhp : 1 ≤ half) (hd : width=half+half)
    (hi : 0 ≤ i) (hn : i+width≤n) (hp : PianoSparseProgress ps table n level i) :
    RangeArgmax ps i (i+half-1) (Znth (i*ST_LEVELS+level-1) table 0) ∧
    RangeArgmax ps (i+half) (i+width-1) (Znth ((i+half)*ST_LEVELS+level-1) table 0) := by
  have ha := hp i (level-1) hi (by omega) (by omega) (Or.inl (by omega))
  have hb := hp (i+half) (level-1) (by omega) (by omega) (by omega) (Or.inl (by omega))
  rw [←hh] at ha hb
  constructor
  · convert ha using 1 <;> congr 1 <;> omega
  · convert hb using 1 <;> congr 1 <;> omega

private theorem sparse_write (ps table : List Int) (n level i best : Int)
    (hlen : Zlength table=n*ST_LEVELS) (hl : 0 ≤ level ∧ level<ST_LEVELS)
    (hi : 0 ≤ i) (hn : i+Power2 level≤n) (hp : PianoSparseProgress ps table n level i)
    (hb : RangeArgmax ps i (i+Power2 level-1) best) :
    PianoSparseProgress ps (replace_Znth (i*ST_LEVELS+level) best table) n level (i+1) := by
  intro row col hr hc hn' hd
  have hp1 := power2_positive level hl.1
  have hp2 := power2_positive col hc.1
  by_cases he : row*ST_LEVELS+col=i*ST_LEVELS+level
  · have hrc : row=i ∧ col=level := by unfold ST_LEVELS at *; omega
    rcases hrc with ⟨hrow,hcol⟩
    subst row; subst col
    rw [Znth_replace_Znth_Same 0 table (i*ST_LEVELS+level) best (by unfold ST_LEVELS at *; omega)]
    exact hb
  · rw [Znth_replace_Znth_Diff 0 table (i*ST_LEVELS+level) (row*ST_LEVELS+col) best
      (by unfold ST_LEVELS at *; omega) (by unfold ST_LEVELS at *; omega) (Ne.symm he)]
    apply hp row col hr hc hn'
    rcases hd with hlt | ⟨hcol,hrow⟩
    · exact Or.inl hlt
    · subst col
      have hne : row≠i := by intro h; subst row; exact he rfl
      exact Or.inr ⟨rfl,by omega⟩

private theorem sparse_query_read (ps table : List Int) (n lo hi level width : Int)
    (hlo : 0≤lo ∧ lo≤hi) (hhi : hi<n) (hl : 0≤level ∧ level<ST_LEVELS)
    (hw : width=Power2 level) (hpos : 1≤width) (hlen : width≤hi-lo+1)
    (ht : PianoSparseTable ps table n) :
    RangeArgmax ps lo (lo+width-1) (Znth (lo*ST_LEVELS+level) table 0) ∧
    RangeArgmax ps (hi-width+1) hi (Znth ((hi-width+1)*ST_LEVELS+level) table 0) := by
  have ha := ht lo level hlo.1 hl (by omega)
  have hb := ht (hi-width+1) level (by omega) hl (by omega)
  rw [←hw] at ha hb
  constructor
  · exact ha
  · convert hb using 1 <;> omega

theorem proof_of_build_sparse_argmax_entail_wit_3 : build_sparse_argmax_entail_wit_3 := by
  left
  intro st_pre len_pre pre_pre ps table_2 i PreH1 PreH2 PreH3 PreH4 PreH5
  have he : i=len_pre*17 := by omega
  subst i
  sep_apply (intArray.undef_seg_empty st_pre (len_pre*17))
  sep_apply (intArray.seg_to_full st_pre 0 (len_pre*17) table_2)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  have hp := sparse_start ps table_2 len_pre
  Exists table_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_entail_wit_4 : build_sparse_argmax_entail_wit_4 := by
  left
  intro st_pre len_pre pre_pre ps table_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  prop_apply (intArray.full_Zlength pre_pre len_pre ps)
  Intros_p hps
  prop_apply (intArray.full_Zlength st_pre (len_pre*17) (replace_Znth (i*17) i table_2))
  Intros_p htable
  rw [Zlength_replace_Znth] at htable
  have hp := sparse_base_step ps table_2 len_pre i hps htable (by omega) PreH6
  Exists (replace_Znth (i*17) i table_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_entail_wit_5 : build_sparse_argmax_entail_wit_5 := by
  left
  intro st_pre len_pre pre_pre ps table_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have he : i=len_pre := by omega
  subst i
  have hp := sparse_base_complete ps table_2 len_pre PreH6
  Exists table_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_entail_wit_7 : build_sparse_argmax_entail_wit_7 := by
  left
  intro st_pre len_pre pre_pre ps table i width half level PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs := sparse_read ps table len_pre level i half width (by unfold ST_LEVELS; omega) PreH6 PreH7 PreH8 PreH10 PreH11 PreH1 PreH13
  have hleft := hs.1.2.1
  have hleft_hi := hs.1.2.2.1
  have hright := hs.2.2.1
  have hright_hi := hs.2.2.2.1
  unfold ST_LEVELS at hleft hleft_hi hright hright_hi
  Exists table
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_entail_wit_9 : build_sparse_argmax_entail_wit_9 := by
  left
  intro st_pre len_pre pre_pre ps table_2 i width half level PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hp := sparse_level_complete ps table_2 len_pre level i (by omega) PreH13
  have hdouble := power2_succ level (by omega)
  have hbound := power2_bound level (by omega)
  have he : level+1-1=level := by omega
  have hshift : width=Power2 (level+1-1) := by rw [he]; exact PreH7
  Exists table_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_return_wit_1 : build_sparse_argmax_return_wit_1 := by
  left
  intro st_pre len_pre pre_pre ps table_2 width half level PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hp := sparse_complete ps table_2 len_pre level (by unfold ST_LEVELS; omega) PreH11
  Exists table_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_entail_wit_8_1 : build_sparse_argmax_entail_wit_8_1 := by
  left
  intro st_pre len_pre pre_pre ps table_2 level half width i a c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  prop_apply (intArray.full_Zlength st_pre (len_pre*17) (replace_Znth (i*17+level) a table_2))
  Intros_p htable
  rw [Zlength_replace_Znth] at htable
  have hs := sparse_read ps table_2 len_pre level i half width (by unfold ST_LEVELS; omega) PreH6 PreH7 PreH8 PreH10 PreH11 PreH12 PreH19
  unfold ST_LEVELS at hs
  rw [←PreH13,←PreH14] at hs
  have hb := argmax_left ps i (i+half-1) (i+half) (i+width-1) a c (by omega) (by omega) (by omega) hs.1 hs.2 (by omega)
  rw [PreH7] at hb
  have hp := sparse_write ps table_2 len_pre level i a htable (by unfold ST_LEVELS; omega) PreH11 (by omega) PreH19 hb
  Exists (replace_Znth (i*17+level) a table_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_build_sparse_argmax_entail_wit_8_2 : build_sparse_argmax_entail_wit_8_2 := by
  left
  intro st_pre len_pre pre_pre ps table_2 level half width i a c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  prop_apply (intArray.full_Zlength st_pre (len_pre*17) (replace_Znth (i*17+level) c table_2))
  Intros_p htable
  rw [Zlength_replace_Znth] at htable
  have hs := sparse_read ps table_2 len_pre level i half width (by unfold ST_LEVELS; omega) PreH6 PreH7 PreH8 PreH10 PreH11 PreH12 PreH19
  unfold ST_LEVELS at hs
  rw [←PreH13,←PreH14] at hs
  have hb := argmax_right ps i (i+half-1) (i+half) (i+width-1) a c (by omega) (by omega) (by omega) hs.1 hs.2 (by omega)
  rw [PreH7] at hb
  have hp := sparse_write ps table_2 len_pre level i c htable (by unfold ST_LEVELS; omega) PreH11 (by omega) PreH19 hb
  Exists (replace_Znth (i*17+level) c table_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (simp only [Power2,Z.pow] <;> norm_num)

theorem proof_of_query_argmax_entail_wit_1 : query_argmax_entail_wit_1 := by
  left
  intro hi_pre lo_pre st_pre len_pre pre_pre st_slots ps PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_query_argmax_entail_wit_2 : query_argmax_entail_wit_2 := by
  left
  intro hi_pre lo_pre st_pre len_pre pre_pre st_slots ps width level PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hdouble := power2_succ level PreH7
  have hl : level≤15 := by
    by_contra h
    have he : level=16 := by omega
    rw [he] at PreH9
    change width=65536 at PreH9
    omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_query_argmax_entail_wit_3 : query_argmax_entail_wit_3 := by
  left
  intro hi_pre lo_pre st_pre len_pre pre_pre st_slots ps width level PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hs := sparse_query_read ps st_slots len_pre lo_pre hi_pre level width (by omega) PreH6 (by unfold ST_LEVELS; omega) PreH9 PreH10 PreH11 PreH12
  have ha := hs.1.2.1
  have hah := hs.1.2.2.1
  have hb := hs.2.2.1
  have hbh := hs.2.2.2.1
  unfold ST_LEVELS at ha hah hb hbh
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_query_argmax_return_wit_1 : query_argmax_return_wit_1 := by
  left
  intro hi_pre lo_pre st_pre len_pre pre_pre st_slots ps level width a c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := sparse_query_read ps st_slots len_pre lo_pre hi_pre level width (by omega) PreH6 (by unfold ST_LEVELS; omega) PreH9 PreH10 PreH11 PreH19
  unfold ST_LEVELS at hs
  rw [←PreH13,←PreH14] at hs
  have hp := argmax_right ps lo_pre (lo_pre+width-1) (hi_pre-width+1) hi_pre a c (by omega) (by omega) (by omega) hs.1 hs.2 (by omega)
  have hlo := hp.2.1
  have hhi := hp.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_query_argmax_return_wit_2 : query_argmax_return_wit_2 := by
  left
  intro hi_pre lo_pre st_pre len_pre pre_pre st_slots ps level width a c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hs := sparse_query_read ps st_slots len_pre lo_pre hi_pre level width (by omega) PreH6 (by unfold ST_LEVELS; omega) PreH9 PreH10 PreH11 PreH19
  unfold ST_LEVELS at hs
  rw [←PreH13,←PreH14] at hs
  have hp := argmax_left ps lo_pre (lo_pre+width-1) (hi_pre-width+1) hi_pre a c (by omega) (by omega) (by omega) hs.1 hs.2 (by omega)
  have hlo := hp.2.1
  have hhi := hp.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

private theorem piano_perm_replace_head {A : Type} (l : List A) (k : Nat) (x d : A) (hk : k < l.length) :
    Permutation (x :: l) (l.getD k d :: replace_nth k l x) := by
  induction l generalizing k x with
  | nil => simp at hk
  | cons y l ih =>
    cases k with
    | zero => exact List.Perm.swap y x l
    | succ k =>
      simp only [List.getD_cons_succ, replace_nth]
      exact (List.Perm.swap y x l).trans
        ((ih k x (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hk)).cons y |>.trans (List.Perm.swap _ _ _))

private theorem piano_permutation_swap_nat {A : Type} (l : List A) (i j : Nat) (d : A)
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
          piano_perm_replace_head l j x d (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_succ] using
          (ih i j (by omega) (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj)).cons x

private theorem piano_permutation_swap_Znth_lt__push_sift_up {A : Type} (l : List A) (i j : Int) (d : A)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  apply piano_permutation_swap_nat
  · omega
  · simp only [Zlength,Int.ofNat_eq_coe] at h; omega

private theorem piano_replace_nth_comm_Z__push_sift_up (ni nj : Nat) {A : Type} (l : List A) (a b : A) (h : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a := by
  induction l generalizing ni nj with
  | nil => cases ni <;> cases nj <;> rfl
  | cons x l ih =>
    cases ni with
    | zero =>
      cases nj with
      | zero => exact False.elim (h rfl)
      | succ nj => rfl
    | succ ni =>
      cases nj with
      | zero => rfl
      | succ nj =>
        change x :: replace_nth nj (replace_nth ni l a) b = x :: replace_nth ni (replace_nth nj l b) a
        exact congrArg (List.cons x) (ih ni nj (by omega))

private theorem piano_replace_Znth_comm__push_sift_up {A : Type} (l : List A) (i j : Int) (a b : A)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) := by
  apply piano_replace_nth_comm_Z__push_sift_up; omega

private theorem piano_permutation_swap_Znth__push_sift_up {A : Type} (l : List A) (i j : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  by_cases he : i = j
  · subst j; simp only [replace_Znth_Znth]; exact List.Perm.refl _
  · by_cases hlt : i < j
    · exact piano_permutation_swap_Znth_lt__push_sift_up l i j d ⟨hi.1,hlt,hj.2⟩
    · rw [piano_replace_Znth_comm__push_sift_up l i j _ _ hi.1 hj.1 he]
      exact piano_permutation_swap_Znth_lt__push_sift_up l j i d ⟨hj.1,by omega,hi.2⟩


private theorem piano_prefix_nth {A : Type} (d : A) (i hi : Int) (xs : List A)
    (h : 0≤i ∧ i<hi) : Znth i (sublist 0 hi xs) d = Znth i xs d :=
  ListLib.Znth_sublist0 d i hi xs h

private theorem piano_list_ext {A : Type} (xs ys : List A) (d : A)
    (hlen : Zlength xs=Zlength ys)
    (hnth : ∀ i, 0≤i ∧ i<Zlength xs → Znth i xs d=Znth i ys d) : xs=ys :=
  (ListLib.list_eq_ext xs ys d).mpr ⟨hlen,hnth⟩

private theorem piano_app_nth1 {A : Type} (d : A) (xs ys : List A) (i : Int)
    (hi : 0≤i ∧ i<Zlength xs) : Znth i (xs++ys) d=Znth i xs d :=
  ListLib.app_Znth1 d xs ys i hi

private theorem piano_prefix_length {A : Type} (xs : List A) (n : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength xs) : Zlength (sublist 0 n xs) = n := by
  have hh : Zlength (sublist 0 n xs)=n-0 := ListLib.Zlength_sublist 0 n xs ⟨le_refl _,hn.1⟩ hn.2
  simpa only [Int.sub_zero] using hh

private theorem piano_prefix_set {A : Type} (xs : List A) (n i : Int) (v d : A)
    (hn : 0 ≤ n ∧ n ≤ Zlength xs) (hi : 0 ≤ i ∧ i < n) :
    sublist 0 n (replace_Znth i v xs) = replace_Znth i v (sublist 0 n xs) := by
  have hl := Zlength_replace_Znth xs i v
  have hp := piano_prefix_length xs n hn
  apply piano_list_ext _ _ d
  · rw [piano_prefix_length _ n (by omega), Zlength_replace_Znth, hp]
  · intro k hk
    rw [piano_prefix_length _ n (by omega)] at hk
    rw [piano_prefix_nth d k n _ hk]
    by_cases he : k=i
    · subst k
      rw [Znth_replace_Znth_Same d xs i v (by omega),
        Znth_replace_Znth_Same d _ i v (by omega)]
    · rw [Znth_replace_Znth_Diff d xs i k v (by omega) (by omega) (Ne.symm he),
        Znth_replace_Znth_Diff d _ i k v (by omega) (by omega) (Ne.symm he),
        piano_prefix_nth d k n xs hk]

private theorem piano_prefix_set_outside {A : Type} (xs : List A) (n i : Int) (v d : A)
    (hn : 0 ≤ n ∧ n ≤ i) (hi : i < Zlength xs) :
    sublist 0 n (replace_Znth i v xs) = sublist 0 n xs := by
  have hl := Zlength_replace_Znth xs i v
  apply piano_list_ext _ _ d
  · rw [piano_prefix_length _ n (by omega), piano_prefix_length xs n (by omega)]
  · intro k hk
    rw [piano_prefix_length _ n (by omega)] at hk
    rw [piano_prefix_nth d k n _ hk, piano_prefix_nth d k n xs hk]
    exact Znth_replace_Znth_Diff d xs i k v (by omega) (by omega) (by omega)

private theorem piano_prefix_append {A : Type} (xs : List A) (n : Int) (v d : A)
    (hn : 0 ≤ n ∧ n < Zlength xs) :
    sublist 0 (n+1) (replace_Znth n v xs) = sublist 0 n xs ++ [v] := by
  have hl := Zlength_replace_Znth xs n v
  rw [sublist_split 0 (n+1) n _ (by omega) (by omega),
    piano_prefix_set_outside xs n n v d (by omega) hn.2,
    sublist_single d n _ (by omega), Znth_replace_Znth_Same d xs n v hn]

private theorem piano_swap_prefix (xs : List Node) (n i j : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength xs) (hi : 0 ≤ i ∧ i<n) (hj : 0 ≤ j ∧ j<n) :
    sublist 0 n (PianoSwap xs i j) = PianoSwap (sublist 0 n xs) i j := by
  unfold PianoSwap
  rw [piano_prefix_set _ n j _ default_node (by simpa only [Zlength_replace_Znth] using hn) hj,
    piano_prefix_set xs n i _ default_node hn hi,
    piano_prefix_nth default_node i n xs hi, piano_prefix_nth default_node j n xs hj]

private theorem piano_map_sublist {A B : Type} (f : A → B) (xs : List A) (lo hi : Int) :
    (sublist lo hi xs).map f = sublist lo hi (xs.map f) := by
  simp only [sublist, List.map_drop, List.map_take]

open SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib

private theorem piano_order_prefix (slots : List Node) (size : Int) :
    heap_ordered ((sublist 0 size slots).map node_value) size ↔
      heap_ordered (slots.map node_value) size := by
  rw [piano_map_sublist]
  constructor <;> intro h i hi
  · have hp := heap_parent_positive_bounds__push_sift_up i size hi.1 (by omega)
    have hh := h i hi
    rw [piano_prefix_nth 0 (heap_parent i) size _ (by omega),
      piano_prefix_nth 0 i size _ (by omega)] at hh
    exact hh
  · have hp := heap_parent_positive_bounds__push_sift_up i size hi.1 (by omega)
    rw [piano_prefix_nth 0 _ size _ (by omega),piano_prefix_nth 0 i size _ (by omega)]
    exact h i hi

private theorem piano_heap_from_order (slots : List Node) (size : Int)
    (hs : 0≤size ∧ size≤Zlength slots) (ho : heap_ordered (slots.map node_value) size) :
    NodeHeapState slots size := by
  refine ⟨ho,?_⟩
  by_cases he : size=0
  · subst size; left; simp [sublist]
  · right
    refine ⟨heap_top_node slots,⟨?_,?_⟩,rfl⟩
    · change Znth 0 slots default_node ∈ sublist 0 size slots
      rw [← piano_prefix_nth default_node 0 size slots (by omega)]
      have hl := piano_prefix_length slots size hs
      have hn : 0 < (sublist 0 size slots).length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
      change (sublist 0 size slots).getD 0 default_node ∈ _
      rw [List.getD_eq_getElem _ default_node hn]
      exact List.getElem_mem hn
    · intro nd hn
      obtain ⟨i,hi,heq⟩ := in_sublist0_Znth default_node size slots nd hs hn
      have hb := heap_ordered_root_upper_bound__pop_initialization (slots.map node_value) size i ho hi
      rw [mapped_node_nth node_value slots i rfl,mapped_node_nth node_value slots 0 rfl,heq] at hb
      exact hb

private theorem piano_scalar_push_start (base : List Int) (size x : Int)
    (hn : 0≤size) (hl : Zlength base=size) (ho : heap_ordered base size) :
    PushLoopState (base++[x]) (base++[x]) size size x := by
  have hlen : Zlength (base++[x])=size+1 := by simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega
  refine ⟨hn,hlen,hlen,hn,by omega,?_,List.Perm.refl _,?_,?_⟩
  · rw [app_Znth2 0 base [x] size (by omega),hl]; simp [Znth]
  · refine ⟨hn,by omega,?_⟩
    intro node hh
    have hb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    rw [piano_app_nth1 0 base [x] (heap_parent node) (by omega),
      piano_app_nth1 0 base [x] node (by omega)]
    exact ho node ⟨hh.1,by omega⟩
  · intro node hh
    have hb := heap_parent_positive_bounds__push_sift_up node size hh.1 (by omega)
    omega

private theorem piano_push_start (slots : List Node) (size : Int) (nd : Node)
    (hs : 0≤size ∧ size<Zlength slots) (hh : NodeHeapState slots size) :
    PianoHeapPush slots (replace_Znth size nd slots) size size nd := by
  constructor
  · refine ⟨Zlength_replace_Znth _ _ _,?_⟩
    rw [piano_prefix_append slots size nd default_node hs]
    exact (List.perm_append_singleton nd _).symm
  · rw [piano_prefix_append slots size nd default_node hs,List.map_append,List.map_singleton]
    apply piano_scalar_push_start _ size (node_value nd) hs.1
    · simpa only [Zlength,List.length_map] using piano_prefix_length slots size (by omega)
    · exact (piano_order_prefix slots size).mpr hh.1

private theorem piano_swap_values (slots : List Node) (i j : Int) :
    (PianoSwap slots i j).map node_value =
      replace_Znth j (Znth i (slots.map node_value) 0)
        (replace_Znth i (Znth j (slots.map node_value) 0) (slots.map node_value)) := by
  simp only [PianoSwap,map_replace_index,mapped_node_nth node_value slots i rfl,
    mapped_node_nth node_value slots j rfl]

private theorem piano_push_swap (before current : List Node) (size child : Int) (nd : Node)
    (hs : 0≤size ∧ size<Zlength current) (hc : 0<child ∧ child≤size)
    (hh : PianoHeapPush before current size child nd)
    (hlt : node_value (Znth (heap_parent child) current default_node) < node_value (Znth child current default_node)) :
    PianoHeapPush before (PianoSwap current (heap_parent child) child) size (heap_parent child) nd := by
  have hp := heap_parent_positive_bounds__push_sift_up child size hc.1 hc.2
  constructor
  · constructor
    · simpa only [PianoSwap,Zlength_replace_Znth] using hh.1.1
    · rw [piano_swap_prefix current (size+1) _ child (by omega) (by omega) (by omega)]
      exact hh.1.2.trans (piano_permutation_swap_Znth__push_sift_up _ _ _ default_node
        (by rw [piano_prefix_length current (size+1) (by omega)]; omega)
        (by rw [piano_prefix_length current (size+1) (by omega)]; omega))
  · rw [piano_swap_prefix current (size+1) _ child (by omega) (by omega) (by omega),piano_swap_values]
    apply (push_swap_advances_loop__push_sift_up _ _ size child (heap_parent child) (node_value nd) hh.2 hc.1 rfl ?_).2
    rw [piano_map_sublist,piano_prefix_nth 0 _ (size+1) _ (by omega),
      piano_prefix_nth 0 child (size+1) _ (by omega),
      mapped_node_nth node_value current _ rfl,mapped_node_nth node_value current child rfl]
    exact hlt

private theorem piano_push_finish (before current : List Node) (size child : Int) (nd : Node)
    (hs : 0≤size ∧ size<Zlength current) (hc : 0≤child ∧ child≤size)
    (hh : PianoHeapPush before current size child nd)
    (hstop : child=0 ∨ node_value (Znth child current default_node) ≤ node_value (Znth (heap_parent child) current default_node)) :
    NodeHeapState current (size+1) ∧ FrontierPushPrefix before size nd current := by
  refine ⟨piano_heap_from_order current (size+1) (by omega) ?_,hh.1⟩
  apply (piano_order_prefix current (size+1)).mp
  rcases hh.2 with ⟨_,_,_,_,_,_,_,hex,_⟩
  intro i hi
  by_cases he : i=child
  · subst i
    rcases hstop with he | hle
    · omega
    · have hp := heap_parent_positive_bounds__push_sift_up child size hi.1 hc.2
      rw [piano_map_sublist,piano_prefix_nth 0 _ (size+1) _ (by omega),
        piano_prefix_nth 0 child (size+1) _ (by omega),
        mapped_node_nth node_value current _ rfl,mapped_node_nth node_value current child rfl]
      exact hle
  · exact hex.2.2 i ⟨hi.1,hi.2,he⟩

private theorem piano_prefix_nested {A : Type} (xs : List A) (lo hi n : Int) (hn : hi≤n) :
    sublist lo hi (sublist 0 n xs) = sublist lo hi xs := by
  simp only [sublist,Int.toNat_zero,List.drop_zero,List.take_take]
  rw [Nat.min_eq_left (by omega)]

private theorem piano_pop_remaining {A : Type} (before : List A) (d : A) (size : Int)
    (hs : 1<size) (hl : Zlength before=size) :
    Permutation (sublist 0 (size-1) (replace_Znth 0 (Znth (size-1) before d) before)) (sublist 1 size before) := by
  cases before with
  | nil => simp only [Zlength_nil] at hl; omega
  | cons x l =>
    have hllen : Zlength l=size-1 := by simp only [Zlength_cons] at hl; omega
    change Permutation (sublist 0 (size-1) (Znth (size-1) (x::l) d::l)) (sublist 1 size (x::l))
    rw [Znth_cons d (size-1) x l (by omega),sublist_cons1 (size-1) _ l (by omega)]
    have he : sublist 1 size (x::l)=l := by
      unfold sublist
      have hn : size.toNat=l.length+1 := by simp only [Zlength,Int.ofNat_eq_coe] at hllen; omega
      simp [hn]
    rw [he]
    have ht : sublist 0 (size-2+1) l=sublist 0 (size-2) l++[Znth (size-2) l d] := by
      rw [sublist_split 0 (size-2+1) (size-2) l (by omega) (by omega),sublist_single d (size-2) l (by omega)]
    rw [sublist_self l _ (by omega)] at ht
    rw [show size-1-1=size-2 by omega]
    exact (List.perm_append_singleton _ _).symm.trans (List.Perm.of_eq ht.symm)

private theorem piano_prefix_cons (xs : List Node) (n : Int) (hn : 0<n ∧ n≤Zlength xs) :
    sublist 0 n xs=Znth 0 xs default_node::sublist 1 n xs := by
  rw [sublist_split 0 n 1 xs (by omega) (by omega)]
  have hh : sublist 0 1 xs=[Znth 0 xs default_node] := by
    simpa only [Int.zero_add] using sublist_single default_node 0 xs (by omega)
  rw [hh]
  rfl

private theorem piano_pop_start (slots : List Node) (size : Int)
    (hs : 1<size ∧ size≤Zlength slots) (hh : NodeHeapState slots size) :
    PianoHeapPop slots (replace_Znth 0 (Znth (size-1) slots default_node) slots) size 0 := by
  constructor
  · refine ⟨Zlength_replace_Znth _ _ _,?_,?_⟩
    · rw [piano_prefix_cons slots size (by omega)]; exact List.mem_cons_self
    · have hp := piano_pop_remaining (sublist 0 size slots) default_node size hs.1 (piano_prefix_length slots size (by omega))
      rw [piano_prefix_nth default_node (size-1) size slots (by omega),
        ←piano_prefix_set slots size 0 _ default_node (by omega) (by omega),
        piano_prefix_nested _ 0 (size-1) size (by omega),piano_prefix_nested slots 1 size size (by omega)] at hp
      rw [piano_prefix_cons slots size (by omega)]
      exact hp.cons _
  · rw [piano_prefix_set slots size 0 _ default_node (by omega) (by omega),map_replace_index]
    have he : node_value (Znth (size-1) slots default_node)=Znth (size-1) ((sublist 0 size slots).map node_value) 0 := by
      rw [piano_map_sublist,piano_prefix_nth 0 _ size _ (by omega),mapped_node_nth node_value slots _ rfl]
    rw [he]
    apply pop_root_replacement_loop_state__pop_initialization _ size hs.1
    · simpa only [Zlength,List.length_map] using piano_prefix_length slots size (by omega)
    · exact (piano_order_prefix slots size).mpr hh.1

private theorem piano_pop_swap (before current : List Node) (size index selected : Int)
    (hs : 1<size ∧ size≤Zlength current) (hi : 0≤index ∧ index<size-1) (hsel : 0≤selected ∧ selected<size-1)
    (hh : PianoHeapPop before current size index) (hc : PianoHeapSelected current (size-1) index selected)
    (hlt : node_value (Znth index current default_node)<node_value (Znth selected current default_node)) :
    PianoHeapPop before (PianoSwap current index selected) size selected := by
  have hc' : PopSelectedChild ((sublist 0 size current).map node_value) (size-1) index selected := by
    simpa only [PianoHeapSelected,Int.sub_add_cancel] using hc
  constructor
  · refine ⟨?_,hh.1.2.1,?_⟩
    · simpa only [PianoSwap,Zlength_replace_Znth] using hh.1.1
    · rw [piano_swap_prefix current (size-1) index selected (by omega) hi hsel]
      exact ((piano_permutation_swap_Znth__push_sift_up _ index selected default_node
        (by rw [piano_prefix_length current (size-1) (by omega)]; exact hi)
        (by rw [piano_prefix_length current (size-1) (by omega)]; exact hsel)).symm.cons _).trans hh.1.2.2
  · rw [piano_swap_prefix current size index selected (by omega) (by omega) (by omega),piano_swap_values]
    apply pop_swap_advances_loop__pop_swap_transition _ _ size index selected hh.2 hc'
    rw [piano_map_sublist,piano_prefix_nth 0 index size _ (by omega),
      piano_prefix_nth 0 selected size _ (by omega),
      mapped_node_nth node_value current index rfl,mapped_node_nth node_value current selected rfl]
    exact hlt

private theorem piano_pop_finish (before current : List Node) (size index : Int)
    (hs : 1<size ∧ size≤Zlength current) (hi : 0≤index ∧ index<size-1)
    (hh : PianoHeapPop before current size index)
    (hstop : index*2+1≥size-1 ∨ ∃ selected, (0≤selected ∧ selected<size-1) ∧
      PianoHeapSelected current (size-1) index selected ∧
      node_value (Znth selected current default_node)≤node_value (Znth index current default_node)) :
    NodeHeapState current (size-1) ∧ FrontierPopTop before size current := by
  refine ⟨piano_heap_from_order current (size-1) (by omega) ?_,hh.1⟩
  have horder : heap_ordered ((sublist 0 size before).map node_value) size := hh.2.2.2.2.2.2.1
  have hmax : PrefixMaximum ((sublist 0 size before).map node_value) size
      (Znth 0 ((sublist 0 size before).map node_value) 0) := by
    refine ⟨by omega,by have hb := hh.2.2.1; omega,rfl,?_⟩
    intro j hj
    exact heap_ordered_root_upper_bound__pop_initialization _ size j horder hj
  have hready : PopReadyState ((sublist 0 size before).map node_value)
      ((sublist 0 size current).map node_value) size
      (Znth 0 ((sublist 0 size before).map node_value) 0) := by
    rcases hstop with hleaf | ⟨selected,hsel,hselected,hle⟩
    · exact pop_leaf_ready__pop_ready_exit _ _ size _ index hmax hh.2 hleaf
    · have hc : PopSelectedChild ((sublist 0 size current).map node_value) (size-1) index selected := by
        simpa only [PianoHeapSelected,Int.sub_add_cancel] using hselected
      apply pop_comparison_ready__pop_ready_exit _ _ size _ index selected hmax hh.2 hc
      rw [piano_map_sublist,piano_prefix_nth 0 index size _ (by omega),
        piano_prefix_nth 0 selected size _ (by omega),
        mapped_node_nth node_value current index rfl,mapped_node_nth node_value current selected rfl]
      exact hle
  intro child hc
  have hp := heap_parent_positive_bounds__push_sift_up child size hc.1 (by omega)
  have ho := hready.2.2.2.2.2.2.2 child hc
  rw [piano_map_sublist,piano_prefix_nth 0 _ size _ (by omega),
    piano_prefix_nth 0 child size _ (by omega)] at ho
  exact ho

private theorem piano_selected_left (slots : List Node) (size index : Int)
    (hi : 0≤index) (hl : index*2+1<size)
    (hc : index*2+2≥size ∨ node_value (Znth (index*2+2) slots default_node)≤node_value (Znth (index*2+1) slots default_node)) :
    PianoHeapSelected slots size index (index*2+1) := by
  apply pop_select_left__pop_child_selection _ size index hi hl
  by_cases hr : size≤index*2+2
  · exact Or.inl hr
  · right
    have hc' := hc.resolve_left (by omega)
    change Znth (index*2+1) ((sublist 0 (size+1) slots).map node_value) 0 ≥ Znth (index*2+2) ((sublist 0 (size+1) slots).map node_value) 0
    rw [piano_map_sublist,piano_prefix_nth 0 _ (size+1) _ (by omega),
      piano_prefix_nth 0 _ (size+1) _ (by omega),mapped_node_nth node_value slots _ rfl,
      mapped_node_nth node_value slots _ rfl]
    exact hc'

private theorem piano_selected_right (slots : List Node) (size index : Int)
    (hi : 0≤index) (hr : index*2+2<size)
    (hc : node_value (Znth (index*2+1) slots default_node)<node_value (Znth (index*2+2) slots default_node)) :
    PianoHeapSelected slots size index (index*2+2) := by
  apply pop_select_right__pop_child_selection _ size index hi hr
  change Znth (index*2+1) ((sublist 0 (size+1) slots).map node_value) 0 < Znth (index*2+2) ((sublist 0 (size+1) slots).map node_value) 0
  rw [piano_map_sublist,piano_prefix_nth 0 _ (size+1) _ (by omega),
    piano_prefix_nth 0 _ (size+1) _ (by omega),mapped_node_nth node_value slots _ rfl,
    mapped_node_nth node_value slots _ rfl]
  exact hc

private theorem piano_pop_singleton (slots : List Node) (hs : 1≤Zlength slots) :
    NodeHeapState slots 0 ∧ FrontierPopTop slots 1 slots := by
  constructor
  · exact piano_heap_from_order slots 0 (by omega) (by intro child hc; omega)
  · refine ⟨rfl,?_,?_⟩
    · rw [piano_prefix_cons slots 1 (by omega)]; exact List.mem_cons_self
    · rw [piano_prefix_cons slots 1 (by omega)]
      simp only [show (1 : Int)-1=0 from rfl,sublist,Int.toNat_zero,List.take_zero,List.drop_zero,List.drop_take]
      exact List.Perm.refl _

private theorem piano_initial_node (ps : List Int) (n L R start lo hi best value : Int)
    (hps : Zlength ps=n+1) (hlr : 1≤L ∧ L≤R) (hr : R≤n)
    (hs : 1≤start ∧ start≤n-L+1) (hlo : lo=start+L-1) (hhi : hi=min n (start+R-1))
    (ha : RangeArgmax ps lo hi best) (hv : value=Znth best ps 0-Znth (start-1) ps 0) :
    ValidNodeFields ps n L R value start lo hi best := by
  rcases ha with ⟨h0,hb0,hb1,hb2,hm⟩
  change Zlength ps=n+1 ∧ 1≤start ∧ start≤n ∧ start+L-1≤lo ∧ lo≤hi ∧
    hi≤min n (start+R-1) ∧ lo≤best ∧ best≤hi ∧
    value=Znth best ps 0-Znth (start-1) ps 0 ∧ _
  refine ⟨hps,hs.1,by omega,by omega,by omega,by omega,hb0,hb1,hv,?_⟩
  intro finish hf
  change lo≤finish ∧ finish≤hi at hf
  change Znth finish ps 0-Znth (start-1) ps 0≤value
  have := hm finish hf
  omega

private theorem piano_initial_empty (ps : List Int) (n L R : Int) :
    PianoInitialPrefix ps n L R 1 [] := by
  constructor
  · exact Forall.iff_forall_mem.mpr (by simp)
  · exact List.Perm.refl []

private theorem piano_range_normalize (n : Nat) :
    (List.range n).map (fun i => 1+(i : Int)) = (List.range n).map (fun i : Nat => 1+(i : Int)) := by
  change ((List.range n).flatMap (fun i : Nat => [(i : Int)])).map (fun i : Int => 1+i) = _
  rw [←List.map_eq_flatMap,List.map_map]
  rfl

private theorem piano_range_snoc (start : Int) (hs : 1≤start) :
    (List.range (start+1-1).toNat).map (fun i => 1+(i : Int)) =
      (List.range (start-1).toNat).map (fun i => 1+(i : Int)) ++ [start] := by
  have hn : (start+1-1).toNat=(start-1).toNat+1 := by omega
  rw [piano_range_normalize,piano_range_normalize,hn,List.range_succ,List.map_append,List.map_singleton]
  have he : 1+((start-1).toNat : Int)=start := by omega
  rw [he]

private theorem piano_initial_step (ps : List Int) (n L R start : Int)
    (nodes out : List Node) (nd : Node) (hs : 1≤start)
    (hp : PianoInitialPrefix ps n L R start nodes) (hv : ValidNode ps n L R nd)
    (hst : node_start nd=start) (hlo : node_lo nd=start+L-1)
    (hhi : node_hi nd=min n (start+R-1)) (hperm : (nd::nodes).Perm out) :
    PianoInitialPrefix ps n L R (start+1) out := by
  constructor
  · apply Forall_permutation _ (nd::nodes) out hperm
    apply Forall.iff_forall_mem.mpr
    intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      exact ⟨hv,by omega,by omega,by simpa only [hst] using hhi⟩
    · have hh := hp.1.mem hx
      exact ⟨hh.1,by omega,hh.2.2.1,hh.2.2.2⟩
  · rw [piano_range_snoc start hs]
    exact (hperm.map node_start).symm.trans (by
      simp only [List.map_cons,hst]
      exact (hp.2.cons start).trans (List.perm_append_singleton start _).symm)

private theorem piano_initial_complete (ps : List Int) (n L R : Int) (nodes : List Node)
    (hlr : 1≤L ∧ L≤R) (hr : R≤n)
    (hp : PianoInitialPrefix ps n L R (n-L+2) nodes) :
    InitialFrontierState ps n L R nodes := by
  have hstarts : (nodes.map node_start).Perm ((List.range (n-L+2-1).toNat).map (fun i : Nat => 1+(i : Int))) := by
    simpa only [piano_range_normalize] using hp.2
  have hnd : (nodes.map node_start).Nodup := hstarts.nodup_iff.mpr
    ((List.nodup_range).map (f := fun i : Nat => 1+(i : Int)) (by
      intro a b h
      exact Int.ofNat_inj.mp (Int.add_left_cancel h)))
  have hn : nodes.Nodup := hnd.of_map node_start
  have hinj := (List.nodup_map_iff_inj_on hn).mp hnd
  refine ⟨⟨rfl,List.nodup_nil,Forall.iff_forall_mem.mpr (by simp)⟩,rfl,?_,?_,?_,?_,?_⟩
  · intro picked rest h
    exact False.elim (List.not_mem_nil h)
  · exact Forall.iff_forall_mem.mpr (fun nd h => (hp.1.mem h).1)
  · refine ⟨hn,?_⟩
    intro a b ha hb hab he
    exact False.elim (hab (hinj a ha b hb he))
  · intro code hc hnot
    rcases hc with ⟨hps,hs,hse,he,hl,hrange⟩
    have hstart : CodeStart n code ∈ nodes.map node_start := by
      apply hstarts.mem_iff.mpr
      apply List.mem_map.mpr
      refine ⟨(CodeStart n code-1).toNat,List.mem_range.mpr (by omega),by omega⟩
    obtain ⟨nd,hmem,hsame⟩ := List.mem_map.mp hstart
    have hnode := hp.1.mem hmem
    refine ⟨nd,hmem,hsame.symm,?_,?_⟩
    · rw [hnode.2.2.1,hsame]; omega
    · rw [hnode.2.2.2,hsame]
      exact le_min he (by omega)
  · intro nd code hmem hcover hnil
    exact List.not_mem_nil hnil

private theorem piano_nodes_maps (vals starts los his bests : List Int)
    (hs : starts.length=vals.length) (hl : los.length=vals.length)
    (hh : his.length=vals.length) (hb : bests.length=vals.length) :
    (PianoNodes vals starts los his bests).map node_value=vals ∧
    (PianoNodes vals starts los his bests).map node_start=starts ∧
    (PianoNodes vals starts los his bests).map node_lo=los ∧
    (PianoNodes vals starts los his bests).map node_hi=his ∧
    (PianoNodes vals starts los his bests).map node_best=bests := by
  induction vals generalizing starts los his bests with
  | nil =>
    have hs' : starts=[] := List.eq_nil_of_length_eq_zero hs
    have hl' : los=[] := List.eq_nil_of_length_eq_zero hl
    have hh' : his=[] := List.eq_nil_of_length_eq_zero hh
    have hb' : bests=[] := List.eq_nil_of_length_eq_zero hb
    subst starts; subst los; subst his; subst bests
    simp [PianoNodes]
  | cons v vals ih =>
    cases starts with
    | nil => simp at hs
    | cons s starts =>
      cases los with
      | nil => simp at hl
      | cons l los =>
        cases his with
        | nil => simp at hh
        | cons h his =>
          cases bests with
          | nil => simp at hb
          | cons b bests =>
            have ht := ih starts los his bests (Nat.succ.inj hs) (Nat.succ.inj hl) (Nat.succ.inj hh) (Nat.succ.inj hb)
            simpa only [PianoNodes,List.zip_cons_cons,List.map_cons,node_value,node_start,node_lo,node_hi,node_best,mkNode,List.cons.injEq,true_and] using ht

private theorem piano_nodes_wf (vals starts los his bests : List Int)
    (hs : Zlength starts=Zlength vals) (hl : Zlength los=Zlength vals)
    (hh : Zlength his=Zlength vals) (hb : Zlength bests=Zlength vals) :
    NodeArrays (PianoNodes vals starts los his bests) vals starts los his bests := by
  have hm := piano_nodes_maps vals starts los his bests
    (Int.ofNat_inj.mp hs) (Int.ofNat_inj.mp hl)
    (Int.ofNat_inj.mp hh) (Int.ofNat_inj.mp hb)
  have hw := nodearrays_of_maps (PianoNodes vals starts los his bests)
  simpa only [hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2] using hw

private theorem piano_nth_bounded (ps : List Int) (i : Int)
    (hl : Forall (fun z => -100000000≤z) ps) (hu : Forall (fun z => z≤100000000) ps) :
    -100000000≤Znth i ps 0 ∧ Znth i ps 0≤100000000 := by
  by_cases h : i.toNat<ps.length
  · have hm := List.getElem_mem (l := ps) h
    simpa only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some] using And.intro (hl.mem hm) (hu.mem hm)
  · have he : ps[i.toNat]?=none := List.getElem?_eq_none (by omega)
    simp only [Znth,List.getD_eq_getElem?_getD,he,Option.getD_none]
    decide


theorem proof_of_frontier_push_entail_wit_1 : frontier_push_entail_wit_1 := by
  left
  intro best_pre hi_pre lo_pre start_pre value_pre size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals vals_out starts_out los_out his_out bests_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hp := piano_push_start (PianoNodes vals starts los his bests) size_pre (mkNode value_pre start_pre lo_pre hi_pre best_pre) (by omega) PreH6
  Exists (replace_Znth size_pre (mkNode value_pre start_pre lo_pre hi_pre best_pre) (PianoNodes vals starts los his bests)) vals_out starts_out los_out his_out bests_out
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_push_entail_wit_2 : frontier_push_entail_wit_2 := by
  left
  intro best_pre hi_pre lo_pre start_pre value_pre size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals child current_2 vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  have hb := heap_parent_positive_bounds__push_sift_up child size_pre PreH1 PreH6
  unfold heap_parent at hb
  Exists current_2 vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_push_entail_wit_3 : frontier_push_entail_wit_3 := by
  left
  intro best_pre hi_pre lo_pre start_pre value_pre size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals current_2 vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 child parent vals_out starts_out los_out his_out bests_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_out)
  Intros_p hlen
  have hn := PreH1.1
  rw [PianoSwap,Zlength_replace_Znth,Zlength_replace_Znth,piano_nodes_of_arrays _ _ _ _ _ _ PreH5] at hn
  have he : parent=heap_parent child := PreH9
  have hvp := (nodearrays_fields_all _ _ _ _ _ _ PreH5 parent).1
  have hvc := (nodearrays_fields_all _ _ _ _ _ _ PreH5 child).1
  have hlt : node_value (Znth (heap_parent child) current_2 default_node)<node_value (Znth child current_2 default_node) := by rw [←he,←hvp,←hvc]; exact PreH2
  have hp := piano_push_swap (PianoNodes vals starts los his bests) current_2 size_pre child (mkNode value_pre start_pre lo_pre hi_pre best_pre) (by omega) (by omega) PreH8 hlt
  rw [←he] at hp
  rw [piano_nodes_of_arrays _ _ _ _ _ _ PreH5] at PreH1
  Exists (PianoSwap current_2 parent child) vals_out starts_out los_out his_out bests_out
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_push_partial_solve_wit_4_pure : frontier_push_partial_solve_wit_4_pure := by
  left
  intro best_pre hi_pre lo_pre start_pre value_pre size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals current vals_cur starts_cur los_cur his_cur bests_cur child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  rw [piano_nodes_of_arrays _ _ _ _ _ _ PreH4]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_frontier_push_return_wit_1 : frontier_push_return_wit_1 := by
  left
  intro best_pre hi_pre lo_pre start_pre value_pre size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals child current vals_cur starts_cur los_cur his_cur bests_cur PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_cur)
  Intros_p hlen
  have hn := PreH4.1
  have hh := piano_push_finish (PianoNodes vals starts los his bests) current size_pre child (mkNode value_pre start_pre lo_pre hi_pre best_pre) (by omega) (by omega) PreH7 (Or.inl (by omega))
  have hheap := hh.1
  have hfields : FrontierPushFields (PianoNodes vals starts los his bests) size_pre value_pre start_pre lo_pre hi_pre best_pre current := hh.2
  Exists vals_cur starts_cur los_cur his_cur bests_cur current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_push_return_wit_2 : frontier_push_return_wit_2 := by
  left
  intro best_pre hi_pre lo_pre start_pre value_pre size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals current vals_cur starts_cur los_cur his_cur bests_cur child parent PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_cur)
  Intros_p hlen
  have hn := PreH4.1
  have hp := (nodearrays_fields_all _ _ _ _ _ _ PreH4 parent).1
  have hc := (nodearrays_fields_all _ _ _ _ _ _ PreH4 child).1
  change parent=heap_parent child at PreH8
  have hstop : node_value (Znth child current default_node)≤node_value (Znth (heap_parent child) current default_node) := by rw [←PreH8,←hp,←hc]; exact PreH1
  have hh := piano_push_finish (PianoNodes vals starts los his bests) current size_pre child (mkNode value_pre start_pre lo_pre hi_pre best_pre) (by omega) (by omega) PreH7 (Or.inr hstop)
  have hheap := hh.1
  have hfields : FrontierPushFields (PianoNodes vals starts los his bests) size_pre value_pre start_pre lo_pre hi_pre best_pre current := hh.2
  Exists vals_cur starts_cur los_cur his_cur bests_cur current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega


theorem proof_of_frontier_pop_only_entail_wit_1 : frontier_pop_only_entail_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals vals_out starts_out los_out his_out bests_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hf := nodearrays_fields_all _ _ _ _ _ _ PreH7 (size_pre-1)
  have he : mkNode (Znth (size_pre-1) vals 0) (Znth (size_pre-1) starts 0) (Znth (size_pre-1) los 0) (Znth (size_pre-1) his 0) (Znth (size_pre-1) bests 0) = Znth (size_pre-1) (PianoNodes vals starts los his bests) default_node := by
    rw [hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2]
    rfl
  rw [he] at PreH1
  have hp := piano_pop_start (PianoNodes vals starts los his bests) size_pre (by omega) PreH8
  Exists vals_out starts_out los_out his_out bests_out (replace_Znth 0 (Znth (size_pre-1) (PianoNodes vals starts los his bests) default_node) (PianoNodes vals starts los his bests))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_entail_wit_2_1 : frontier_pop_only_entail_wit_2_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2 index PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := (nodearrays_fields_all _ _ _ _ _ _ PreH10 (index*2+1)).1
  have hr := (nodearrays_fields_all _ _ _ _ _ _ PreH10 (index*2+2)).1
  have he : index*2+1+1=index*2+2 := by omega
  rw [he,hl,hr] at PreH1
  have hp := piano_selected_right current_2 (size_pre-1) index PreH7 (by omega) PreH1
  have hp' : PianoHeapSelected current_2 (size_pre-1) index (index*2+1+1) := by simpa only [he] using hp
  Exists vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_entail_wit_2_2 : frontier_pop_only_entail_wit_2_2 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2 index PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have hp := piano_selected_left current_2 (size_pre-1) index PreH6 PreH2 (Or.inl (by omega))
  Exists vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_entail_wit_2_3 : frontier_pop_only_entail_wit_2_3 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2 index PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hl := (nodearrays_fields_all _ _ _ _ _ _ PreH10 (index*2+1)).1
  have hr := (nodearrays_fields_all _ _ _ _ _ _ PreH10 (index*2+2)).1
  have he : index*2+1+1=index*2+2 := by omega
  rw [he,hl,hr] at PreH1
  have hp := piano_selected_left current_2 (size_pre-1) index PreH7 PreH3 (Or.inr PreH1)
  Exists vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_entail_wit_3 : frontier_pop_only_entail_wit_3 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals current_2 vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 index left right selected vals_out starts_out los_out his_out bests_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_out)
  Intros_p hlen
  rw [piano_nodes_of_arrays _ _ _ _ _ _ PreH9] at PreH1
  have hn := PreH1.1
  rw [PianoSwap,Zlength_replace_Znth,Zlength_replace_Znth] at hn
  have hi := (nodearrays_fields_all _ _ _ _ _ _ PreH9 index).1
  have hs := (nodearrays_fields_all _ _ _ _ _ _ PreH9 selected).1
  rw [hi,hs] at PreH2
  have hp := piano_pop_swap (PianoNodes vals starts los his bests) current_2 size_pre index selected (by omega) (by omega) (by omega) PreH8 PreH14 PreH2
  Exists vals_out starts_out los_out his_out bests_out (PianoSwap current_2 index selected)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_partial_solve_wit_11_pure : frontier_pop_only_partial_solve_wit_11_pure := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals current vals_cur starts_cur los_cur his_cur bests_cur index left right selected PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [piano_nodes_of_arrays _ _ _ _ _ _ PreH8]
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_frontier_pop_only_return_wit_1 : frontier_pop_only_return_wit_1 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  subst size_pre
  have hh := piano_pop_singleton (PianoNodes vals starts los his bests) (by omega)
  have hheap := hh.1
  have hpop := hh.2
  Exists vals starts los his bests (PianoNodes vals starts los his bests)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_return_wit_2 : frontier_pop_only_return_wit_2 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals vals_cur starts_cur los_cur his_cur bests_cur current index PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_cur)
  Intros_p hlen
  have hn := PreH8.1
  have hh := piano_pop_finish (PianoNodes vals starts los his bests) current size_pre index (by omega) (by omega) PreH7 (Or.inl PreH1)
  have hheap := hh.1
  have hpop := hh.2
  Exists vals_cur starts_cur los_cur his_cur bests_cur current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_frontier_pop_only_return_wit_3 : frontier_pop_only_return_wit_3 := by
  left
  intro size_pre cap_pre heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre bests his los starts vals current vals_cur starts_cur los_cur his_cur bests_cur index left right selected PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_cur)
  Intros_p hlen
  have hn := PreH8.1
  have hi := (nodearrays_fields_all _ _ _ _ _ _ PreH8 index).1
  have hs := (nodearrays_fields_all _ _ _ _ _ _ PreH8 selected).1
  rw [hi,hs] at PreH1
  have hh := piano_pop_finish (PianoNodes vals starts los his bests) current size_pre index (by omega) (by omega) PreH7 (Or.inr ⟨selected,⟨PreH11,PreH12⟩,PreH13,PreH1⟩)
  have hheap := hh.1
  have hpop := hh.2
  Exists vals_cur starts_cur los_cur his_cur bests_cur current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega


theorem proof_of_build_initial_frontier_entail_wit_4_1 : build_initial_frontier_entail_wit_4_1 := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals_2 starts_2 los_2 his_2 bests_2 slots_2 start size retval vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  prop_apply (intArray.full_Zlength pre_pre (n_pre+1) ps)
  Intros_p hps
  have hmin : n_pre=min n_pre (start+R_pre-1) := by omega
  have hv := piano_initial_node ps n_pre L_pre R_pre start (start+L_pre-1) n_pre retval (Znth retval ps 0-Znth (start-1) ps 0) hps (by omega) PreH14 (by omega) rfl hmin PreH7 rfl
  have he := piano_nodes_of_arrays _ _ _ _ _ _ PreH28
  rw [he] at PreH4
  have hp := piano_initial_step ps n_pre L_pre R_pre start (sublist 0 size slots_2) (sublist 0 (size+1) slots_out)
    (mkNode (Znth retval ps 0-Znth (start-1) ps 0) start (start+L_pre-1) n_pre retval)
    PreH19 PreH25 hv rfl rfl hmin PreH4.2
  Exists vals_out starts_out los_out his_out bests_out slots_out
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_build_initial_frontier_entail_wit_4_2 : build_initial_frontier_entail_wit_4_2 := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals_2 starts_2 los_2 his_2 bests_2 slots_2 start size retval vals_out starts_out los_out his_out bests_out slots_out PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  prop_apply (intArray.full_Zlength pre_pre (n_pre+1) ps)
  Intros_p hps
  have hmin : (start+R_pre-1)=min n_pre (start+R_pre-1) := by omega
  have hv := piano_initial_node ps n_pre L_pre R_pre start (start+L_pre-1) (start+R_pre-1) retval (Znth retval ps 0-Znth (start-1) ps 0) hps (by omega) PreH14 (by omega) rfl hmin PreH7 rfl
  have he := piano_nodes_of_arrays _ _ _ _ _ _ PreH28
  rw [he] at PreH4
  have hp := piano_initial_step ps n_pre L_pre R_pre start (sublist 0 size slots_2) (sublist 0 (size+1) slots_out)
    (mkNode (Znth retval ps 0-Znth (start-1) ps 0) start (start+L_pre-1) (start+R_pre-1) retval)
    PreH19 PreH25 hv rfl rfl hmin PreH4.2
  Exists vals_out starts_out los_out his_out bests_out slots_out
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_build_initial_frontier_partial_solve_wit_12_pure : build_initial_frontier_partial_solve_wit_12_pure := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals starts los his bests slots start size retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  rw [piano_nodes_of_arrays _ _ _ _ _ _ PreH24]
  have hh : NodeHeapState slots (start-1) := by rw [←PreH17]; exact PreH23
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_build_initial_frontier_partial_solve_wit_13_pure : build_initial_frontier_partial_solve_wit_13_pure := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals starts los his bests slots start size retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  rw [piano_nodes_of_arrays _ _ _ _ _ _ PreH24]
  have hh : NodeHeapState slots (start-1) := by rw [←PreH17]; exact PreH23
  split_pures <;> dump_pre_spatial
  all_goals first | assumption | omega

theorem proof_of_build_initial_frontier_safety_wit_23 : build_initial_frontier_safety_wit_23 := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals starts los his bests slots start size retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hb := piano_nth_bounded ps retval PreH18 PreH19
  have hs := piano_nth_bounded ps (start-1) PreH18 PreH19
  split_pures <;> dump_pre_spatial
  · change _ ≤ (2147483647 : Int)
    omega
  · change (-2147483648 : Int) ≤ _
    omega

theorem proof_of_build_initial_frontier_safety_wit_26 : build_initial_frontier_safety_wit_26 := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals starts los his bests slots start size retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hb := piano_nth_bounded ps retval PreH18 PreH19
  have hs := piano_nth_bounded ps (start-1) PreH18 PreH19
  split_pures <;> dump_pre_spatial
  · change _ ≤ (2147483647 : Int)
    omega
  · change (-2147483648 : Int) ≤ _
    omega

theorem proof_of_build_initial_frontier_return_wit_1 : build_initial_frontier_return_wit_1 := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps vals_2 starts_2 los_2 his_2 bests_2 slots_2 start size PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have he : start=n_pre-L_pre+2 := by omega
  rw [he] at PreH17
  have hp := piano_initial_complete ps n_pre L_pre R_pre (sublist 0 size slots_2) (by omega) PreH6 PreH17
  Exists vals_2 starts_2 los_2 his_2 bests_2 slots_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_build_initial_frontier_entail_wit_3 : build_initial_frontier_entail_wit_3 := by
  left
  intro heap_best_pre heap_hi_pre heap_lo_pre heap_start_pre heap_value_pre cap_pre st_pre R_pre L_pre n_pre pre_pre st_slots ps bests_2 his_2 los_2 starts_2 vals_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : i=cap_pre := by omega
  subst i
  sep_apply (intArray.undef_seg_empty heap_value_pre cap_pre)
  sep_apply (intArray.seg_to_full heap_value_pre 0 cap_pre vals_2)
  sep_apply (intArray.undef_seg_empty heap_start_pre cap_pre)
  sep_apply (intArray.seg_to_full heap_start_pre 0 cap_pre starts_2)
  sep_apply (intArray.undef_seg_empty heap_lo_pre cap_pre)
  sep_apply (intArray.seg_to_full heap_lo_pre 0 cap_pre los_2)
  sep_apply (intArray.undef_seg_empty heap_hi_pre cap_pre)
  sep_apply (intArray.seg_to_full heap_hi_pre 0 cap_pre his_2)
  sep_apply (intArray.undef_seg_empty heap_best_pre cap_pre)
  sep_apply (intArray.seg_to_full heap_best_pre 0 cap_pre bests_2)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  prop_apply (intArray.full_Zlength heap_value_pre cap_pre vals_2)
  Intros_p hlen_vals_2
  prop_apply (intArray.full_Zlength heap_start_pre cap_pre starts_2)
  Intros_p hlen_starts_2
  prop_apply (intArray.full_Zlength heap_lo_pre cap_pre los_2)
  Intros_p hlen_los_2
  prop_apply (intArray.full_Zlength heap_hi_pre cap_pre his_2)
  Intros_p hlen_his_2
  prop_apply (intArray.full_Zlength heap_best_pre cap_pre bests_2)
  Intros_p hlen_bests_2
  have hw := piano_nodes_wf vals_2 starts_2 los_2 his_2 bests_2 (by omega) (by omega) (by omega) (by omega)
  have hn := hw.1
  have hp : PianoInitialPrefix ps n_pre L_pre R_pre 1 (sublist 0 0 (PianoNodes vals_2 starts_2 los_2 his_2 bests_2)) := by
    simpa only [sublist,Int.toNat_zero,List.take_zero,List.drop_zero] using piano_initial_empty ps n_pre L_pre R_pre
  have hh := piano_heap_from_order (PianoNodes vals_2 starts_2 los_2 his_2 bests_2) 0 (by omega) (by intro child hc; omega)
  Exists vals_2 starts_2 los_2 his_2 bests_2 (PianoNodes vals_2 starts_2 los_2 his_2 bests_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

end SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_proof_manual
