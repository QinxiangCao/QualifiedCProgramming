import ListLib.General.Length
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P075_1474D_cleaning_goal P075_1474D_cleaning_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev charArray := naive_C_Rules.CharArray

private theorem app_left (l r : List Int) (i : Int) (h : 0 ≤ i ∧ i < Zlength l) : Znth i (l++r) 0=Znth i l 0 := ListLib.app_Znth1 0 l r i h

private theorem int64Array_head_missing (ptr lo hi : Int) (h : lo < hi) :
    int64Array.seg_shape ptr (lo+1) hi |-- int64Array.missing_i_shape ptr lo lo hi := by
  apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.missing_i_shape_unfold ptr lo lo hi h)).2)
  Left
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    rfl

private theorem charArray_head_missing (ptr lo hi : Int) (h : lo < hi) :
    charArray.seg_shape ptr (lo+1) hi |-- charArray.missing_i_shape ptr lo lo hi := by
  apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (charArray.missing_i_shape_unfold ptr lo lo hi h)).2)
  Left
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    rfl

private theorem int64Array_cell (ptr i v : Int) :
    ((ptr+i*sizeof(INT64)) # Int64|->v) |-- int64Array.seg ptr i (i+1) [v] := int64Array.seg_single ptr i v

private theorem int64Array_last_missing (ptr lo hi : Int) (h : lo < hi) :
    int64Array.missing_i_shape ptr (hi-1) lo hi |-- int64Array.seg_shape ptr lo (hi-1) := by
  generalize hn : (hi-lo).toNat = n
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
    sep_apply (int64Array.missing_i_shape_unfold ptr (hi-1) lo hi h)
    Split
    · Intros_p he
      have hl : lo+1=hi := by omega
      have he' : hi-1=lo := by omega
      rw [hl,he']
      sep_apply (int64Array.seg_shape_empty ptr hi)
      exact (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.seg_shape_empty ptr lo)).2)
    · Intros v
      sep_apply (ih (lo+1) (by omega) (by omega))
      apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.seg_shape_unfold ptr lo (hi-1) (by omega))).2)
      refine Automation.exp_right_rule (CRules := naive_C_Rules) v ?_
      cancel
      exact fun _ hs => ⟨by assumption,hs⟩

private theorem int64Array_materialize (ptr lo hi : Int) (h : lo ≤ hi) :
    int64Array.seg_shape ptr lo hi |-- EX l : List Int, “ (Zlength l=hi-lo) ” && int64Array.seg ptr lo hi l := by
  generalize hn : (hi-lo).toNat=n
  induction n generalizing lo with
  | zero =>
    have he : lo=hi := by omega
    rw [he]
    sep_apply (int64Array.seg_shape_empty ptr hi)
    refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
    split_pure_spatial
    · exact fun _ hs => ⟨rfl,rfl,hs⟩
    · dump_pre_spatial
      simp only [Zlength_nil,Int.sub_self]
  | succ n ih =>
    sep_apply (int64Array.seg_shape_unfold ptr lo hi (by omega))
    Intros v
    sep_apply (ih (lo+1) (by omega) (by omega))
    Intros tail
    refine Automation.exp_right_rule (CRules := naive_C_Rules) (v::tail) ?_
    split_pure_spatial
    · apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (int64Array.seg_unfold ptr lo hi tail v)).2)
      cancel
      exact fun _ hs => ⟨by assumption,hs⟩
    · dump_pre_spatial
      rw [Zlength_cons]
      omega

private theorem charArray_cell (ptr i v : Int) :
    ((ptr+i*sizeof(CHAR)) # Char|->v) |-- charArray.seg ptr i (i+1) [v] := charArray.seg_single ptr i v

private theorem charArray_last_missing (ptr lo hi : Int) (h : lo < hi) :
    charArray.missing_i_shape ptr (hi-1) lo hi |-- charArray.seg_shape ptr lo (hi-1) := by
  generalize hn : (hi-lo).toNat = n
  induction n generalizing lo with
  | zero => omega
  | succ n ih =>
    sep_apply (charArray.missing_i_shape_unfold ptr (hi-1) lo hi h)
    Split
    · Intros_p he
      have hl : lo+1=hi := by omega
      have he' : hi-1=lo := by omega
      rw [hl,he']
      sep_apply (charArray.seg_shape_empty ptr hi)
      exact (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (charArray.seg_shape_empty ptr lo)).2)
    · Intros v
      sep_apply (ih (lo+1) (by omega) (by omega))
      apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (charArray.seg_shape_unfold ptr lo (hi-1) (by omega))).2)
      refine Automation.exp_right_rule (CRules := naive_C_Rules) v ?_
      cancel
      exact fun _ hs => ⟨by assumption,hs⟩

private theorem charArray_materialize (ptr lo hi : Int) (h : lo ≤ hi) :
    charArray.seg_shape ptr lo hi |-- EX l : List Int, “ (Zlength l=hi-lo) ” && charArray.seg ptr lo hi l := by
  generalize hn : (hi-lo).toNat=n
  induction n generalizing lo with
  | zero =>
    have he : lo=hi := by omega
    rw [he]
    sep_apply (charArray.seg_shape_empty ptr hi)
    refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
    split_pure_spatial
    · exact fun _ hs => ⟨rfl,rfl,hs⟩
    · dump_pre_spatial
      simp only [Zlength_nil,Int.sub_self]
  | succ n ih =>
    sep_apply (charArray.seg_shape_unfold ptr lo hi (by omega))
    Intros v
    sep_apply (ih (lo+1) (by omega) (by omega))
    Intros tail
    refine Automation.exp_right_rule (CRules := naive_C_Rules) (v::tail) ?_
    split_pure_spatial
    · apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (charArray.seg_unfold ptr lo hi tail v)).2)
      cancel
      exact fun _ hs => ⟨by assumption,hs⟩
    · dump_pre_spatial
      rw [Zlength_cons]
      omega

private theorem leading_last (l : List Int) (i : Int) (hi : 0≤i) (hl : Zlength l=i+1) :
    Zlength (sublist 0 i l)=i ∧ l=sublist 0 i l++[Znth i l 0] := by
  constructor
  · have h : Zlength (sublist 0 i l)=i-0 := ListLib.Zlength_sublist 0 i l ⟨by omega,hi⟩ (by change i≤Zlength l; omega)
    omega
  · calc
      l = sublist 0 (i+1) l := (sublist_self l (i+1) hl.symm).symm
      _ = sublist 0 i l ++ [Znth i l 0] := by
        rw [sublist_split 0 (i+1) i l ⟨by omega,hi⟩ ⟨by omega,by omega⟩,sublist_single 0 i l ⟨hi,by omega⟩]

private theorem snoc_nth (l : List Int) (v i : Int) (hl : Zlength l=i) : Znth i (l++[v]) 0=v := by
  rw [app_Znth2 0 l [v] i (by omega),hl,sub_self]
  rfl

private theorem snoc_right (l : List Int) (v i : Int) (hl : Zlength l=i) : sublist i (i+1) (l++[v])=[v] := by
  rw [sublist_split_app_r i (i+1) i l [v] hl ⟨by omega,by omega⟩]
  simp only [sub_self,show i+1-i=1 from by omega]
  rfl

private theorem int64Array_snoc_split (ptr i v : Int) (l : List Int) (hi : 0≤i) (hl : Zlength l=i) :
    int64Array.seg ptr 0 (i+1) (l++[v]) |-- int64Array.seg ptr 0 i l ** ((ptr+i*sizeof(INT64)) # Int64|->v) := by
  sep_apply (int64Array.seg_split_to_seg ptr 0 i (i+1) (l++[v]) ⟨hi,by omega⟩)
  have he : sublist 0 i (l++[v])=l := by rw [← hl]; exact sublist_app_exact1 l [v]
  simp only [Int.sub_zero,he,snoc_right l v i hl]
  sep_apply (int64Array.seg_unfold ptr i (i+1) [] v)
  sep_apply (int64Array.seg_empty ptr (i+1) (i+1))
  cancel
  Intros_p heq
  exact naive_C_Rules.toContext.derivable1_refl _

private theorem charArray_snoc_split (ptr i v : Int) (l : List Int) (hi : 0≤i) (hl : Zlength l=i) :
    charArray.seg ptr 0 (i+1) (l++[v]) |-- charArray.seg ptr 0 i l ** ((ptr+i*sizeof(CHAR)) # Char|->v) := by
  sep_apply (charArray.seg_split_to_seg ptr 0 i (i+1) (l++[v]) ⟨hi,by omega⟩)
  have he : sublist 0 i (l++[v])=l := by rw [← hl]; exact sublist_app_exact1 l [v]
  simp only [Int.sub_zero,he,snoc_right l v i hl]
  sep_apply (charArray.seg_unfold ptr i (i+1) [] v)
  sep_apply (charArray.seg_empty ptr (i+1) (i+1))
  cancel
  Intros_p heq
  exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1 := by
  unfold solver_safety_wit_6_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  have hv := PreH4 (i-1) ⟨by omega,by omega⟩
  have hb := PreH10 (i-1) ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  rw [app_left pre_values [old_pre_i] (i-1) (by omega)]
  omega

theorem proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2 := by
  unfold solver_safety_wit_6_split_goal_2
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  have hv := PreH4 (i-1) ⟨by omega,by omega⟩
  have hb := PreH10 (i-1) ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  rw [app_left pre_values [old_pre_i] (i-1) (by omega)]
  omega

theorem proof_of_solver_safety_wit_6 : solver_safety_wit_6 := by
  unfold solver_safety_wit_6
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | first | exact (proof_of_solver_safety_wit_6_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_6_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))
    | first | exact (proof_of_solver_safety_wit_6_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_6_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10))

theorem proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1 := by
  unfold solver_safety_wit_22_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  have hv := PreH4 (i-1) ⟨by omega,by omega⟩
  have hb := PreH16 0 ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  omega

theorem proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2 := by
  unfold solver_safety_wit_22_split_goal_2
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  have hv := PreH4 (i-1) ⟨by omega,by omega⟩
  have hb := PreH16 0 ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  omega

theorem proof_of_solver_safety_wit_22 : solver_safety_wit_22 := by
  unfold solver_safety_wit_22
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pures
  all_goals first
    | first | exact (proof_of_solver_safety_wit_22_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_22_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))
    | first | exact (proof_of_solver_safety_wit_22_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_22_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values okpre_values suf_values oksuf_values suf_prefix oksuf_prefix i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))

theorem proof_of_solver_safety_wit_38_split_goal_1 : solver_safety_wit_38_split_goal_1 := by
  unfold solver_safety_wit_38_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH7 i ⟨by omega,by omega⟩
  have hb := PreH17 (i-1) ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  omega

theorem proof_of_solver_safety_wit_38_split_goal_2 : solver_safety_wit_38_split_goal_2 := by
  unfold solver_safety_wit_38_split_goal_2
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  dump_pre_spatial
  have hv := PreH7 i ⟨by omega,by omega⟩
  have hb := PreH17 (i-1) ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  omega

theorem proof_of_solver_safety_wit_38 : solver_safety_wit_38 := by
  unfold solver_safety_wit_38
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pures
  all_goals first
    | first | exact (proof_of_solver_safety_wit_38_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_38_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))
    | first | exact (proof_of_solver_safety_wit_38_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_38_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))

theorem proof_of_solver_safety_wit_44_split_goal_1 : solver_safety_wit_44_split_goal_1 := by
  unfold solver_safety_wit_44_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have hv1 := PreH8 (i-1) ⟨by omega,by omega⟩
  have hv2 := PreH8 i ⟨by omega,by omega⟩
  have hb := PreH18 (i-1) ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  omega

theorem proof_of_solver_safety_wit_44_split_goal_2 : solver_safety_wit_44_split_goal_2 := by
  unfold solver_safety_wit_44_split_goal_2
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  dump_pre_spatial
  have hv1 := PreH8 (i-1) ⟨by omega,by omega⟩
  have hv2 := PreH8 i ⟨by omega,by omega⟩
  have hb := PreH18 (i-1) ⟨by omega,by omega⟩
  try rw [Znth_cons 0 i 0 values (by omega)]
  try rw [Znth_cons 0 (i+1) 0 values (by omega)]
  try simp only [Int.sub_zero,Int.sub_self,Int.add_sub_cancel]
  omega

theorem proof_of_solver_safety_wit_44 : solver_safety_wit_44 := by
  unfold solver_safety_wit_44
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pures
  all_goals first
    | first | exact (proof_of_solver_safety_wit_44_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_44_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | first | exact (proof_of_solver_safety_wit_44_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) | (dump_pre_spatial; exact (proof_of_solver_safety_wit_44_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values PreH1 PreH2 PreH3 PreH4
  
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([1] : List Int) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([0] : List Int) ?_
  split_pure_spatial
  · sep_apply (int64Array_cell pre_pre 0 0)
    sep_apply (charArray_cell okpre_pre 0 1)
    sep_apply (int64Array.missing_i_shape_to_seg_shape_head pre_pre 0 (n_pre+1) (by omega))
    sep_apply (charArray.missing_i_shape_to_seg_shape_head okpre_pre 0 (n_pre+1) (by omega))
    try simp only [Int.zero_mul,Int.add_zero,Int.zero_add]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | omega | exact prefix_residual_state_init__prefix_construction values | exact prefix_residual_init_bound__prefix_construction | (simp only [Zlength_cons,Zlength_nil]; omega)

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  unfold solver_entail_wit_3_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  intro k hk
  exact PreH11 k hk

theorem proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2 := by
  unfold solver_entail_wit_3_split_goal_2
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  intro k hk
  exact PreH5 k hk

theorem proof_of_solver_entail_wit_3_split_goal_spatial : solver_entail_wit_3_split_goal_spatial := by
  unfold solver_entail_wit_3_split_goal_spatial
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  sep_apply (int64Array_head_missing pre_pre i (n_pre+1) (by omega))
  sep_apply (charArray_head_missing okpre_pre i (n_pre+1) (by omega))
  cancel

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · exact proof_of_solver_entail_wit_3_split_goal_spatial oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_entail_wit_3_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_3_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))
      | first | exact (proof_of_solver_entail_wit_3_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_3_split_goal_2 oksuf_pre okpre_pre suf_pre pre_pre n_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11))

theorem proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1 := by
  unfold solver_entail_wit_4_1
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hc := Znth_cons 0 i 0 values (by omega)
  have hp := app_left pre_values_2 [old_pre_i] (i-1) ⟨by omega,by omega⟩
  have hf := app_left okpre_values_2 [old_okpre_i] (i-1) ⟨by omega,by omega⟩
  simp only [Int.sub_zero,hc,hp,hf] at *
  let r := Znth (i-1) values 0-Znth (i-1) pre_values_2 0
  have hpr : replace_Znth i r (pre_values_2++[old_pre_i])=pre_values_2++[r] := by
    rw [← PreH8]
    exact replace_Znth_app_last__prefix_construction _ _ _
  have hfr : replace_Znth i 0 (okpre_values_2++[old_okpre_i])=okpre_values_2++[0] := by
    rw [← PreH9]
    exact replace_Znth_app_last__prefix_construction _ _ _
  change _ at hpr
  rw [hpr,hfr]
  have hstate : PrefixResidualState values (pre_values_2++[r]) (okpre_values_2++[0]) := by
    apply prefix_residual_extend_prior_false__prefix_construction values pre_values_2 okpre_values_2 i r
    all_goals first | assumption | rfl | omega
  have hbound : ∀ k, (0 ≤ k ∧ k < i+1) → -1000000000*k ≤ Znth k (pre_values_2++[r]) 0 ∧ Znth k (pre_values_2++[r]) 0 ≤ 1000000000*k := by
    apply prefix_residual_extend_bound__prefix_construction values pre_values_2 i r n_pre
    all_goals first | assumption | rfl | omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (okpre_values_2++[0]) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (pre_values_2++[r]) ?_
  split_pure_spatial
  · sep_apply (int64Array.missing_i_shape_to_seg_shape_head pre_pre i (n_pre+1) (by omega))
    sep_apply (charArray.missing_i_shape_to_seg_shape_head okpre_pre i (n_pre+1) (by omega))
    sep_apply (int64Array.full_to_seg pre_pre (i+1) (pre_values_2++[r]))
    sep_apply (charArray.full_to_seg okpre_pre (i+1) (okpre_values_2++[0]))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2 := by
  unfold solver_entail_wit_4_2
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hc := Znth_cons 0 i 0 values (by omega)
  have hp := app_left pre_values_2 [old_pre_i] (i-1) ⟨by omega,by omega⟩
  have hf := app_left okpre_values_2 [old_okpre_i] (i-1) ⟨by omega,by omega⟩
  simp only [Int.sub_zero,hc,hp,hf] at *
  let r := Znth (i-1) values 0-Znth (i-1) pre_values_2 0
  have hpr : replace_Znth i r (pre_values_2++[old_pre_i])=pre_values_2++[r] := by
    rw [← PreH9]
    exact replace_Znth_app_last__prefix_construction _ _ _
  have hfr : replace_Znth i 1 (okpre_values_2++[old_okpre_i])=okpre_values_2++[1] := by
    rw [← PreH10]
    exact replace_Znth_app_last__prefix_construction _ _ _
  change _ at hpr
  rw [hpr,hfr]
  have hb := PreH1
  rw [Znth_replace_Znth_Same 0 (pre_values_2++[old_pre_i]) i r (by rw [Zlength_app,Zlength_cons,Zlength_nil]; omega)] at hb
  have hstate : PrefixResidualState values (pre_values_2++[r]) (okpre_values_2++[1]) := by
    apply prefix_residual_extend_success__prefix_construction values pre_values_2 okpre_values_2 i r
    all_goals first | assumption | rfl | omega
  have hbound : ∀ k, (0 ≤ k ∧ k < i+1) → -1000000000*k ≤ Znth k (pre_values_2++[r]) 0 ∧ Znth k (pre_values_2++[r]) 0 ≤ 1000000000*k := by
    apply prefix_residual_extend_bound__prefix_construction values pre_values_2 i r n_pre
    all_goals first | assumption | rfl | omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (okpre_values_2++[1]) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (pre_values_2++[r]) ?_
  split_pure_spatial
  · sep_apply (int64Array.missing_i_shape_to_seg_shape_head pre_pre i (n_pre+1) (by omega))
    sep_apply (charArray.missing_i_shape_to_seg_shape_head okpre_pre i (n_pre+1) (by omega))
    sep_apply (int64Array.full_to_seg pre_pre (i+1) (pre_values_2++[r]))
    sep_apply (charArray.full_to_seg okpre_pre (i+1) (okpre_values_2++[1]))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3 := by
  unfold solver_entail_wit_4_3
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 old_pre_i old_okpre_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hc := Znth_cons 0 i 0 values (by omega)
  have hp := app_left pre_values_2 [old_pre_i] (i-1) ⟨by omega,by omega⟩
  have hf := app_left okpre_values_2 [old_okpre_i] (i-1) ⟨by omega,by omega⟩
  simp only [Int.sub_zero,hc,hp,hf] at *
  let r := Znth (i-1) values 0-Znth (i-1) pre_values_2 0
  have hpr : replace_Znth i r (pre_values_2++[old_pre_i])=pre_values_2++[r] := by
    rw [← PreH9]
    exact replace_Znth_app_last__prefix_construction _ _ _
  have hfr : replace_Znth i 0 (okpre_values_2++[old_okpre_i])=okpre_values_2++[0] := by
    rw [← PreH10]
    exact replace_Znth_app_last__prefix_construction _ _ _
  change _ at hpr
  rw [hpr,hfr]
  have hb := PreH1
  rw [Znth_replace_Znth_Same 0 (pre_values_2++[old_pre_i]) i r (by rw [Zlength_app,Zlength_cons,Zlength_nil]; omega)] at hb
  have hstate : PrefixResidualState values (pre_values_2++[r]) (okpre_values_2++[0]) := by
    apply prefix_residual_extend_current_false__prefix_construction values pre_values_2 okpre_values_2 i r
    all_goals first | assumption | rfl | omega
  have hbound : ∀ k, (0 ≤ k ∧ k < i+1) → -1000000000*k ≤ Znth k (pre_values_2++[r]) 0 ∧ Znth k (pre_values_2++[r]) 0 ≤ 1000000000*k := by
    apply prefix_residual_extend_bound__prefix_construction values pre_values_2 i r n_pre
    all_goals first | assumption | rfl | omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (okpre_values_2++[0]) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (pre_values_2++[r]) ?_
  split_pure_spatial
  · sep_apply (int64Array.missing_i_shape_to_seg_shape_head pre_pre i (n_pre+1) (by omega))
    sep_apply (charArray.missing_i_shape_to_seg_shape_head okpre_pre i (n_pre+1) (by omega))
    sep_apply (int64Array.full_to_seg pre_pre (i+1) (pre_values_2++[r]))
    sep_apply (charArray.full_to_seg okpre_pre (i+1) (okpre_values_2++[0]))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hi : i=n_pre+1 := by omega
  rw [hi] at *
  sep_apply (int64Array.seg_shape_empty pre_pre (n_pre+1))
  sep_apply (charArray.seg_shape_empty okpre_pre (n_pre+1))
  sep_apply (int64Array.seg_to_full pre_pre 0 (n_pre+1) pre_values_2)
  sep_apply (charArray.seg_to_full okpre_pre 0 (n_pre+1) okpre_values_2)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  sep_apply (int64Array.full_shape_split_to_missing_i_shape suf_pre (n_pre+1) (n_pre+2) (by omega))
  Intros old_suf_terminal
  sep_apply (charArray.full_shape_split_to_missing_i_shape oksuf_pre (n_pre+1) (n_pre+2) (by omega))
  Intros old_oksuf_terminal
  refine Automation.exp_right_rule (CRules := naive_C_Rules) old_oksuf_terminal ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) old_suf_terminal ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · cancel
    try elim_emp
    try cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | omega | (intro k hk; apply PreH11 k; omega)

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hs := suffix_residual_state_terminal_init__suffix_setup values
  have hn : Zlength values=n_pre := by omega
  rw [hn] at hs
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([1] : List Int) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([0] : List Int) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · have he : n_pre+2-1=n_pre+1 := by omega
    have hh64 : int64Array.missing_i_shape suf_pre (n_pre+1) 0 (n_pre+2) |-- int64Array.seg_shape suf_pre 0 (n_pre+1) := by simpa only [he] using int64Array_last_missing suf_pre 0 (n_pre+2) (by omega)
    sep_apply hh64
    have hh8 : charArray.missing_i_shape oksuf_pre (n_pre+1) 0 (n_pre+2) |-- charArray.seg_shape oksuf_pre 0 (n_pre+1) := by simpa only [he] using charArray_last_missing oksuf_pre 0 (n_pre+2) (by omega)
    sep_apply hh8
    sep_apply (int64Array_cell suf_pre (n_pre+1) 0)
    sep_apply (charArray_cell oksuf_pre (n_pre+1) 1)
    simp only [he,show n_pre+1+1=n_pre+2 from by omega]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | omega | (simp only [Zlength_cons,Zlength_nil]; omega) | (intro q hq; have he:q=0 := (by omega); subst q; change -1000000000*(n_pre-n_pre-0)≤0 ∧ 0≤1000000000*(n_pre-n_pre-0); omega)

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  sep_apply (int64Array_materialize suf_pre 0 (i+1) (by omega))
  Intros suf_prefix
  sep_apply (charArray_materialize oksuf_pre 0 (i+1) (by omega))
  Intros oksuf_prefix
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_prefix ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_prefix ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · cancel
    try elim_emp
    try cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 suf_values_2 oksuf_values_2 suf_prefix oksuf_prefix_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hi : 0≤i := by omega
  have hh := leading_last suf_prefix i hi PreH11
  let leading := sublist 0 i suf_prefix
  let r := Znth (i-1) values 0-Znth 0 suf_values_2 0
  have hr : replace_Znth i r suf_prefix=leading++[r] := by
    rw [hh.2]
    change replace_Znth i r (leading++[Znth i suf_prefix 0])=leading++[r]
    rw [← hh.1]
    exact replace_Znth_app_last__suffix_step _ _ _
  simp only [Int.sub_self,Znth_cons 0 i 0 values (by omega)]
  rw [hr]
  have hv := PreH4 (i-1) ⟨by omega,by omega⟩
  have ht := PreH16 0 ⟨by omega,by omega⟩
  have hb : -1000000000*(n_pre-i+1)≤r ∧ r≤1000000000*(n_pre-i+1) := by dsimp only [r]; omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) r ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_prefix_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) leading ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · sep_apply (int64Array.full_to_seg suf_pre (i+1) (leading++[r]))
    sep_apply (int64Array_snoc_split suf_pre i r leading (by omega) hh.1)
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | exact hh.1 | rfl | omega

theorem proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1 := by
  unfold solver_entail_wit_9_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 suf_values_2 oksuf_values_2 suf_leading_2 oksuf_prefix new_suf_i_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  have hh := leading_last oksuf_prefix i (by omega) PreH13
  let leading := sublist 0 i oksuf_prefix
  have hr : replace_Znth i 0 oksuf_prefix=leading++[0] := by
    rw [hh.2]
    change replace_Znth i 0 (leading++[Znth i oksuf_prefix 0])=leading++[0]
    rw [← hh.1]
    exact replace_Znth_app_last__suffix_step _ _ _
  rw [hr]
  simp only [Int.sub_self,Int.sub_zero] at *
  Left
  refine Automation.exp_right_rule (CRules := naive_C_Rules) 0 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) new_suf_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) leading ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_leading_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · sep_apply (charArray.full_to_seg oksuf_pre (i+1) (leading++[0]))
    sep_apply (charArray_snoc_split oksuf_pre i 0 leading (by omega) hh.1)
    sep_apply (int64Array_snoc_split suf_pre i new_suf_i_2 suf_leading_2 (by omega) PreH12)
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | exact hh.1 | rfl | omega | (intro h; constructor <;> omega)

theorem proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2 := by
  unfold solver_entail_wit_9_2
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 suf_values_2 oksuf_values_2 suf_leading_2 oksuf_prefix new_suf_i_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hh := leading_last oksuf_prefix i (by omega) PreH14
  let leading := sublist 0 i oksuf_prefix
  have hr : replace_Znth i 1 oksuf_prefix=leading++[1] := by
    rw [hh.2]
    change replace_Znth i 1 (leading++[Znth i oksuf_prefix 0])=leading++[1]
    rw [← hh.1]
    exact replace_Znth_app_last__suffix_step _ _ _
  rw [hr]
  simp only [Int.sub_self,Int.sub_zero] at *
  rw [snoc_nth suf_leading_2 new_suf_i_2 i PreH13] at PreH1
  have hb := suffix_residual_flag_boolean values (i+1) suf_values_2 oksuf_values_2 0 PreH16 ⟨by omega,by omega⟩
  Right
  refine Automation.exp_right_rule (CRules := naive_C_Rules) 1 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) new_suf_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) leading ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_leading_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · sep_apply (charArray.full_to_seg oksuf_pre (i+1) (leading++[1]))
    sep_apply (charArray_snoc_split oksuf_pre i 1 leading (by omega) hh.1)
    sep_apply (int64Array_snoc_split suf_pre i new_suf_i_2 suf_leading_2 (by omega) PreH13)
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | exact hh.1 | rfl | omega | (intro h; constructor <;> omega)

theorem proof_of_solver_entail_wit_9_3 : solver_entail_wit_9_3 := by
  unfold solver_entail_wit_9_3
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 suf_values_2 oksuf_values_2 suf_leading_2 oksuf_prefix new_suf_i_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hh := leading_last oksuf_prefix i (by omega) PreH14
  let leading := sublist 0 i oksuf_prefix
  have hr : replace_Znth i 0 oksuf_prefix=leading++[0] := by
    rw [hh.2]
    change replace_Znth i 0 (leading++[Znth i oksuf_prefix 0])=leading++[0]
    rw [← hh.1]
    exact replace_Znth_app_last__suffix_step _ _ _
  rw [hr]
  simp only [Int.sub_self,Int.sub_zero] at *
  rw [snoc_nth suf_leading_2 new_suf_i_2 i PreH13] at PreH1
  Left
  refine Automation.exp_right_rule (CRules := naive_C_Rules) 0 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) new_suf_i_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) leading ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_leading_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · sep_apply (charArray.full_to_seg oksuf_pre (i+1) (leading++[0]))
    sep_apply (charArray_snoc_split oksuf_pre i 0 leading (by omega) hh.1)
    sep_apply (int64Array_snoc_split suf_pre i new_suf_i_2 suf_leading_2 (by omega) PreH13)
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | exact hh.1 | rfl | omega | (intro h; constructor <;> omega)

theorem proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1 := by
  unfold solver_entail_wit_10_1
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 suf_values_2 oksuf_values_2 suf_leading oksuf_leading new_suf_i new_oksuf_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hs : SuffixResidualState values i (new_suf_i::suf_values_2) (new_oksuf_i::oksuf_values_2) := by
    apply suffix_residual_prepend_core__suffix_step values i suf_values_2 oksuf_values_2 new_suf_i new_oksuf_i
    all_goals first | assumption | omega | exact Or.inl PreH16 | exact ⟨by assumption,by assumption⟩
  have hb : ∀ q, (0≤q ∧ q<Zlength (new_suf_i::suf_values_2)) → -1000000000*(n_pre-(i-1)-q)≤Znth q (new_suf_i::suf_values_2) 0 ∧ Znth q (new_suf_i::suf_values_2) 0≤1000000000*(n_pre-(i-1)-q) := by
    apply suffix_residual_prepend_bound__suffix_step n_pre i suf_values_2 new_suf_i
    all_goals first | assumption | omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (new_oksuf_i::oksuf_values_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (new_suf_i::suf_values_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · sep_apply (int64Array_cell suf_pre i new_suf_i)
    sep_apply (charArray_cell oksuf_pre i new_oksuf_i)
    sep_apply (int64Array.seg_merge_to_seg suf_pre i (i+1) (n_pre+2) [new_suf_i] suf_values_2 (by omega))
    sep_apply (charArray.seg_merge_to_seg oksuf_pre i (i+1) (n_pre+2) [new_oksuf_i] oksuf_values_2 (by omega))
    sep_apply (int64Array.seg_to_seg_shape suf_pre 0 i suf_leading)
    sep_apply (charArray.seg_to_seg_shape oksuf_pre 0 i oksuf_leading)
    simp only [Int.sub_add_cancel,List.singleton_append]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2 := by
  unfold solver_entail_wit_10_2
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values pre_values_2 okpre_values_2 suf_values_2 oksuf_values_2 suf_leading oksuf_leading new_suf_i new_oksuf_i i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hs : SuffixResidualState values i (new_suf_i::suf_values_2) (new_oksuf_i::oksuf_values_2) := by
    apply suffix_residual_prepend_core__suffix_step values i suf_values_2 oksuf_values_2 new_suf_i new_oksuf_i
    all_goals first | assumption | omega | exact Or.inr PreH16 | exact ⟨by assumption,by assumption⟩
  have hb : ∀ q, (0≤q ∧ q<Zlength (new_suf_i::suf_values_2)) → -1000000000*(n_pre-(i-1)-q)≤Znth q (new_suf_i::suf_values_2) 0 ∧ Znth q (new_suf_i::suf_values_2) 0≤1000000000*(n_pre-(i-1)-q) := by
    apply suffix_residual_prepend_bound__suffix_step n_pre i suf_values_2 new_suf_i
    all_goals first | assumption | omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (new_oksuf_i::oksuf_values_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (new_suf_i::suf_values_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · sep_apply (int64Array_cell suf_pre i new_suf_i)
    sep_apply (charArray_cell oksuf_pre i new_oksuf_i)
    sep_apply (int64Array.seg_merge_to_seg suf_pre i (i+1) (n_pre+2) [new_suf_i] suf_values_2 (by omega))
    sep_apply (charArray.seg_merge_to_seg oksuf_pre i (i+1) (n_pre+2) [new_oksuf_i] oksuf_values_2 (by omega))
    sep_apply (int64Array.seg_to_seg_shape suf_pre 0 i suf_leading)
    sep_apply (charArray.seg_to_seg_shape oksuf_pre 0 i oksuf_leading)
    simp only [Int.sub_add_cancel,List.singleton_append]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | rfl | omega

theorem proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1 := by
  unfold solver_entail_wit_11_1
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hi : i=0 := by omega
  subst i
  try simp only [Int.zero_add,Int.sub_zero] at *
  have hd : ¬DirectResidualSuccess pre_values_2 okpre_values_2 (Zlength values) := by
    intro h
    change Znth (Zlength values) okpre_values_2 0=1 ∧ Znth (Zlength values) pre_values_2 0=0 at h
    rw [← PreH5] at h
    omega
  have hc := checked_swap_prefix_init values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 hd
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · cancel
    try elim_emp
    try cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | omega | (intro q hq; apply PreH16 q; omega)

theorem proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2 := by
  unfold solver_entail_wit_11_2
  left
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre a_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : i=0 := by omega
  subst i
  try simp only [Int.zero_add,Int.sub_zero] at *
  have hd : ¬DirectResidualSuccess pre_values_2 okpre_values_2 (Zlength values) := by
    intro h
    change Znth (Zlength values) okpre_values_2 0=1 ∧ Znth (Zlength values) pre_values_2 0=0 at h
    rw [← PreH6] at h
    omega
  have hc := checked_swap_prefix_init values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 hd
  refine Automation.exp_right_rule (CRules := naive_C_Rules) oksuf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) suf_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) okpre_values_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) pre_values_2 ?_
  split_pure_spatial
  · cancel
    try elim_emp
    try cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [Int.sub_add_cancel,Zlength_app,Zlength_cons,Zlength_nil]
    all_goals first | assumption | omega | (intro q hq; apply PreH17 q; omega)

theorem proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1 := by
  unfold solver_entail_wit_12_1_split_goal_1
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  apply checked_swap_prefix_step values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i PreH19
  intro h
  rcases h with ⟨hp,hf,hx,hy,he⟩
  try rw [Znth_cons 0 i 0 values (by omega)] at PreH1
  try rw [Znth_cons 0 (i+1) 0 values (by omega)] at PreH1
  try simp only [Int.add_sub_cancel,show i+2-1=i+1 from by omega] at PreH1
  omega

theorem proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1 := by
  unfold solver_entail_wit_12_1
  right
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_entail_wit_12_1_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_1_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))

theorem proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1 := by
  unfold solver_entail_wit_12_2_split_goal_1
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  apply checked_swap_prefix_step values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i PreH15
  intro h
  rcases h with ⟨hp,hf,hx,hy,he⟩
  try rw [Znth_cons 0 i 0 values (by omega)] at PreH1
  try rw [Znth_cons 0 (i+1) 0 values (by omega)] at PreH1
  try simp only [Int.add_sub_cancel,show i+2-1=i+1 from by omega] at PreH1
  omega

theorem proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2 := by
  unfold solver_entail_wit_12_2
  right
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_entail_wit_12_2_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_2_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))

theorem proof_of_solver_entail_wit_12_3_split_goal_1 : solver_entail_wit_12_3_split_goal_1 := by
  unfold solver_entail_wit_12_3_split_goal_1
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  apply checked_swap_prefix_step values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i PreH16
  intro h
  rcases h with ⟨hp,hf,hx,hy,he⟩
  try rw [Znth_cons 0 i 0 values (by omega)] at PreH1
  try rw [Znth_cons 0 (i+1) 0 values (by omega)] at PreH1
  try simp only [Int.add_sub_cancel,show i+2-1=i+1 from by omega] at PreH1
  omega

theorem proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3 := by
  unfold solver_entail_wit_12_3
  right
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_entail_wit_12_3_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_3_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18))

theorem proof_of_solver_entail_wit_12_4_split_goal_1 : solver_entail_wit_12_4_split_goal_1 := by
  unfold solver_entail_wit_12_4_split_goal_1
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  apply checked_swap_prefix_step values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i PreH17
  intro h
  rcases h with ⟨hp,hf,hx,hy,he⟩
  try rw [Znth_cons 0 i 0 values (by omega)] at PreH1
  try rw [Znth_cons 0 (i+1) 0 values (by omega)] at PreH1
  try simp only [Int.add_sub_cancel,show i+2-1=i+1 from by omega] at PreH1
  omega

theorem proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4 := by
  unfold solver_entail_wit_12_4
  right
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_entail_wit_12_4_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_4_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))

theorem proof_of_solver_entail_wit_12_5_split_goal_1 : solver_entail_wit_12_5_split_goal_1 := by
  unfold solver_entail_wit_12_5_split_goal_1
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  apply checked_swap_prefix_step values pre_values_2 suf_values_2 okpre_values_2 oksuf_values_2 i PreH18
  intro h
  rcases h with ⟨hp,hf,hx,hy,he⟩
  try rw [Znth_cons 0 i 0 values (by omega)] at PreH1
  try rw [Znth_cons 0 (i+1) 0 values (by omega)] at PreH1
  try simp only [Int.add_sub_cancel,show i+2-1=i+1 from by omega] at PreH1
  omega

theorem proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5 := by
  unfold solver_entail_wit_12_5
  right
  intro n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  split_pure_spatial
  · cancel
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_entail_wit_12_5_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20) | (dump_pre_spatial; exact (proof_of_solver_entail_wit_12_5_split_goal_1 n_pre values oksuf_values_2 suf_values_2 okpre_values_2 pre_values_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20))

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  unfold solver_return_wit_1_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  dump_pre_spatial
  right
  refine ⟨rfl,?_⟩
  intro hc
  have hcases := (cleanable_residual_characterization__final_result values pre_values suf_values okpre_values oksuf_values (by omega) (by omega) (by omega) (by omega) PreH12 PreH13).mp hc
  rcases hcases with hd | ⟨j,hj,hs⟩
  · exact PreH14.1 hd
  · exact PreH14.2 j ⟨hj.1,by omega⟩ hs

theorem proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial := by
  unfold solver_return_wit_1_split_goal_spatial
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  sep_apply (int64Array.full_to_full_shape pre_pre (n_pre+1) pre_values)
  sep_apply (charArray.full_to_full_shape okpre_pre (n_pre+1) okpre_values)
  sep_apply (int64Array.seg_to_seg_shape suf_pre 1 (n_pre+2) suf_values)
  sep_apply (int64Array.seg_shape_merge_to_seg_shape suf_pre 0 1 (n_pre+2) (by omega))
  sep_apply (int64Array.seg_shape_to_full_shape suf_pre 0 (n_pre+2))
  sep_apply (charArray.seg_to_seg_shape oksuf_pre 1 (n_pre+2) oksuf_values)
  sep_apply (charArray.seg_shape_merge_to_seg_shape oksuf_pre 0 1 (n_pre+2) (by omega))
  sep_apply (charArray.seg_shape_to_full_shape oksuf_pre 0 (n_pre+2))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · exact proof_of_solver_return_wit_1_split_goal_spatial oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_return_wit_1_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16) | (dump_pre_spatial; exact (proof_of_solver_return_wit_1_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16))

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  unfold solver_return_wit_2_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dump_pre_spatial
  have hp : Znth (i-1) okpre_values 0 = 1 := by
    have hb := prefix_residual_flag_boolean values pre_values okpre_values (i-1) PreH17 ⟨by omega,by omega⟩
    omega
  have hf : Znth (i+1) oksuf_values 0 = 1 := by
    have hb := suffix_residual_flag_boolean values 1 suf_values oksuf_values (i+1) PreH18 ⟨by omega,by omega⟩
    have he : i+2-1=i+1 := by omega
    rw [he] at PreH4
    omega
  have hs : SwapResidualSuccess values pre_values suf_values okpre_values oksuf_values i := by
    simp only [Znth_cons 0 i 0 values (by omega),Znth_cons 0 (i+1) 0 values (by omega),Int.add_sub_cancel,show i+2-1=i+1 from by omega] at PreH1 PreH2 PreH3
    exact ⟨hp,hf,by omega,by omega,by convert PreH1 using 1 <;> congr 1 <;> omega⟩
  left
  refine ⟨rfl,?_⟩
  apply (cleanable_residual_characterization__final_result values pre_values suf_values okpre_values oksuf_values (by omega) (by omega) (by omega) (by omega) PreH17 PreH18).mpr
  exact Or.inr ⟨i,⟨by omega,by omega⟩,hs⟩

theorem proof_of_solver_return_wit_2_split_goal_spatial : solver_return_wit_2_split_goal_spatial := by
  unfold solver_return_wit_2_split_goal_spatial
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  sep_apply (int64Array.full_to_full_shape pre_pre (n_pre+1) pre_values)
  sep_apply (charArray.full_to_full_shape okpre_pre (n_pre+1) okpre_values)
  sep_apply (int64Array.seg_to_seg_shape suf_pre 1 (n_pre+2) suf_values)
  sep_apply (int64Array.seg_shape_merge_to_seg_shape suf_pre 0 1 (n_pre+2) (by omega))
  sep_apply (int64Array.seg_shape_to_full_shape suf_pre 0 (n_pre+2))
  sep_apply (charArray.seg_to_seg_shape oksuf_pre 1 (n_pre+2) oksuf_values)
  sep_apply (charArray.seg_shape_merge_to_seg_shape oksuf_pre 0 1 (n_pre+2) (by omega))
  sep_apply (charArray.seg_shape_to_full_shape oksuf_pre 0 (n_pre+2))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  unfold solver_return_wit_2
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · exact proof_of_solver_return_wit_2_split_goal_spatial oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_return_wit_2_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21) | (dump_pre_spatial; exact (proof_of_solver_return_wit_2_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  unfold solver_return_wit_3_split_goal_1
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  dump_pre_spatial
  have hi : i=0 := by omega
  have hp : Znth n_pre okpre_values 0=1 := by
    have hb := prefix_residual_flag_boolean values pre_values okpre_values n_pre PreH14 ⟨by omega,by omega⟩
    omega
  have hs : SuffixResidualState values 1 suf_values oksuf_values := by simpa only [hi,Int.zero_add] using PreH15
  left
  refine ⟨rfl,?_⟩
  apply (cleanable_residual_characterization__final_result values pre_values suf_values okpre_values oksuf_values (by omega) (by omega) (by omega) (by omega) PreH14 hs).mpr
  left
  change Znth (Zlength values) okpre_values 0=1 ∧ Znth (Zlength values) pre_values 0=0
  rw [← PreH6]
  exact ⟨hp,PreH1⟩

theorem proof_of_solver_return_wit_3_split_goal_spatial : solver_return_wit_3_split_goal_spatial := by
  unfold solver_return_wit_3_split_goal_spatial
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hi : i=0 := by omega
  rw [hi]
  simp only [Int.zero_add]
  sep_apply (int64Array.full_to_full_shape pre_pre (n_pre+1) pre_values)
  sep_apply (charArray.full_to_full_shape okpre_pre (n_pre+1) okpre_values)
  sep_apply (int64Array.seg_to_seg_shape suf_pre 1 (n_pre+2) suf_values)
  sep_apply (int64Array.seg_shape_merge_to_seg_shape suf_pre 0 1 (n_pre+2) (by omega))
  sep_apply (int64Array.seg_shape_to_full_shape suf_pre 0 (n_pre+2))
  sep_apply (charArray.seg_to_seg_shape oksuf_pre 1 (n_pre+2) oksuf_values)
  sep_apply (charArray.seg_shape_merge_to_seg_shape oksuf_pre 0 1 (n_pre+2) (by omega))
  sep_apply (charArray.seg_shape_to_full_shape oksuf_pre 0 (n_pre+2))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  unfold solver_return_wit_3
  right
  intro oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · exact proof_of_solver_return_wit_3_split_goal_spatial oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  · split_pures
    all_goals first
      | first | exact (proof_of_solver_return_wit_3_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17) | (dump_pre_spatial; exact (proof_of_solver_return_wit_3_split_goal_1 oksuf_pre okpre_pre suf_pre pre_pre n_pre values oksuf_values suf_values okpre_values pre_values i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17))

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_proof_manual
