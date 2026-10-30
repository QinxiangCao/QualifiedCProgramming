import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part1
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part2
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part3
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part4
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual_part5
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_goal
import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open stock_trading_goal stock_trading_lib StockProofInternal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
open stock_trading_proof_manual_part1
open stock_trading_proof_manual_part2
open stock_trading_proof_manual_part3
open stock_trading_proof_manual_part4
open stock_trading_proof_manual_part5

theorem proof_of_stock_init_storage_entail_wit_1 : stock_init_storage_entail_wit_1 := by
  right
  intro length_pre PreH1 PreH2
  split_pure_spatial
  · cancel
  · split_pures; dump_pre_spatial
    rfl

theorem proof_of_stock_init_storage_entail_wit_2 : stock_init_storage_entail_wit_2 := by
  right
  intro length_pre cells_2 index PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures; dump_pre_spatial
    simp only [Zlength_app,Zlength_cons,Zlength_nil]; omega

theorem proof_of_maximum_profit_entail_wit_4 : maximum_profit_entail_wit_4 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre dp_init queue_l_2 width q_init neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  split_pure_spatial
  · cancel
  · split_pures; dump_pre_spatial
    rw [Zlength_replace_Znth]; assumption

theorem proof_of_maximum_profit_entail_wit_1 : maximum_profit_entail_wit_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  sep_apply (intArray.undef_full_split_to_undef_seg (&("queue_index")) (max_stock_pre+1) 991 (by omega))
  sep_apply (intArray.undef_full_split_to_undef_seg (&("dp")) ((days_pre+1)*(max_stock_pre+1)) 982081 (by constructor <;> nlinarith))
  sep_apply (intArray.undef_seg_to_undef_full (&("queue_index")) 0 (max_stock_pre+1))
  sep_apply (intArray.undef_seg_to_undef_full (&("dp")) 0 ((days_pre+1)*(max_stock_pre+1)))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
  change l.getD i.toNat d ∈ l
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

private theorem annotation_row_length (rows : List (List Int)) (n m i : Int) (d : List Int)
    (hl : Zlength rows = n) (hs : Forall (Eq m) (rows.map StockRowLength)) (hi : 0 ≤ i ∧ i < n) :
    Zlength (Znth i rows d) = m := by
  have hm := nth_mem rows d i (by omega)
  exact (hs.mem (List.mem_map.mpr ⟨Znth i rows d,hm,rfl⟩)).symm

theorem proof_of_maximum_profit_entail_wit_5 : maximum_profit_entail_wit_5 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre dp_init queue_l_2 width q_init neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs : StockFillRows dp_init days_pre max_stock_pre 0 := by
    refine ⟨⟨by omega,by omega⟩,⟨PreH26,?_⟩,?_⟩
    · intro row hr
      exact annotation_row_length dp_init (days_pre+1) (max_stock_pre+1) row [] PreH26 PreH27 hr
    · intro row stock hr hstock; omega
  split_pure_spatial
  · cancel
  · split_pures; dump_pre_spatial; exact hs

theorem proof_of_maximum_profit_entail_wit_6 : maximum_profit_entail_wit_6 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hl := annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) i __default__List_Z PreH25 PreH26 (by omega)
  have hs : StockFillCells (Znth i dp_l_2 __default__List_Z) max_stock_pre i 0 := by
    refine ⟨⟨by omega,by omega⟩,hl,?_⟩
    intro stock hstock; omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

private theorem forall_of_nth {A : Type} (P : A → Prop) (l : List A) (d : A)
    (h : ∀ i, (0 ≤ i ∧ i < Zlength l) → P (Znth i l d)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hp := h (i : Int) ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he] using hp

private theorem shape_annotation (rows : List (List Int)) (days stocks : Int) (h : StockTableShape rows days stocks) :
    Forall (Eq (stocks+1)) (rows.map StockRowLength) := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hx
  have hh : Forall (fun row => Zlength row = stocks+1) rows := by
    apply forall_of_nth _ rows []
    intro i hi
    exact h.2 i (by rw [h.1] at hi; exact hi)
  exact (hh.mem hr).symm

theorem proof_of_maximum_profit_entail_wit_7_1 : maximum_profit_entail_wit_7_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hv : (0 : Int) = StockInitialCell i j := by
    simp [StockInitialCell, show i = 0 by omega, show j = 0 by omega]
  obtain ⟨hr,hc⟩ := stock_fill_update_step__init_copy dp_l_2 days_pre max_stock_pre i j (0 : Int) __default__List_Z PreH29 PreH30 (by omega) (by omega) hv
  have ha := shape_annotation (replace_Znth i (replace_Znth j (0 : Int) (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hr.2.1
  have hlen := hr.2.1.1
  have hrowlen := hc.2.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j (0 : Int) dp_l_2 __default__List_Z (by omega) (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth i (replace_Znth j (0 : Int) (Znth i dp_l_2 __default__List_Z)) dp_l_2) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_7_2 : maximum_profit_entail_wit_7_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hv : neg_inf = StockInitialCell i j := by
    simp [StockInitialCell, show i ≠ 0 by omega, STOCK_NEG_INF]; omega
  obtain ⟨hr,hc⟩ := stock_fill_update_step__init_copy dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z PreH28 PreH29 (by omega) (by omega) hv
  have ha := shape_annotation (replace_Znth i (replace_Znth j neg_inf (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hr.2.1
  have hlen := hr.2.1.1
  have hrowlen := hc.2.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j neg_inf dp_l_2 __default__List_Z (by omega) (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth i (replace_Znth j neg_inf (Znth i dp_l_2 __default__List_Z)) dp_l_2) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_7_3 : maximum_profit_entail_wit_7_3 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have hv : neg_inf = StockInitialCell i j := by
    simp [StockInitialCell, show i = 0 by omega, show j ≠ 0 by omega, STOCK_NEG_INF]; omega
  obtain ⟨hr,hc⟩ := stock_fill_update_step__init_copy dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z PreH29 PreH30 (by omega) (by omega) hv
  have ha := shape_annotation (replace_Znth i (replace_Znth j neg_inf (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hr.2.1
  have hlen := hr.2.1.1
  have hrowlen := hc.2.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j neg_inf dp_l_2 __default__List_Z (by omega) (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth i (replace_Znth j neg_inf (Znth i dp_l_2 __default__List_Z)) dp_l_2) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_maximum_profit_entail_wit_8 : maximum_profit_entail_wit_8 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hs : StockFillRows dp_l_2 days_pre max_stock_pre (i+1) := by
    refine ⟨⟨by omega,by omega⟩,PreH25.2.1,?_⟩
    intro row stock hr hstock
    by_cases hri : row < i
    · exact PreH25.2.2 row stock (by omega) hstock
    · have he : row=i := by omega
      subst row
      rw [same_index_different_default i dp_l_2 __default__List_Z (by omega)]
      exact ⟨PreH26.2.1, PreH26.2.2 stock (by omega)⟩
  split_pure_spatial
  · cancel
  · split_pures; dump_pre_spatial; exact hs

theorem proof_of_maximum_profit_entail_wit_10 : maximum_profit_entail_wit_10 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hs : StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i 0 := by
    refine ⟨PreH23,by omega,by omega,?_⟩
    intro stock hstock; omega
  split_pure_spatial
  · cancel
  · split_pures; dump_pre_spatial; exact hs

theorem proof_of_maximum_profit_entail_wit_11 : maximum_profit_entail_wit_11 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width (i-1) j dp_l __default__List_Z (by omega) (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) dp_l ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg

private theorem flat_to_rows_rec (k : Nat) (x lo m : Int) (l : List Int) (hm : 0 ≤ m) :
    intArray.seg x (lo*m) ((lo+(k : Int))*m) l |--
    EX rows : List (List Int),
      “(Zlength rows = (k : Int) ∧ Forall (fun row => Zlength row = m) rows)” &&
      store_array_rec naive_C_Rules (intArray2.row_store m) x lo (lo+(k : Int)) rows := by
  induction k generalizing lo l with
  | zero =>
    simp only [Nat.cast_zero,Int.add_zero]
    prop_apply (intArray.seg_Zlength x (lo*m) (lo*m) l)
    Intros_p hl
    have he : l=[] := by
      apply List.length_eq_zero_iff.mp
      change (l.length : Int) = lo*m-lo*m at hl
      omega
    subst l
    sep_apply (intArray.seg_empty x (lo*m) (lo*m))
    Intros
    refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List (List Int)) ?_
    simp only [store_array_rec]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first | rfl | trivial | exact ⟨rfl,Forall.nil⟩
  | succ k ih =>
    have he : lo + ((k+1 : Nat) : Int) = (lo+1)+(k : Int) := by omega
    rw [he]
    sep_apply (intArray.seg_split_to_seg x (lo*m) ((lo+1)*m) (((lo+1)+(k : Int))*m) l (by constructor <;> nlinarith))
    sep_apply (ih (lo+1) (sublist ((lo+1)*m-lo*m) (((lo+1)+(k : Int))*m-lo*m) l))
    Intros rows
    have hrows : Zlength rows = (k : Int) ∧ Forall (fun row => Zlength row = m) rows := by first | assumption | exact ⟨by assumption,by assumption⟩
    change (store_array_rec naive_C_Rules (intArray2.row_store m) x (lo+1) (lo+1+(k : Int)) rows **
      intArray.seg x (lo*m) ((lo+1)*m) (sublist 0 ((lo+1)*m-lo*m) l)) |-- _
    refine naive_C_Rules.toContext.derivable1_trans _
      (store_array_rec naive_C_Rules (intArray2.row_store m) x (lo+1) (lo+1+(k : Int)) rows **
        intArray.full (x+lo*m*sizeof(INT)) ((lo+1)*m-lo*m) (sublist 0 ((lo+1)*m-lo*m) l)) _ ?_ ?_
    · apply naive_C_Rules.toContext.derivable1_sepcon_mono
      · exact naive_C_Rules.toContext.derivable1_refl _
      · exact intArray.seg_to_full x (lo*m) ((lo+1)*m) (sublist 0 ((lo+1)*m-lo*m) l)
    · have hd : (lo+1)*m-lo*m=m := by ring
      rw [hd]
      prop_apply (intArray.full_Zlength (x+lo*m*sizeof(INT)) m (sublist 0 m l))
      Intros_p hlen
      refine Automation.exp_right_rule (CRules := naive_C_Rules) ((sublist 0 m l)::rows) ?_
      simp only [store_array_rec,SimpleC.SL.Array2LibCore.Array2LibCoreSig.Array2Lib.row_store,SimpleC.SL.Array2LibCore.Array2LibCoreSig.Array2Lib.row_addr]
      split_pure_spatial
      · cancel
        exact naive_C_Rules.toContext.derivable1_refl _
      · split_pures <;> dump_pre_spatial
        exact ⟨by simp only [Zlength_cons]; omega, Forall.cons hlen hrows.2⟩

private theorem flat_to_rows (x n m : Int) (l : List Int) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    intArray.full x (n*m) l |--
    EX rows : List (List Int),
      “(Zlength rows = n ∧ Forall (fun row => Zlength row = m) rows)” && intArray2.full x n m rows := by
  sep_apply (intArray.full_to_seg x (n*m) l)
  have hr := flat_to_rows_rec n.toNat x 0 m l hm
  simp only [Int.toNat_of_nonneg hn,Int.zero_mul,Int.zero_add] at hr
  sep_apply hr
  Intros rows
  have hrows : Zlength rows = n ∧ Forall (fun row => Zlength row = m) rows := by first | assumption | exact ⟨by assumption,by assumption⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) rows ?_
  change _ |-- “(Zlength rows = n ∧ Forall (fun row => Zlength row = m) rows)” && store_array_rec naive_C_Rules (intArray2.row_store m) x 0 n rows
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hrows | exact hrows.1 | exact hrows.2

theorem proof_of_maximum_profit_entail_wit_2 : maximum_profit_entail_wit_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre cells cells_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  simp only [Int.zero_mul,Int.add_zero]
  sep_apply (flat_to_rows (&("dp")) (days_pre+1) (max_stock_pre+1) cells_2 (by omega) (by omega))
  Intros rows
  have hrows : Zlength rows = days_pre+1 ∧ Forall (fun row => Zlength row = max_stock_pre+1) rows := by first | assumption | exact ⟨by assumption,by assumption⟩
  have hlen := hrows.1
  have hf : Forall (Eq (max_stock_pre+1)) (rows.map StockRowLength) := by
    apply Forall.iff_forall_mem.mpr
    intro z hz
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hz
    exact (hrows.2.mem hr).symm
  refine Automation.exp_right_rule (CRules := naive_C_Rules) rows ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cells ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals assumption

private theorem annotation_inputs (ask bid buy sell : List Int) (days stocks : Int)
    (ha : Zlength ask=days) (hb : Zlength bid=days) (hu : Zlength buy=days) (hs : Zlength sell=days)
    (hd : 1 ≤ days ∧ days ≤ 990) (hst : 1 ≤ stocks ∧ stocks ≤ 990)
    (hbid : Forall (fun x => 1 ≤ x) bid) (hask : Forall (fun x => x ≤ 1000) ask)
    (hpair : Forall2 (LE.le (α := Int)) bid ask)
    (hbuylo : Forall (fun x => 1 ≤ x) buy) (hbuyhi : Forall (fun x => x ≤ stocks) buy)
    (hselllo : Forall (fun x => 1 ≤ x) sell) (hsellhi : Forall (fun x => x ≤ stocks) sell) :
    StockInputsBounded ask bid buy sell days stocks := by
  refine ⟨ha,hb,hu,hs,hd,hst,?_⟩
  intro day hday
  have hbm := nth_mem bid 0 (day-1) (by omega)
  have ham := nth_mem ask 0 (day-1) (by omega)
  have hum := nth_mem buy 0 (day-1) (by omega)
  have hsm := nth_mem sell 0 (day-1) (by omega)
  have hp := (AUXLib.Forall2_nth_iff Int Int (LE.le (α := Int)) bid ask 0 0).mp hpair
  have hn : (day-1).toNat < bid.length := by change (bid.length : Int)=days at hb; omega
  have horder := hp.2 (day-1).toNat hn
  exact ⟨⟨hbid.mem hbm,horder⟩,hask.mem ham,⟨hbuylo.mem hum,hbuyhi.mem hum⟩,⟨hselllo.mem hsm,hsellhi.mem hsm⟩⟩

private theorem table_bound_annotations (rows : List (List Int)) (days stocks : Int)
    (hs : StockTableShape rows days stocks) (hb : StockTableValuesBounded rows days stocks) :
    Forall (Forall (fun x => -1000000000 ≤ x)) rows ∧ Forall (Forall (fun x => x ≤ 1000000000)) rows := by
  constructor
  · apply forall_of_nth _ rows []
    intro r hr
    have hrr : 0 ≤ r ∧ r < days+1 := by rw [hs.1] at hr; exact hr
    apply forall_of_nth _ (Znth r rows []) 0
    intro c hc
    exact (hb r c hrr (by rw [hs.2 r hrr] at hc; exact hc)).1
  · apply forall_of_nth _ rows []
    intro r hr
    have hrr : 0 ≤ r ∧ r < days+1 := by rw [hs.1] at hr; exact hr
    apply forall_of_nth _ (Znth r rows []) 0
    intro c hc
    exact (hb r c hrr (by rw [hs.2 r hrr] at hc; exact hc)).2

theorem proof_of_maximum_profit_entail_wit_9 : maximum_profit_entail_wit_9 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH12 PreH13 PreH14 PreH15 (by omega) (by omega) PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he : i=days_pre+1 := by omega
  rw [he] at PreH23
  have hd := (stock_completed_initial_table_days_done__init_copy ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre (by omega) hi PreH23).1
  have hb := table_bound_annotations dp_l_2 (Zlength ap_l) max_stock_pre hd.1 hd.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hb.1 | exact hb.2 | exact hd

theorem proof_of_maximum_profit_entail_wit_12 : maximum_profit_entail_wit_12 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i j previous_value __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hshapeA := PreH28.1.1
  have hprev : 0 ≤ i-1 ∧ i-1 < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hv : previous_value = Znth j (Znth (i-1) dp_l_2 []) 0 := by
    rw [← Znth_indep dp_l_2 (i-1) __default__List_Z [] hprev]
    exact PreH16
  obtain ⟨hcopy,hshape⟩ := stock_copy_update_step__init_copy ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j previous_value hshapeA PreH28 hv (by omega) (by omega) (by omega)
  rw [← Znth_indep dp_l_2 i __default__List_Z [] hcur] at hcopy hshape
  have hb := table_bound_annotations _ (Zlength ap_l) max_stock_pre hcopy.1.1 hcopy.1.2.1
  rw [PreH17] at hshape
  have ha := shape_annotation _ days_pre max_stock_pre hshape
  have hlen := hshape.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j previous_value dp_l_2 __default__List_Z (by omega) (by omega))
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth i (replace_Znth j previous_value (Znth i dp_l_2 __default__List_Z)) dp_l_2) ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact hb.1 | exact hb.2 | omega

theorem proof_of_maximum_profit_entail_wit_13 : maximum_profit_entail_wit_13 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH15 PreH16 PreH17 PreH18 (by omega) (by omega) PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hdaily := hi.2.2.2.2.2.2 i (by omega)
  have hs : StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i 1 := by
    rcases PreH26 with ⟨HD, Hi, Hcol, Hcopy⟩
    refine ⟨HD, Hi, by omega, Hcopy 0 (by omega), ?_⟩
    intro stock hstock
    simp only [if_neg (show ¬ stock < 1 by omega)]
    exact Hcopy stock (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hs | omega

theorem proof_of_maximum_profit_entail_wit_14_1 : maximum_profit_entail_wit_14_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j ask_price buy_cap i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH24 PreH25 PreH26 PreH27 (by omega) (by omega) PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hlen := PreH40
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hc := PreH35.2.2.2.2 j (by omega)
  simp only [if_neg (show ¬ j < j by omega)] at hc
  have hmax : (-j*ask_price) = max (Znth j (Znth (i-1) dp_l_2 []) 0) (-j*Znth (i-1) ap_l 0) := by
    rw [he] at PreH3
    rw [← hc, ← PreH17]
    exact (Int.max_eq_right (by omega)).symm
  have hstep := stock_early_buy_update_step__early_buy ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j (-j*ask_price) days_pre hi PreH35 (by omega) (by omega) hmax
  obtain ⟨hp,hs⟩ := hstep
  rw [← he] at hp hs
  have hb := table_bound_annotations _ (Zlength ap_l) max_stock_pre hp.1.1 hp.1.2.1
  have ha := shape_annotation _ days_pre max_stock_pre hs
  have hlenNew := hs.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j (-j*ask_price) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists (replace_Znth i (replace_Znth j (-j*ask_price) (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact hb.1 | exact hb.2 | omega

theorem proof_of_maximum_profit_entail_wit_14_2 : maximum_profit_entail_wit_14_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j ask_price buy_cap i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH24 PreH25 PreH26 PreH27 (by omega) (by omega) PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have hlen := PreH40
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hc := PreH35.2.2.2.2 j (by omega)
  simp only [if_neg (show ¬ j < j by omega)] at hc
  have hmax : (Znth j (Znth i dp_l_2 __default__List_Z) 0) = max (Znth j (Znth (i-1) dp_l_2 []) 0) (-j*Znth (i-1) ap_l 0) := by
    rw [he] at PreH3
    rw [← hc, ← PreH17]
    rw [he]; exact (Int.max_eq_left (by omega)).symm
  have hstep := stock_early_buy_update_step__early_buy ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j (Znth j (Znth i dp_l_2 __default__List_Z) 0) days_pre hi PreH35 (by omega) (by omega) hmax
  obtain ⟨hp,hs⟩ := hstep
  rw [← he] at hp hs
  have hb := table_bound_annotations _ (Zlength ap_l) max_stock_pre hp.1.1 hp.1.2.1
  have ha := shape_annotation _ days_pre max_stock_pre hs
  have hlenNew := hs.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j (Znth j (Znth i dp_l_2 __default__List_Z) 0) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists (replace_Znth i (replace_Znth j (Znth j (Znth i dp_l_2 __default__List_Z) 0) (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact hb.1 | exact hb.2 | omega

theorem proof_of_maximum_profit_entail_wit_15 : maximum_profit_entail_wit_15 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH15 PreH16 PreH17 PreH18 (by omega) (by omega) PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH30,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH30 PreH31 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_15_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 j i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_15_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_15_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_15_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_15_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_15_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 j i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_16 : maximum_profit_entail_wit_16 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH46,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH46 PreH47 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_16_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_17 : maximum_profit_entail_wit_17 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH47,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH47 PreH48 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_17_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_18_1 : maximum_profit_entail_wit_18_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH46,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH46 PreH47 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_18_1_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_18_2 : maximum_profit_entail_wit_18_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH47,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH47 PreH48 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_18_2_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_18_2_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 bid_price tail head sell_cap j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

private theorem sublist_bound_annotations (q : List Int) (head tail bound : Int)
    (hh : 0 ≤ head ∧ head ≤ tail) (ht : tail ≤ Zlength q)
    (hb : ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q 0 ∧ Znth pos q 0 ≤ bound) :
    Forall (fun x : Int => 0 ≤ x) (sublist head tail q) ∧
    Forall (fun x : Int => x ≤ bound) (sublist head tail q) := by
  have hl : Zlength (sublist head tail q) = tail-head := by
    simp only [Zlength, sublist_length head tail q hh ht, Int.ofNat_eq_coe]
    omega
  constructor
  all_goals
    apply forall_of_nth _ _ 0
    intro i hi
    rw [Znth_sublist 0 head i tail q hh.1 (by omega)]
    have := hb (i+head) (by omega)
    omega

theorem proof_of_maximum_profit_entail_wit_19_1 : maximum_profit_entail_wit_19_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hs : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  have hlen := hs.1
  have hrow := hs.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j+1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH4
    unfold STOCK_NEG_INF
    omega
  have hq : StockSellQueue dp_l queue_l source_day bid_price ((j+1)+1) (j+sell_cap) head tail := by
    simpa only [show j+1+1=j+2 by omega] using PreH42
  have hp := StockSellQueue_begin_popping__sell_pop_append dp_l queue_l source_day bid_price (j+1) (j+sell_cap) head tail (by omega) (by omega) hn hq
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail) : 0 ≤ Znth pos queue_l 0 ∧ Znth pos queue_l 0 ≤ max_stock_pre := by
    have helem := PreH42.2.1 pos hpos
    rcases helem with ⟨h0,hl,hv,hr⟩
    omega
  have hlast := hb (tail-1) (by omega)
  have hqa := sublist_bound_annotations queue_l head tail max_stock_pre (by omega) (by omega) hb
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day (j+1) dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact hqa.1 | exact hqa.2 | rfl | omega | (intro h; first | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_19_2 : maximum_profit_entail_wit_19_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hs : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  have hlen := hs.1
  have hrow := hs.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j+1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH4
    unfold STOCK_NEG_INF
    omega
  have hq : StockSellQueue dp_l queue_l_2 source_day bid_price ((j+1)+1) (j+sell_cap) head tail := by
    simpa only [show j+1+1=j+2 by omega] using PreH42
  have hp := StockSellQueue_begin_popping__sell_pop_append dp_l queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail (by omega) (by omega) hn hq
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail) : 0 ≤ Znth pos queue_l_2 0 ∧ Znth pos queue_l_2 0 ≤ max_stock_pre := by
    have helem := PreH42.2.1 pos hpos
    rcases helem with ⟨h0,hl,hv,hr⟩
    omega

  have hqa := sublist_bound_annotations queue_l_2 head tail max_stock_pre (by omega) (by omega) hb
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day (j+1) dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact hqa.1 | exact hqa.2 | rfl | omega | (intro h; first | trivial | rfl | omega)

private theorem sublist_bound_lookup (q : List Int) (head tail bound : Int)
    (hh : 0 ≤ head ∧ head ≤ tail) (ht : tail ≤ Zlength q)
    (hlo : Forall (fun x : Int => 0 ≤ x) (sublist head tail q))
    (hhi : Forall (fun x : Int => x ≤ bound) (sublist head tail q)) :
    ∀ pos, head ≤ pos ∧ pos < tail → 0 ≤ Znth pos q 0 ∧ Znth pos q 0 ≤ bound := by
  have hl : Zlength (sublist head tail q) = tail-head := by
    simp only [Zlength, sublist_length head tail q hh ht, Int.ofNat_eq_coe]; omega
  intro pos hp
  have hm := nth_mem (sublist head tail q) 0 (pos-head) (by omega)
  have h : 0 ≤ Znth (pos-head) (sublist head tail q) 0 ∧ Znth (pos-head) (sublist head tail q) 0 ≤ bound := ⟨hlo.mem hm,hhi.mem hm⟩
  simpa only [Znth_sublist 0 head (pos-head) tail q hh.1 (by omega),Int.sub_add_cancel] using h

theorem proof_of_maximum_profit_entail_wit_20_1 : maximum_profit_entail_wit_20_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have oldbounds := sublist_bound_lookup queue_l_2 head tail max_stock_pre (by omega) (by omega) PreH44 PreH45
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH54,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH54 PreH55 hr⟩
  have hlen := oldshape.1
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockSellScore dp_l_2 source_day bid_price (Znth (tail-1) queue_l_2 0) ≤ StockSellScore dp_l_2 source_day bid_price (j+1) := by
    unfold StockSellScore
    rw [← PreH30 (by omega), ← he]
    omega
  have hp := StockSellQueuePopping_drop_tail__sell_pop_append dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail PreH43 (by omega) hscore
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail-1) := oldbounds pos (show head ≤ pos ∧ pos < tail by omega)
  have hlast := hb (tail-1-1) (by omega)
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  have hqa := sublist_bound_annotations queue_l_2 head (tail-1) max_stock_pre (by omega) (by omega) hb
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega) | exact hqa.1 | exact hqa.2

theorem proof_of_maximum_profit_entail_wit_20_2 : maximum_profit_entail_wit_20_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have oldbounds := sublist_bound_lookup queue_l_2 head tail max_stock_pre (by omega) (by omega) PreH44 PreH45
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH54,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH54 PreH55 hr⟩
  have hlen := oldshape.1
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockSellScore dp_l_2 source_day bid_price (Znth (tail-1) queue_l_2 0) ≤ StockSellScore dp_l_2 source_day bid_price (j+1) := by
    unfold StockSellScore
    rw [← PreH30 (by omega), ← he]
    omega
  have hp := StockSellQueuePopping_drop_tail__sell_pop_append dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail PreH43 (by omega) hscore
  have hb (pos : Int) (hpos : head ≤ pos ∧ pos < tail-1) := oldbounds pos (show head ≤ pos ∧ pos < tail by omega)

  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  have hqa := sublist_bound_annotations queue_l_2 head (tail-1) max_stock_pre (by omega) (by omega) hb
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega) | exact hqa.1 | exact hqa.2

theorem proof_of_maximum_profit_entail_wit_21_1 : maximum_profit_entail_wit_21_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hqlen : Zlength queue_l_2=width := by omega
  have hp : StockSellQueuePending dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail := by
    refine ⟨PreH39, by omega, ?_⟩
    intro hh
    omega
  have hsell : 1 ≤ sell_cap := by
    have hm := nth_mem sell_l 0 (i-1) (by omega)
    have hv := PreH36.mem hm
    omega
  have hqueue := StockSellQueuePending_append__sell_pop_append dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail (by omega) hp
  have hnewlen := Zlength_replace_Znth queue_l_2 tail (j+1)
  rw [PreH46] at hqueue
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_21_2 : maximum_profit_entail_wit_21_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH53,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH53 PreH54 hr⟩
  have hqlen : Zlength queue_l_2=width := by omega
  have hp : StockSellQueuePending dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail := by
    refine ⟨PreH42, by omega, ?_⟩
    intro hh
    have hlen := oldshape.1
    have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
    unfold StockSellScore
    rw [← PreH29 hh, ← he]
    omega
  have hsell : 1 ≤ sell_cap := by
    have hm := nth_mem sell_l 0 (i-1) (by omega)
    have hv := PreH39.mem hm
    omega
  have hqueue := StockSellQueuePending_append__sell_pop_append dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail (by omega) hp
  have hnewlen := Zlength_replace_Znth queue_l_2 tail (j+1)
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_22_2 : maximum_profit_entail_wit_22_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  have hlen := oldshape.1
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hn : Znth (j+1) (Znth source_day dp_l_2 []) 0 = STOCK_NEG_INF := by
    rw [he] at PreH3
    unfold STOCK_NEG_INF
    omega
  have hp := stock_sell_queue_extend_lower_neg_inf__sell_cell_progress dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail hn (by simpa only [show j+1+1=j+2 by omega] using PreH41)
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day (j+1) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (intro h; first | assumption | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_24 : maximum_profit_entail_wit_24 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day best_index dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (intro h; first | assumption | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_23 : maximum_profit_entail_wit_23 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH22 PreH23 PreH24 PreH25 (by omega) (by omega) PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH43,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH43 PreH44 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_24_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_24_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_24_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_24_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_25_3 : maximum_profit_entail_wit_25_3 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH22 PreH23 PreH24 PreH25 (by omega) (by omega) PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH43,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH43 PreH44 hr⟩
  rw [← PreH39]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_7 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_26_3_split_goal_8 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_26 : maximum_profit_entail_wit_26 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH46,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH46 PreH47 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_27_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_27_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_27_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_27_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_27_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_27_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_27 : maximum_profit_entail_wit_27 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH25 PreH26 PreH27 PreH28 (by omega) (by omega) PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH47,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH47 PreH48 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_28_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_28_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_28_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_28 : maximum_profit_entail_wit_28 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH30 PreH31 PreH32 PreH33 (by omega) (by omega) PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_29_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_29_1 : maximum_profit_entail_wit_29_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH29 PreH30 PreH31 PreH32 (by omega) (by omega) PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH48,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH48 PreH49 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_30_1_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_29_2 : maximum_profit_entail_wit_29_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH30 PreH31 PreH32 PreH33 (by omega) (by omega) PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_30_2_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_30_1 : maximum_profit_entail_wit_30_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have oldshape : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH51,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH51 PreH52 hr⟩
  have hlen := oldshape.1
  have hrow := oldshape.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j-1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH4
    unfold STOCK_NEG_INF
    omega
  have hq : StockBuyQueue dp_l queue_l source_day ask_price (j-buy_cap) ((j-1)-1) head tail := by
    simpa only [show j-1-1=j-2 by omega] using PreH42
  have hp := StockBuyQueue_begin_popping__buy_pop_append dp_l queue_l source_day ask_price (j-buy_cap) (j-1) head tail (by omega) (by omega) hn hq
  have hlast := PreH42.2.1 (tail-1) (by omega)
  rcases hlast with ⟨hl0,hll,hlv,hlr⟩
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day (j-1) dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_30_2 : maximum_profit_entail_wit_30_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have oldshape : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH51,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH51 PreH52 hr⟩
  have hlen := oldshape.1
  have hrow := oldshape.2 source_day (by omega)
  have he := Znth_indep dp_l source_day __default__List_Z [] (by omega)
  have hn : Znth (j-1) (Znth source_day dp_l []) 0 ≠ STOCK_NEG_INF := by
    rw [he] at PreH4
    unfold STOCK_NEG_INF
    omega
  have hq : StockBuyQueue dp_l queue_l_2 source_day ask_price (j-buy_cap) ((j-1)-1) head tail := by
    simpa only [show j-1-1=j-2 by omega] using PreH42
  have hp := StockBuyQueue_begin_popping__buy_pop_append dp_l queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail (by omega) (by omega) hn hq
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day (j-1) dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_31_1 : maximum_profit_entail_wit_31_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH54,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH54 PreH55 hr⟩
  have hlen := oldshape.1
  have hrow := oldshape.2 source_day (by omega)
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockBuyScore dp_l_2 source_day ask_price (Znth (tail-1) queue_l_2 0) ≤ StockBuyScore dp_l_2 source_day ask_price (j-1) := by
    unfold StockBuyScore
    rw [← PreH32 (by omega), ← he]
    omega
  have hp := StockBuyQueuePopping_drop_tail__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail PreH45 (by omega) hscore
  have hlast := PreH45.2.2.1 (tail-1-1) (by omega)
  rcases hlast with ⟨hl0,hll,hlv,hlr⟩
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_31_2 : maximum_profit_entail_wit_31_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH54,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH54 PreH55 hr⟩
  have hlen := oldshape.1
  have hrow := oldshape.2 source_day (by omega)
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hscore : StockBuyScore dp_l_2 source_day ask_price (Znth (tail-1) queue_l_2 0) ≤ StockBuyScore dp_l_2 source_day ask_price (j-1) := by
    unfold StockBuyScore
    rw [← PreH32 (by omega), ← he]
    omega
  have hp := StockBuyQueuePopping_drop_tail__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail PreH45 (by omega) hscore
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_32_1 : maximum_profit_entail_wit_32_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have hqlen : Zlength queue_l_2=width := by omega
  have hp : StockBuyQueuePending dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail := by
    refine ⟨PreH41, by omega, ?_⟩
    intro hh
    omega
  have hbuy : 1 ≤ buy_cap := by
    have hm := nth_mem buy_l 0 (i-1) (by omega)
    have hv := PreH36.mem hm
    omega
  have hqueue := StockBuyQueuePending_append__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail hp (by omega)
  have hnewlen := Zlength_replace_Znth queue_l_2 tail (j-1)
  rw [PreH46] at hqueue
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_32_2 : maximum_profit_entail_wit_32_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH53,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH53 PreH54 hr⟩
  have hqlen : Zlength queue_l_2=width := by omega
  have hp : StockBuyQueuePending dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail := by
    refine ⟨PreH44, by omega, ?_⟩
    intro hh
    have hlen := oldshape.1
    have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
    unfold StockBuyScore
    rw [← PreH31 hh, ← he]
    omega
  have hbuy : 1 ≤ buy_cap := by
    have hm := nth_mem buy_l 0 (i-1) (by omega)
    have hv := PreH39.mem hm
    omega
  have hqueue := StockBuyQueuePending_append__buy_pop_append dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail hp (by omega)
  have hnewlen := Zlength_replace_Znth queue_l_2 tail (j-1)
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day last_index dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)

theorem proof_of_maximum_profit_entail_wit_33_2 : maximum_profit_entail_wit_33_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have oldshape : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  have hlen := oldshape.1
  have hrow := oldshape.2 source_day (by omega)
  have he := Znth_indep dp_l_2 source_day __default__List_Z [] (by omega)
  have hn : Znth (j-1) (Znth source_day dp_l_2 []) 0 = STOCK_NEG_INF := by
    rw [he] at PreH3
    unfold STOCK_NEG_INF
    omega
  have hp := StockBuyQueue_extend_invalid__buy_cell_progress dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail (by simpa only [show j-1-1=j-2 by omega] using PreH41) (by omega) hn
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day (j-1) dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | (intro h; first | assumption | trivial | rfl | omega)


private theorem product_bounds (x p : Int) (hx : 0 ≤ x ∧ x ≤ 990)
    (hp : 0 ≤ p ∧ p ≤ 1000) : 0 ≤ x*p ∧ x*p ≤ 990000 :=
  ⟨Int.mul_nonneg hx.1 hp.1, Int.mul_le_mul hx.2 hp.2 hp.1 (by omega)⟩

theorem proof_of_maximum_profit_safety_wit_70 : maximum_profit_safety_wit_70 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l bid_price tail head sell_cap j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47
  split_pures
  all_goals
    rcases PreH39 with hqueue | hqueue
    all_goals
      have he := hqueue.2.1 head (by omega)
      have hi := he.2.2.2
      dump_pre_spatial
      simp only [INT_MAX, INT_MIN]
      omega

theorem proof_of_maximum_profit_safety_wit_80 : maximum_profit_safety_wit_80 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have old_PreH28 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have old_PreH31 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH48,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH48 PreH49 hr⟩
  split_pures
  all_goals
    have Hdone := PreH39.1
    have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j + 1) __default__List_Z old_PreH28 Hdone old_PreH31 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds (j + 1) bid_price (by omega) (by omega)
    have hjprod := product_bounds j bid_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_88 : maximum_profit_safety_wit_88 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have old_PreH28 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have old_PreH31 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH48,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH48 PreH49 hr⟩
  split_pures
  all_goals
    have Hdone := PreH39.1
    have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j + 1) __default__List_Z old_PreH28 Hdone old_PreH31 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds (j + 1) bid_price (by omega) (by omega)
    have hjprod := product_bounds j bid_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_96 : maximum_profit_safety_wit_96 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l incoming_score last_index tail head sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have old_PreH27 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have old_PreH31 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  split_pures
  all_goals
    have Hdone := PreH38.1
    have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day last_index __default__List_Z old_PreH27 Hdone old_PreH31 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds last_index bid_price (by omega) (by omega)
    have hjprod := product_bounds j bid_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_109 : maximum_profit_safety_wit_109 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have old_PreH26 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH26 PreH27 PreH28 PreH29 (by omega) (by omega) PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have old_PreH29 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH48,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH48 PreH49 hr⟩
  split_pures
  all_goals
    have Hdone := PreH37.1
    have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z old_PreH26 Hdone old_PreH29 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds best_index bid_price (by omega) (by omega)
    have hjprod := product_bounds j bid_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_111 : maximum_profit_safety_wit_111 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have old_PreH26 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH26 PreH27 PreH28 PreH29 (by omega) (by omega) PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36
  have old_PreH29 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH48,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH48 PreH49 hr⟩
  split_pures
  all_goals
    have Hdone := PreH37.1
    have Hcell := StockDaysDone_cell_bounded__safety_sell ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z old_PreH26 Hdone old_PreH29 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds best_index bid_price (by omega) (by omega)
    have hjprod := product_bounds j bid_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_129 : maximum_profit_safety_wit_129 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l tail head buy_cap ask_price sell_cap bid_price j source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  split_pures
  all_goals
    rcases PreH41 with hqueue | hqueue
    all_goals
      have he := hqueue.2.1 head (by omega)
      have hi := he.2.2.2
      dump_pre_spatial
      simp only [INT_MAX, INT_MIN]
      omega

theorem proof_of_maximum_profit_safety_wit_139 : maximum_profit_safety_wit_139 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have old_PreH28 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have old_PreH31 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  split_pures
  all_goals
    have Hdone := PreH39.1
    have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j - 1) __default__List_Z old_PreH28 Hdone old_PreH31 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds (j - 1) ask_price (by omega) (by omega)
    have hjprod := product_bounds j ask_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_147 : maximum_profit_safety_wit_147 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have old_PreH28 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have old_PreH31 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  split_pures
  all_goals
    have Hdone := PreH39.1
    have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day (j - 1) __default__List_Z old_PreH28 Hdone old_PreH31 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds (j - 1) ask_price (by omega) (by omega)
    have hjprod := product_bounds j ask_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_155 : maximum_profit_safety_wit_155 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l incoming_score last_index tail head buy_cap ask_price sell_cap bid_price source_day j i width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have old_PreH29 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH29 PreH30 PreH31 PreH32 (by omega) (by omega) PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have old_PreH32 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  split_pures
  all_goals
    have Hdone := PreH40.1
    have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day last_index __default__List_Z old_PreH29 Hdone old_PreH32 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds last_index ask_price (by omega) (by omega)
    have hjprod := product_bounds j ask_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_168 : maximum_profit_safety_wit_168 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have old_PreH27 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have old_PreH30 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  split_pures
  all_goals
    have Hdone := PreH38.1
    have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z old_PreH27 Hdone old_PreH30 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds best_index ask_price (by omega) (by omega)
    have hjprod := product_bounds j ask_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_safety_wit_170 : maximum_profit_safety_wit_170 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre ap_pre bp_pre buy_limit_pre sell_limit_pre queue_l dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50
  have old_PreH27 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have old_PreH30 : StockTableShape dp_l days_pre max_stock_pre := ⟨PreH49,fun row hr => annotation_row_length dp_l (days_pre+1) (max_stock_pre+1) row [] PreH49 PreH50 hr⟩
  split_pures
  all_goals
    have Hdone := PreH38.1
    have Hcell := StockDaysDone_cell_bounded__safety_buy ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i source_day best_index __default__List_Z old_PreH27 Hdone old_PreH30 (by omega) (by omega)
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT at Hcell
    have hprod := product_bounds best_index ask_price (by omega) (by omega)
    have hjprod := product_bounds j ask_price (by omega) (by omega)
    dump_pre_spatial
    simp only [INT_MAX, INT_MIN]
    omega

theorem proof_of_maximum_profit_entail_wit_34 : maximum_profit_entail_wit_34 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH23 PreH24 PreH25 PreH26 (by omega) (by omega) PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH44,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH44 PreH45 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_36_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_36_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_36_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_36_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_36_3 : maximum_profit_entail_wit_36_3 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH23 PreH24 PreH25 PreH26 (by omega) (by omega) PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH44,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH44 PreH45 hr⟩
  rw [← PreH40]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_2 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_3 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_4 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_5 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_6 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_7 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_8 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))
      | exact (stock_aux_maximum_profit_entail_wit_38_3_split_goal_9 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l_2 dp_l_2 neg_inf width i source_day j bid_price sell_cap ask_price buy_cap head tail (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_37_1 : maximum_profit_entail_wit_37_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 tail head j buy_cap ask_price sell_cap bid_price source_day i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH25 PreH26 PreH27 PreH28 (by omega) (by omega) PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH47,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH47 PreH48 hr⟩
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact StockBuyProgress_complete_day__buy_semantics ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j hi PreH4 PreH7 PreH1 PreH40

theorem proof_of_maximum_profit_entail_wit_37_2 : maximum_profit_entail_wit_37_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 j ask_price buy_cap i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH21 PreH22 PreH23 PreH24 (by omega) (by omega) PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH37,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH37 PreH38 hr⟩
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact stock_early_buy_complete__early_buy ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i j hi PreH32 (by omega) PreH12 (by omega)

theorem proof_of_maximum_profit_entail_wit_38 : maximum_profit_entail_wit_38 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 i width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hi := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH12 PreH13 PreH14 PreH15 (by omega) (by omega) PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have hs : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH28,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH28 PreH29 hr⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | omega
      | exact (stock_aux_maximum_profit_entail_wit_41_split_goal_1 wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l dp_l_2 i width neg_inf (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega) (by first | assumption | exact hi | exact hs | omega))

theorem proof_of_maximum_profit_entail_wit_25_1 : maximum_profit_entail_wit_25_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i j source_day best_index head tail bid_price sell_cap sell_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have old_PreH25 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have old_PreH29 : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  have hlen := old_PreH29.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH3
  rw [hidef] at hcompare
  have hval : sell_candidate = StockSellScore dp_l_2 source_day bid_price best_index - j*bid_price := by
    unfold StockSellScore
    rw [← hsdef]
    exact PreH39
  have hcell := StockProofInternal.sell_cell_queue ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j queue_l_2 bid_price sell_cap head tail best_index sell_candidate old_PreH25 PreH38 (by omega) PreH40 (by omega) PreH21 PreH25 PreH26 hval
  rw [Int.max_eq_right (by omega)] at hcell
  have hstep := StockProofInternal.sell_replace_step ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j sell_candidate old_PreH25 (by omega) PreH38 (by omega) hcell
  obtain ⟨hp,hs⟩ := hstep
  rw [← hidef] at hp hs
  have hq := StockProofInternal.sell_queue_replace dp_l_2 queue_l_2 source_day bid_price (j+1) (j+sell_cap) head tail i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) hsrc hcur (by omega) PreH40
  have hqnext : StockSellQueue (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) queue_l_2 source_day bid_price (j-1+2) (j-1+sell_cap+1) head tail := by
    simpa only [show j-1+2=j+1 by omega, show j-1+sell_cap+1=j+sell_cap by omega] using hq
  have hdaily := old_PreH25.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH38.2.2.1
  have hrange := PreH38.2.2.2.1
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j sell_candidate dp_l_2 __default__List_Z (by omega) (by omega))
  have hvalues : StockTableValuesBounded (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre := by
    have hv := hp.1.2.1
    simpa only [PreH27] using hv
  have hbound := table_bound_annotations (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hs hvalues
  have hshape := shape_annotation (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hs
  have hlength := hs.1
  Exists (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | exact hbound.1 | exact hbound.2

theorem proof_of_maximum_profit_entail_wit_25_2 : maximum_profit_entail_wit_25_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i j source_day best_index head tail bid_price sell_cap sell_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51
  have old_PreH25 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH27 PreH28 PreH29 PreH30 (by omega) (by omega) PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have old_PreH29 : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH50,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH50 PreH51 hr⟩
  have hlen := old_PreH29.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH3
  rw [hidef] at hcompare
  have hval : sell_candidate = StockSellScore dp_l_2 source_day bid_price best_index - j*bid_price := by
    unfold StockSellScore
    rw [← hsdef]
    exact PreH39
  have hcell := StockProofInternal.sell_cell_queue ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j queue_l_2 bid_price sell_cap head tail best_index sell_candidate old_PreH25 PreH38 (by omega) PreH40 (by omega) PreH21 PreH25 PreH26 hval
  rw [Int.max_eq_left (by omega)] at hcell
  have hp : StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day (j-1) := by
    rcases PreH38 with ⟨HD,Hi,Hsrc,Hsr,Hj,Hcopy,Hcells,Hlast⟩
    refine ⟨HD,Hi,Hsrc,Hsr,by omega,?_,?_,Hlast⟩
    · intro stock hs; exact Hcopy stock (by omega)
    · intro stock hs
      by_cases he : stock = j
      · subst stock; exact hcell
      · exact Hcells stock (by omega)
  have hq := PreH40
  have hqnext : StockSellQueue dp_l_2 queue_l_2 source_day bid_price (j-1+2) (j-1+sell_cap+1) head tail := by
    simpa only [show j-1+2=j+1 by omega, show j-1+sell_cap+1=j+sell_cap by omega] using hq
  have hdaily := old_PreH25.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH38.2.2.1
  have hrange := PreH38.2.2.2.1
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width i j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega

theorem proof_of_maximum_profit_entail_wit_35 : maximum_profit_entail_wit_35 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l neg_inf width i source_day bid_price sell_cap ask_price buy_cap j best_index head tail __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width source_day best_index dp_l __default__List_Z (by omega) (by omega))
  Exists dp_l
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega

theorem proof_of_maximum_profit_entail_wit_36_1 : maximum_profit_entail_wit_36_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i j source_day best_index head bid_price sell_cap ask_price buy_cap tail buy_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have old_PreH26 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have old_PreH30 : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH51,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH51 PreH52 hr⟩
  have hlen := old_PreH30.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH3
  rw [hidef] at hcompare
  have hval : buy_candidate = StockBuyScore dp_l_2 source_day ask_price best_index - j*ask_price := by
    unfold StockBuyScore
    rw [← hsdef]
    exact PreH40
  have hcell := StockBuyCellValue_improve__buy_cell_progress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j queue_l_2 ask_price buy_cap head tail best_index buy_candidate PreH39 (by omega) PreH41 (by omega) PreH20 PreH24 PreH23 hval hcompare
  have hstep := StockBuyProgress_replace_improved_step__buy_semantics ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre i source_day j buy_candidate old_PreH26 (by omega) old_PreH30 PreH39 (by omega) hcompare hcell
  obtain ⟨hp,hs⟩ := hstep
  rw [← hidef] at hp hs
  have hq := StockBuyQueue_replace_other_row__buy_cell_progress dp_l_2 queue_l_2 source_day ask_price (j-buy_cap) (j-1) head tail i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) hsrc hcur (by omega) PreH41
  have hdaily := old_PreH26.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH39.2.2.1
  have hrange := PreH39.2.2.2.1
  have hqnext : StockBuyQueue (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) queue_l_2 source_day ask_price (j+1-buy_cap-1) (j+1-2) head tail := by
    simpa only [show j+1-buy_cap-1=j-buy_cap by omega, show j+1-2=j-1 by omega] using hq
  sep_apply (StockProofInternal.merge_cell (&("dp")) (days_pre+1) width i j buy_candidate dp_l_2 __default__List_Z (by omega) (by omega))
  have hvalues : StockTableValuesBounded (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre := by
    have hv := hp.1.2.1
    simpa only [PreH28] using hv
  have hbound := table_bound_annotations (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hs hvalues
  have hshape := shape_annotation (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre hs
  have hlength := hs.1
  Exists (replace_Znth i (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega | exact hbound.1 | exact hbound.2

theorem proof_of_maximum_profit_entail_wit_36_2 : maximum_profit_entail_wit_36_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 neg_inf width i j source_day best_index head bid_price sell_cap ask_price buy_cap tail buy_candidate __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52
  have old_PreH26 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH28 PreH29 PreH30 PreH31 (by omega) (by omega) PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have old_PreH30 : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH51,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH51 PreH52 hr⟩
  have hlen := old_PreH30.1
  have hsrc : 0 ≤ source_day ∧ source_day < Zlength dp_l_2 := by omega
  have hcur : 0 ≤ i ∧ i < Zlength dp_l_2 := by omega
  have hsdef := Znth_indep dp_l_2 source_day __default__List_Z [] hsrc
  have hidef := Znth_indep dp_l_2 i __default__List_Z [] hcur
  have hcompare := PreH3
  rw [hidef] at hcompare
  have hval : buy_candidate = StockBuyScore dp_l_2 source_day ask_price best_index - j*ask_price := by
    unfold StockBuyScore
    rw [← hsdef]
    exact PreH40
  have hcell := StockBuyCellValue_keep__buy_cell_progress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j queue_l_2 ask_price buy_cap head tail best_index buy_candidate PreH39 (by omega) PreH41 (by omega) PreH20 PreH24 PreH23 hval hcompare
  have hp := StockBuyProgress_step_same__buy_cell_progress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i source_day j PreH39 (by omega) hcell
  have hq := PreH41
  have hdaily := old_PreH26.2.2.2.2.2.2 i (by omega)
  rcases hdaily with ⟨hbid,hask,hbuy,hsell⟩
  have heq := PreH39.2.2.1
  have hrange := PreH39.2.2.2.1
  have hqnext : StockBuyQueue dp_l_2 queue_l_2 source_day ask_price (j+1-buy_cap-1) (j+1-2) head tail := by
    simpa only [show j+1-buy_cap-1=j-buy_cap by omega, show j+1-2=j-1 by omega] using hq
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width i j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega

theorem proof_of_maximum_profit_entail_wit_39_1 : maximum_profit_entail_wit_39_1 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 answer j width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have old_PreH15 := annotation_inputs ap_l bp_l buy_l sell_l days_pre max_stock_pre PreH17 PreH18 PreH19 PreH20 (by omega) (by omega) PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have old_PreH17 : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH33,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH33 PreH34 hr⟩
  have hlen := old_PreH17.1
  have hday : 0 ≤ days_pre ∧ days_pre < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 days_pre __default__List_Z [] hday
  have hv : (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) = Znth j (Znth days_pre dp_l_2 []) 0 := by rw [he]
  have hp := stock_answer_improve__outer_answer ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) (by omega) PreH15 PreH4 PreH28 hv PreH3
  have hb := PreH28.1.2.1 days_pre j (by rw [old_PreH15.1]; omega) (by omega)
  rw [← he] at hb
  unfold STOCK_MAX_PROFIT at hb
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width days_pre j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega

theorem proof_of_maximum_profit_entail_wit_39_2 : maximum_profit_entail_wit_39_2 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l_2 dp_l_2 answer j width neg_inf __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34
  have old_PreH17 : StockTableShape dp_l_2 days_pre max_stock_pre := ⟨PreH33,fun row hr => annotation_row_length dp_l_2 (days_pre+1) (max_stock_pre+1) row [] PreH33 PreH34 hr⟩
  have hlen := old_PreH17.1
  have hday : 0 ≤ days_pre ∧ days_pre < Zlength dp_l_2 := by omega
  have he := Znth_indep dp_l_2 days_pre __default__List_Z [] hday
  have hv : (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) = Znth j (Znth days_pre dp_l_2 []) 0 := by rw [he]
  have hp := stock_answer_keep__outer_answer ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0) (by omega) PreH4 PreH28 hv PreH3
  sep_apply (StockProofInternal.restore_cell (&("dp")) (days_pre+1) width days_pre j dp_l_2 __default__List_Z (by omega) (by omega))
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | trivial | rfl | omega

private theorem row_forget (x lo m : Int) (row : List Int) :
    intArray2.row_store m x lo row |-- intArray.undef_seg x (lo*m) ((lo+1)*m) := by
  change intArray.full (x+lo*m*sizeof(INT)) m row |-- _
  refine naive_C_Rules.toContext.derivable1_trans _ _ _
    (intArray.full_to_undef_full (x+lo*m*sizeof(INT)) m row) ?_
  have h := (intArray.undef_seg_0_shift x (lo*m) ((lo+1)*m)).right
  have he : (lo+1)*m-lo*m=m := by ring
  simpa only [he, SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full,
    SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg, store_undef_array, Int.sub_zero] using h

private theorem rows_forget_rec (x lo hi m : Int) (rows : List (List Int))
    (hm : 0 ≤ m) (hlen : Zlength rows = hi-lo) :
    store_array_rec naive_C_Rules (intArray2.row_store m) x lo hi rows |--
      intArray.undef_seg x (lo*m) (hi*m) := by
  induction rows generalizing lo with
  | nil =>
    have he : lo=hi := by simp only [Zlength_nil] at hlen; omega
    subst lo
    simp only [store_array_rec]
    intro state hs
    exact (intArray.undef_seg_empty x (hi*m)).right state hs.2.2
  | cons row rows ih =>
    have hl : Zlength rows = hi-(lo+1) := by simp only [Zlength_cons] at hlen; omega
    have hnonneg : 0 ≤ Zlength rows := Zlength_nonneg rows
    change intArray2.row_store m x lo row ** store_array_rec naive_C_Rules (intArray2.row_store m) x (lo+1) hi rows |-- _
    refine naive_C_Rules.toContext.derivable1_trans _ _ _
      (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ (row_forget x lo m row) (ih (lo+1) hl)) ?_
    exact intArray.undef_seg_merge_to_undef_seg x (lo*m) ((lo+1)*m) (hi*m) (by constructor <;> nlinarith)

private theorem rows_forget (x n m : Int) (rows : List (List Int))
    (hm : 0 ≤ m) (hlen : Zlength rows=n) :
    intArray2.full x n m rows |-- intArray.undef_seg x 0 (n*m) := by
  simpa only [Int.zero_mul,Int.sub_zero] using rows_forget_rec x 0 n m rows hm (by omega)

private theorem scratch_cleanup (a len total : Int) (l : List Int) (hc : 0 ≤ len ∧ len ≤ total) :
    intArray.full a len l ** intArray.undef_seg a len total |-- intArray.undef_full a total := by
  refine naive_C_Rules.toContext.derivable1_trans _ (intArray.undef_seg a 0 len ** intArray.undef_seg a len total) _ ?_ ?_
  · apply naive_C_Rules.toContext.derivable1_sepcon_mono
    · exact naive_C_Rules.toContext.derivable1_trans _ _ _ (intArray.full_to_seg a len l) (intArray.seg_to_undef_seg a 0 len l)
    · exact naive_C_Rules.toContext.derivable1_refl _
  · simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.undef_seg_merge_to_undef_full a 0 len total hc

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

theorem proof_of_maximum_profit_entail_wit_40 : maximum_profit_entail_wit_40 := by
  right
  intro sell_l buy_l bp_l ap_l days_pre max_stock_pre wait_days_pre queue_l dp_l answer j width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hp := stock_answer_finish__outer_answer ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre j answer (by omega) PreH1 PreH11 PreH25
  subst width
  sep_apply (rows_forget (&("dp")) (days_pre+1) (max_stock_pre+1) dp_l (by omega) PreH30)
  sep_apply (scratch_cleanup (&("queue_index")) (max_stock_pre+1) 991 queue_l (by omega))
  sep_apply (intArray.undef_seg_merge_to_undef_full (&("dp")) 0 ((days_pre+1)*(max_stock_pre+1)) 982081 (by constructor <;> nlinarith))
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial; exact hp

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_proof_manual
