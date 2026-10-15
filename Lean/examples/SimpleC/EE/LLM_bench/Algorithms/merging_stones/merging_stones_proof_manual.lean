import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_goal
import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open merging_stones_goal merging_stones_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev array2 := naive_C_Rules.IntArray2
private theorem merge_cell (addr n row col value : Int) (table : List (List Int)) (d : List Int)
    (hr : 0 ≤ row ∧ row < n) (hc : 0 ≤ col ∧ col < n) :
    (((addr+(row*n+col)*sizeof(INT)) # Int |-> value) **
      intArray.missing_i (addr+row*n*sizeof(INT)) col 0 n (Znth row table d) **
      array2.missing_i addr row 0 n n table) |--
    array2.full addr n n (replace_Znth row (replace_Znth col value (Znth row table d)) table) := by
  have he : addr+(row*n+col)*sizeof(INT) = addr+row*n*sizeof(INT)+col*sizeof(INT) := by ring
  rw [he]
  sep_apply (intArray.missing_i_merge_to_full (addr+row*n*sizeof(INT)) col n value (Znth row table d) hc)
  have ht : (intArray.full (addr+row*n*sizeof(INT)) n (replace_Znth col value (Znth row table d)) **
      array2.missing_i addr row 0 n n table |--
      array2.full addr n n (replace_Znth row (replace_Znth col value (Znth row table d)) table)) :=
    array2.missing_i_merge_to_full addr row n n table (replace_Znth col value (Znth row table d)) hr
  sep_apply ht
  cancel

private theorem restore_cell (addr n row col : Int) (table : List (List Int)) (d : List Int)
    (hr : 0 ≤ row ∧ row < n) (hc : 0 ≤ col ∧ col < n) :
    (((addr+(row*n+col)*sizeof(INT)) # Int |-> Znth col (Znth row table d) 0) **
      intArray.missing_i (addr+row*n*sizeof(INT)) col 0 n (Znth row table d) **
      array2.missing_i addr row 0 n n table) |-- array2.full addr n n table := by
  simpa only [replace_Znth_Znth] using merge_cell addr n row col
    (Znth col (Znth row table d) 0) table d hr hc

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

private theorem scratch_flat_to_rows_rec (k : Nat) (x lo m : Int) (l : List Int)
    (hm : 0 ≤ m) :
    intArray.seg x (lo*m) ((lo+(k : Int))*m) l |--
    EX rows : List (List Int), “ (Zlength rows = (k : Int) ∧ Forall (fun row => Zlength row = m) rows) ” &&
      store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store m) x lo (lo+(k : Int)) rows := by
  induction k generalizing lo l with
  | zero =>
    simp only [Nat.cast_zero, Int.add_zero]
    prop_apply (intArray.seg_Zlength x (lo*m) (lo*m) l)
    Intros_p hlen
    have he : l = [] := by
      have hn : Zlength l = 0 := by omega
      change (l.length : Int) = 0 at hn
      have hnat : l.length = 0 := by omega
      cases l with
      | nil => rfl
      | cons a rest =>
        simp only [List.length_cons] at hnat
        omega
    rw [he]
    Exists ([] : List (List Int))
    sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (intArray.seg_empty x (lo*m) (lo*m))).1)
    simp only [store_array_rec]
    split_pure_spatial
    · Intros_p htrue
      exact naive_C_Rules.toContext.derivable1_refl _
    · split_pures <;> dump_pre_spatial <;> simp [Zlength_nil, Forall.iff_forall_mem]
  | succ k ih =>
    simp only [Nat.cast_succ]
    have hsplit : lo*m ≤ (lo+1)*m ∧ (lo+1)*m ≤ (lo+((k : Int)+1))*m := by
      constructor <;> nlinarith [Int.natCast_nonneg k]
    sep_apply (intArray.seg_split_to_seg x (lo*m) ((lo+1)*m) ((lo+((k : Int)+1))*m) l hsplit)
    have he : lo+((k : Int)+1) = (lo+1)+(k : Int) := by omega
    rw [he]
    sep_apply (ih (lo+1) (sublist (((lo+1)*m)-(lo*m)) ((((lo+1)+(k : Int))*m)-(lo*m)) l))
    Intros rows
    rename_i hr
    sep_apply (intArray.seg_to_full x (lo*m) ((lo+1)*m) (sublist 0 (((lo+1)*m)-(lo*m)) l))
    have hdelta : (lo+1)*m-lo*m = m := by ring
    simp only [hdelta]
    prop_apply intArray.full_Zlength
    Intros_p hrow
    Exists ((sublist 0 m l)::rows)
    simp only [store_array_rec, Zlength_cons]
    change _ |-- _ && (intArray.full (x+lo*m*sizeof(INT)) m (sublist 0 m l) ** _)
    split_pure_spatial
    · cancel
      exact naive_C_Rules.toContext.derivable1_refl _
    · dump_pre_spatial
      refine ⟨by omega, ?_⟩
      have hrows := hr.2
      rw [Forall.iff_forall_mem] at hrows ⊢
      intro row hmem
      rcases List.mem_cons.mp hmem with heq | hin
      · simpa only [heq] using hrow
      · exact hrows row hin

private theorem scratch_flat_to_rows (x n m : Int) (l : List Int)
    (hn : 0 ≤ n) (hm : 0 ≤ m) :
    intArray.full x (n*m) l |-- EX rows : List (List Int),
      “ (Zlength rows = n ∧ Forall (fun row => Zlength row = m) rows) ” && array2.full x n m rows := by
  have hcast : (n.toNat : Int) = n := Int.toNat_of_nonneg hn
  have hrec := scratch_flat_to_rows_rec n.toNat x 0 m l hm
  simp only [hcast, Int.zero_mul, Int.zero_add] at hrec
  change intArray.full x (n*m) l |-- EX rows : List (List Int),
    “ (Zlength rows = n ∧ Forall (fun row => Zlength row = m) rows) ” &&
      store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store m) x 0 n rows
  exact naive_C_Rules.toContext.derivable1_trans _ _ _ (intArray.full_to_seg x (n*m) l) hrec

private theorem scratch_row_to_undef_seg (x lo m : Int) (row : List Int) :
    array2.row_store m x lo row |-- intArray.undef_seg x (lo*m) ((lo+1)*m) := by
  change intArray.full (x+lo*m*sizeof(INT)) m row |-- _
  sep_apply (intArray.full_to_undef_full (x+lo*m*sizeof(INT)) m row)
  sep_apply (intArray.undef_full_to_undef_seg (x+lo*m*sizeof(INT)) m)
  have hs := ((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (intArray.undef_seg_shift x (lo*m) 0 m)).2
  have he : lo*m+m = (lo+1)*m := by ring
  simpa only [Int.zero_mul, Int.add_zero, he] using hs

private theorem scratch_rows_rec_to_undef_seg (rows : List (List Int)) (x lo hi m : Int)
    (hm : 0 ≤ m) :
    store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store m) x lo hi rows |--
      intArray.undef_seg x (lo*m) (hi*m) := by
  induction rows generalizing lo with
  | nil =>
    simp only [store_array_rec]
    Intros_p he
    subst hi
    sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (intArray.undef_seg_empty x (lo*m))).2)
    split_pures <;> first | cancel | (dump_pre_spatial; trivial)
    Intros_p htrue
    exact naive_C_Rules.toContext.derivable1_refl _
  | cons row rows ih =>
    simp only [store_array_rec]
    prop_apply (SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_valid naive_C_Rules.toSeparationLogicSig (List Int)
      (array2.row_store m) x (lo+1) hi rows)
    Intros_p hb
    sep_apply (ih (lo+1))
    sep_apply (scratch_row_to_undef_seg x lo m row)
    sep_apply (intArray.undef_seg_merge_to_undef_seg x (lo*m) ((lo+1)*m) (hi*m)
      (by constructor <;> nlinarith))
    cancel

private theorem scratch_rows_to_flat_undef (x n m : Int) (rows : List (List Int))
    (hm : 0 ≤ m) : array2.full x n m rows |-- intArray.undef_full x (n*m) := by
  change store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store m) x 0 n rows |-- _
  sep_apply (scratch_rows_rec_to_undef_seg rows x 0 n m hm)
  simp only [Int.zero_mul]
  sep_apply (intArray.undef_seg_to_undef_full x 0 (n*m))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  exact naive_C_Rules.toContext.derivable1_refl _
private theorem indexed_Forall {A : Type} (P : A → Prop) (l : List A) (d : A) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
    have hm := h l[i.toNat] (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm
  · intro h v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength l := by change 0 ≤ (n : Int) ∧ (n : Int) < (l.length : Int); omega
    have hh := h n hi
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh

private theorem forall_sublist_index {A : Type} (P : A → Prop) (d : A)
    (l : List A) (lo hi : Int) (hb : 0 ≤ lo ∧ lo ≤ hi) (he : hi ≤ Zlength l) :
    Forall P (sublist lo hi l) ↔ ∀ k, lo ≤ k ∧ k < hi → P (Znth k l d) := by
  rw [indexed_Forall P _ d]
  have hlen : Zlength (sublist lo hi l) = hi-lo := by
    unfold Zlength
    rw [sublist_length lo hi l hb he]
    exact Int.toNat_of_nonneg (by omega)
  constructor
  · intro h k hk
    have hh := h (k-lo) (by rw [hlen]; omega)
    rw [Znth_sublist d lo (k-lo) hi l hb.1 (by omega), Int.sub_add_cancel] at hh
    exact hh
  · intro h j hj
    rw [hlen] at hj
    rw [Znth_sublist d lo j hi l hb.1 hj]
    exact h (j+lo) (by omega)


private theorem stone_mass (l : List Int) (n : Int) (hl : Zlength l = n)
    (hlo : Forall (LE.le (1 : Int)) l) (hhi : Forall (GE.ge (1000 : Int)) l) :
    StoneMassesBounded l n := by
  refine ⟨hl, ?_⟩
  intro idx hi
  exact ⟨(indexed_Forall _ l 0).mp hlo idx (by omega),
    (indexed_Forall _ l 0).mp hhi idx (by omega)⟩

private theorem stone_shape (rows : List (List Int)) (n : Int) (hlen : Zlength rows = n)
    (hr : Forall (Eq n) (rows.map Zlength)) : StoneTableShape rows n := by
  refine ⟨hlen, ?_⟩
  have hf : Forall (fun row => Zlength row = n) rows := by
    rw [Forall.iff_forall_mem] at hr ⊢
    intro row hm
    exact (hr (Zlength row) (List.mem_map.mpr ⟨row, hm, rfl⟩)).symm
  intro r hidx
  exact (indexed_Forall _ rows []).mp hf r (by omega)

theorem proof_of_mergingStones_entail_wit_3 : mergingStones_entail_wit_3 := by
  unfold mergingStones_entail_wit_3
  right
  intro n stones flat k hmax hmin hk hk0 hkn hn hnmax hstones hb hu
  have he : k = n*n := by omega
  rw [he]
  sep_apply (intArray.seg_to_full (&("dp")) 0 (n*n) flat)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (scratch_flat_to_rows (&("dp")) n n flat (by omega) (by omega))
  Intros rows
  have hrows : Zlength rows = n ∧ Forall (fun row => Zlength row = n) rows := by assumption
  Exists ([0] : List Int) rows
  sep_apply (intArray.undef_seg_split_to_undef_seg (&("prefix")) 1 (n+1) 9 ⟨by omega, by omega⟩)
  simp only [Int.zero_mul, Int.add_zero]
  have hrowmap : Forall (Eq n) (rows.map Zlength) := by
    have hf := hrows.2
    rw [Forall.iff_forall_mem] at hf ⊢
    intro v hv
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hv
    exact (hf row hr).symm
  have hprefix : StonePrefixProgress stones [0] 0 := by
    intro j hj
    have he : j = 0 := by omega
    subst j
    simp [Znth, sublist, sum]
  split_pure_spatial
  · change _ |-- ((intArray.seg (&("prefix")) 0 1 [0] **
      intArray.undef_seg (&("prefix")) 1 (n+1)) ** array2.full (&("dp")) n n rows) **
      intArray.undef_seg (&("prefix")) (n+1) 9
    have hstore : DerivedPredSig.store_4byte SacContext.endian SacContext.rules (&("prefix")) 0 |--
        ((&("prefix")) # Int |-> (0 : Int)) := by
      change _ |-- “ (DerivedPredSig.isvalidptr_int SacContext.arch (&("prefix")) ∧
        0 ≤ Int.max_signed ∧ 0 ≥ Int.min_signed) ” && _
      split_pure_spatial
      · exact naive_C_Rules.toContext.derivable1_refl _
      · dump_pre_spatial
        assumption
    have hseg : ((&("prefix")) # Int |-> (0 : Int)) |-- intArray.seg (&("prefix")) 0 1 [0] := by
      have hs := intArray.seg_single (&("prefix")) 0 (0 : Int)
      change (((&("prefix"))+0*sizeof(INT)) # Int |-> (0 : Int)) |--
        intArray.seg (&("prefix")) 0 1 [0] at hs
      simpa only [Int.zero_mul, Int.add_zero] using hs
    have hsingle := naive_C_Rules.toContext.derivable1_trans _ _ _ hstore hseg
    have hframe := naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
      (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ hsingle
          (naive_C_Rules.toContext.derivable1_refl (intArray.undef_seg (&("prefix")) 1 (n+1))))
        (naive_C_Rules.toContext.derivable1_refl (array2.full (&("dp")) n n rows)))
      (naive_C_Rules.toContext.derivable1_refl (intArray.undef_seg (&("prefix")) (n+1) 9))
    apply naive_C_Rules.toContext.derivable1_trans _ _ _ ?_ hframe
    cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_mergingStones_entail_wit_4 : mergingStones_entail_wit_4 := by
  unfold mergingStones_entail_wit_4
  left
  intro n stones_addr stones pre i table hi hn hnmax hb hu hrows hi0 hin hp
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (intArray.seg_Zlength (&("prefix")) 0 (i+1+1)
    (pre ++ [Znth (i-0) pre 0 + Znth i stones 0]))
  Intros_p hpre
  simp only [Int.sub_zero, Zlength_app, Zlength_cons, Zlength_nil] at hpre ⊢
  have hlegacy : StonePrefixProgressLegacy stones pre n i :=
    ⟨hstones, by omega, ⟨hi0, hin⟩, hp⟩
  have hnext := StonePrefixProgress_extend__prefix_math stones pre n i hlegacy ⟨hi0, hi⟩
  Exists (pre ++ [Znth i pre 0 + Znth i stones 0]) table
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | exact hnext.toAnnotation

theorem proof_of_mergingStones_entail_wit_5 : mergingStones_entail_wit_5 := by
  unfold mergingStones_entail_wit_5
  right
  intro n stones pre i table hi hn hnmax hb hu hrows hi0 hin hp
  have he : i = n := by omega
  have hdone : StonePrefixDone stones pre n := by simpa only [he] using hp
  have hzero : StoneZeroRows table 0 := by
    simp only [StoneZeroRows, sublist]
    simp [Forall.iff_forall_mem]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_mergingStones_entail_wit_6 : mergingStones_entail_wit_6 := by
  unfold mergingStones_entail_wit_6
  right
  intro n stones row pre table hr hn hnmax hb hu hrows hp hr0 hrn hz
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    refine ⟨hz, ?_⟩
    simp [sublist, Forall.iff_forall_mem]

private theorem zero_rows_legacy (table : List (List Int)) (n row : Int)
    (hs : StoneTableShape table n) (hr : 0 ≤ row ∧ row ≤ n) (hz : StoneZeroRows table row) :
    StoneZeroRowsLegacy table n row := by
  refine ⟨hs, hr, ?_⟩
  have hrows := (forall_sublist_index (Forall (Eq (0 : Int))) [] table 0 row
    ⟨by omega, hr.1⟩ (by rw [hs.1]; exact hr.2)).mp hz
  intro r c hrr hcc
  have hh := (indexed_Forall (Eq (0 : Int)) (Znth r table []) 0).mp (hrows r (by omega))
    c (by rw [hs.2 r (by omega)]; exact hcc)
  exact hh.symm

private theorem zero_rows_current (table : List (List Int)) (n row : Int)
    (hz : StoneZeroRowsLegacy table n row) : StoneZeroRows table row := by
  have hrowrange := hz.2.1
  apply (forall_sublist_index (Forall (Eq (0 : Int))) [] table 0 row
    ⟨by omega, hz.2.1.1⟩ (by rw [hz.1.1]; exact hz.2.1.2)).mpr
  intro r hr
  apply (indexed_Forall (Eq (0 : Int)) (Znth r table []) 0).mpr
  intro c hc
  rw [hz.1.2 r (by omega)] at hc
  exact (hz.2.2 r c (by omega) hc).symm

private theorem zero_progress_legacy (table : List (List Int)) (n row col : Int)
    (hs : StoneTableShape table n) (hr : 0 ≤ row ∧ row < n) (hc : 0 ≤ col ∧ col ≤ n)
    (hz : StoneZeroProgress table row col) : StoneZeroProgressLegacy table n row col := by
  have hrows := zero_rows_legacy table n row hs ⟨hr.1, by omega⟩ hz.1
  refine ⟨hs, hr, hc, hrows.2.2, ?_⟩
  have hrow := (forall_sublist_index (Eq (0 : Int)) 0 (Znth row table []) 0 col
    ⟨by omega, hc.1⟩ (by rw [hs.2 row hr]; exact hc.2)).mp hz.2
  intro c hcc
  exact (hrow c (by omega)).symm

private theorem zero_progress_current (table : List (List Int)) (n row col : Int)
    (hz : StoneZeroProgressLegacy table n row col) : StoneZeroProgress table row col := by
  refine ⟨zero_rows_current table n row ⟨hz.1, ⟨hz.2.1.1, by have := hz.2.1; omega⟩, hz.2.2.2.1⟩, ?_⟩
  apply (forall_sublist_index (Eq (0 : Int)) 0 (Znth row table []) 0 col
    ⟨by omega, hz.2.2.1.1⟩ (by rw [hz.1.2 row hz.2.1]; exact hz.2.2.1.2)).mpr
  intro c hc
  exact (hz.2.2.2.2 c (by omega)).symm

private theorem shape_row_map (table : List (List Int)) (n : Int) (hs : StoneTableShape table n) :
    Forall (Eq n) (table.map Zlength) := by
  have hh : Forall (fun row => Zlength row = n) table :=
    (indexed_Forall _ table []).mpr (by intro r hr; exact hs.2 r (by rw [← hs.1]; exact hr))
  rw [Forall.iff_forall_mem] at hh ⊢
  intro v hv
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hv
  exact (hh row hr).symm

private theorem prefix_interval_sum (stones pre : List Int) (n lo hi : Int)
    (hlen : Zlength stones = n) (hp : StonePrefixDone stones pre n)
    (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ n) :
    Znth hi pre 0 - Znth lo pre 0 = sum (sublist lo hi stones) := by
  rw [hp hi ⟨by omega, hh⟩, hp lo ⟨hl.1, by omega⟩,
    sublist_split 0 hi lo stones ⟨by omega, hl.1⟩ ⟨hl.2, by rw [hlen]; exact hh⟩, sum_app]
  omega

private theorem prefix_interval_bounds (stones pre : List Int) (n lo hi : Int)
    (hm : StoneMassesBounded stones n) (hp : StonePrefixDone stones pre n)
    (hl : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ n) :
    hi-lo ≤ Znth hi pre 0-Znth lo pre 0 ∧ Znth hi pre 0-Znth lo pre 0 ≤ (hi-lo)*1000 := by
  rw [prefix_interval_sum stones pre n lo hi hm.1 hp hl hh]
  exact StoneMassesBounded_sublist_sum_bounds__prefix_math stones n lo hi hm hl hh

theorem proof_of_mergingStones_entail_wit_7 : mergingStones_entail_wit_7 := by
  unfold mergingStones_entail_wit_7
  left
  intro n stones_addr stones col row pre table d hc hn hnmax hb hu hmap hp hr0 hrn hc0 hcn hz
  prop_apply (array2.missing_i_Zlength (&("dp")) row 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hzold := zero_progress_legacy table n row col hs ⟨hr0, hrn⟩ ⟨hc0, hcn⟩ hz
  have hnext := StoneZeroProgress_store__zero_table table n row col d hzold hc
  let updated := replace_Znth row (replace_Znth col 0 (Znth row table d)) table
  have hnewzero : StoneZeroProgress updated row (col+1) := zero_progress_current _ n _ _ hnext
  have hnewmap : Forall (Eq n) (updated.map Zlength) := shape_row_map _ n hnext.1
  Exists pre updated
  sep_apply (merge_cell (&("dp")) n row col 0 table d ⟨hr0, hrn⟩ ⟨hc0, hc⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_mergingStones_entail_wit_8 : mergingStones_entail_wit_8 := by
  unfold mergingStones_entail_wit_8
  left
  intro n stones_addr stones col row pre table hc hn hnmax hb hu hmap hp hr0 hrn hc0 hcn hz
  prop_apply (array2.full_Zlength (&("dp")) n n table)
  Intros_p htable
  have hs := stone_shape table n htable hmap
  have hzold := zero_progress_legacy table n row col hs ⟨hr0, hrn⟩ ⟨hc0, hcn⟩ hz
  have hnext : StoneZeroRowsLegacy table n (row+1) := by
    refine ⟨hs, ⟨by omega, by omega⟩, ?_⟩
    intro r c hrr hcc
    by_cases hlt : r < row
    · exact hzold.2.2.2.1 r c ⟨hrr.1, hlt⟩ hcc
    · have he : r = row := by omega
      subst r
      exact hzold.2.2.2.2 c ⟨hcc.1, by omega⟩
  have hnewzero := zero_rows_current table n (row+1) hnext
  Exists pre table
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_mergingStones_entail_wit_9 : mergingStones_entail_wit_9 := by
  unfold mergingStones_entail_wit_9
  left
  intro n stones_addr stones row pre table hr hn hnmax hb hu hmap hp hr0 hrn hz
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.full_Zlength (&("dp")) n n table)
  Intros_p htable
  have hs := stone_shape table n htable hmap
  have hzold := zero_rows_legacy table n row hs ⟨hr0, hrn⟩ hz
  have he : row = n := by omega
  rw [he] at hzold
  have hlegacy := StoneLenDone_two_of_zero__zero_table stones table n hstones hn hzold
  have hdone := hlegacy.toAnnotation
  Exists pre table
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_mergingStones_entail_wit_10 : mergingStones_entail_wit_10 := by
  unfold mergingStones_entail_wit_10
  right
  intro n stones len pre table hl hn hnmax hb hu hmap hp hl0 hln hd
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    refine ⟨hd, ?_⟩
    intro l r hl hr hfit
    omega

theorem proof_of_mergingStones_entail_wit_11 : mergingStones_entail_wit_11 := by
  unfold mergingStones_entail_wit_11
  left
  intro n stones_addr stones left len pre table hfit hn hnmax hb hu hmap hp hlen hln hl hlnext hprogress
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  have hm := stone_mass stones n hstones hb hu
  have hsum := prefix_interval_sum stones pre n left (left+len) hstones hp ⟨hl, by omega⟩ hfit
  have hbounds := prefix_interval_bounds stones pre n left (left+len) hm hp ⟨hl, by omega⟩ hfit
  have hsplit : StoneSplitProgress stones table n len left left 1000000 :=
    ⟨hprogress, Or.inl ⟨rfl, rfl⟩⟩
  Exists pre table
  simp only [Int.sub_add_cancel]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | trivial

private theorem left_progress_legacy (stones : List Int) (table : List (List Int)) (n len left : Int)
    (hstones : Zlength stones = n) (hs : StoneTableShape table n)
    (hl : 2 ≤ len ∧ len ≤ n) (hleft : 0 ≤ left ∧ left ≤ n-len+1)
    (hp : StoneLeftProgress stones table n len left) : StoneLeftProgressLegacy stones table n len left :=
  ⟨⟨hstones, hs, by omega, hp.1⟩, hl, hleft, hp.2⟩

private theorem split_progress_legacy (stones : List Int) (table : List (List Int))
    (n len left split best : Int) (hstones : Zlength stones = n) (hs : StoneTableShape table n)
    (hl : 2 ≤ len ∧ len ≤ n) (hleft : 0 ≤ left ∧ left+len ≤ n)
    (hk : left ≤ split ∧ split ≤ left+len-1) (hb : 0 ≤ best ∧ best ≤ 1000000)
    (hp : StoneSplitProgress stones table n len left split best) :
    StoneSplitProgressLegacy stones table n len left split best :=
  ⟨left_progress_legacy stones table n len left hstones hs hl ⟨hleft.1, by omega⟩ hp.1, hk, hb, hp.2⟩

private theorem split_progress_current (stones : List Int) (table : List (List Int))
    (n len left split best : Int) (hp : StoneSplitProgressLegacy stones table n len left split best) :
    StoneSplitProgress stones table n len left split best :=
  ⟨⟨hp.1.1.2.2.2, hp.1.2.2.2⟩, hp.2.2.2⟩

theorem proof_of_mergingStones_entail_wit_12 : mergingStones_entail_wit_12 := by
  unfold mergingStones_entail_wit_12
  right
  intro n stones best interval_sum split right left len pre table d hmax hmin hk hn hnmax hb hu hmap hp hlen hln hl hfit hr hls hsr hsum hsum0 hsummax hbest0 hbestmax hprogress
  Exists table
  sep_apply (restore_cell (&("dp")) n left split table d ⟨hl, by omega⟩ ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | trivial

theorem proof_of_mergingStones_entail_wit_13_1 : mergingStones_entail_wit_13_1 := by
  unfold mergingStones_entail_wit_13_1
  left
  intro n stones_addr stones pre table len left right split interval_sum best left_value d hcompare hn hnmax hb hu hmap hp hlen hln hl hfit hr hls hsr hsum hsum0 hsummax hbest0 hbestmax hprogress hk hleft_value
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.missing_i_Zlength (&("dp")) (split+1) 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hm := stone_mass stones n hstones hb hu
  have hlegacy := split_progress_legacy stones table n len left split best hstones hs
    ⟨hlen, hln⟩ ⟨hl, hfit⟩ ⟨hls, by omega⟩ ⟨hbest0, hbestmax⟩ hprogress
  have hcf := StoneSplitProgress_candidate_facts__interval_min_core stones table n len left split right best
    interval_sum d hm hnmax hlegacy hr ⟨hls, hk⟩ (by omega) hsum
  dsimp at hcf
  rw [← hleft_value] at hcf
  have hnext := StoneSplitProgress_replace_best__split_loop_step stones table n len left right split
    (left_value + Znth right (Znth (split+1) table d) 0 + interval_sum) best hr hk hcf.1.1 (by have := hcf.1.2; omega) hcompare hcf.2 hlegacy
  have hnewprogress := split_progress_current _ _ _ _ _ _ _ hnext
  Exists pre table
  sep_apply (restore_cell (&("dp")) n (split+1) right table d ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | trivial

theorem proof_of_mergingStones_entail_wit_13_2 : mergingStones_entail_wit_13_2 := by
  unfold mergingStones_entail_wit_13_2
  left
  intro n stones_addr stones pre table len left right split interval_sum best left_value d hcompare hn hnmax hb hu hmap hp hlen hln hl hfit hr hls hsr hsum hsum0 hsummax hbest0 hbestmax hprogress hk hleft_value
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.missing_i_Zlength (&("dp")) (split+1) 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hm := stone_mass stones n hstones hb hu
  have hlegacy := split_progress_legacy stones table n len left split best hstones hs
    ⟨hlen, hln⟩ ⟨hl, hfit⟩ ⟨hls, by omega⟩ ⟨hbest0, hbestmax⟩ hprogress
  have hcf := StoneSplitProgress_candidate_facts__interval_min_core stones table n len left split right best
    interval_sum d hm hnmax hlegacy hr ⟨hls, hk⟩ (by omega) hsum
  dsimp at hcf
  rw [← hleft_value] at hcf
  have hnext := StoneSplitProgress_keep_best__split_loop_step stones table n len left right split
    (left_value + Znth right (Znth (split+1) table d) 0 + interval_sum) best hr hk hcf.1.2 hcompare hcf.2 hlegacy
  have hnewprogress := split_progress_current _ _ _ _ _ _ _ hnext
  Exists pre table
  sep_apply (restore_cell (&("dp")) n (split+1) right table d ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega | trivial

theorem proof_of_mergingStones_entail_wit_15 : mergingStones_entail_wit_15 := by
  unfold mergingStones_entail_wit_15
  right
  intro n stones left len pre table hleft hn hnmax hb hu hmap hp hlen hln hl hlnext hprogress
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    intro l a b hll hb ha hfit
    by_cases hlt : l < len
    · exact hprogress.1 l a b ⟨hll.1, hlt⟩ hb ha hfit
    · have he : l = len := by omega
      subst l
      exact hprogress.2 a b ⟨ha, by omega⟩ hb hfit

theorem proof_of_mergingStones_entail_wit_14 : mergingStones_entail_wit_14 := by
  unfold mergingStones_entail_wit_14
  left
  intro n stones_addr stones best interval_sum split right left len pre table d hk hn hnmax hb hu hmap hp hlen hln hl hfit hr hls hsr hsum hsum0 hsummax hbest0 hbestmax hprogress
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.missing_i_Zlength (&("dp")) left 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hlegacy := split_progress_legacy stones table n len left split best hstones hs
    ⟨hlen, hln⟩ ⟨hl, hfit⟩ ⟨hls, by omega⟩ ⟨hbest0, hbestmax⟩ hprogress
  have he : split = right := by omega
  rw [he] at hlegacy
  have hmin := StoneSplitProgress_complete__interval_min_core stones table n len left right best hr
    (by omega) (by omega) hlegacy
  let updated := replace_Znth left (replace_Znth right best (Znth left table d)) table
  have hd := Znth_indep table left d [] (by rw [htable]; omega)
  have hcell : StoneUpdatedCell stones table updated left right best := by
    refine ⟨⟨by omega, by omega⟩, ?_, ?_, hmin⟩
    · rw [hs.2 left (by omega)]
      omega
    · simp only [updated, hd]
  have hnext := StoneUpdatedCell_to_next_left_progress__table_progress stones table updated n len left right best
    hlegacy.1 hr hfit hcell
  have hnewmap := shape_row_map updated n hnext.1.2.1
  have hnewprogress : StoneLeftProgress stones updated n len (left+1) :=
    ⟨hnext.1.2.2.2, hnext.2.2.2⟩
  Exists pre updated
  sep_apply (merge_cell (&("dp")) n left right best table d ⟨hl, by omega⟩ ⟨by omega, by omega⟩)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | omega

theorem proof_of_mergingStones_entail_wit_16 : mergingStones_entail_wit_16 := by
  unfold mergingStones_entail_wit_16
  left
  intro n stones_addr stones len pre table d hlen hn hnmax hb hu hmap hp hlen0 hln hdone
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.missing_i_Zlength (&("dp")) 0 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hm := stone_mass stones n hstones hb hu
  have hlegacy : StoneLenDoneLegacy stones table n len := ⟨hstones, hs, by omega, hdone⟩
  have hf := StoneLenDone_final_facts__interval_min_core stones table n len d hn hnmax hm hlen hln hlegacy
  have hresult := hf.2.1.toAnnotation
  sep_apply (restore_cell (&("dp")) n 0 (n-1) table d ⟨by omega, hn⟩ ⟨by omega, by omega⟩)
  sep_apply (scratch_rows_to_flat_undef (&("dp")) n n table (by omega))
  sep_apply (intArray.undef_full_to_undef_seg (&("dp")) (n*n))
  sep_apply (intArray.undef_seg_merge_to_undef_full (&("dp")) 0 (n*n) 64 (by constructor <;> nlinarith))
  sep_apply (intArray.full_to_undef_full (&("prefix")) (n+1) pre)
  sep_apply (intArray.undef_full_to_undef_seg (&("prefix")) (n+1))
  sep_apply (intArray.undef_seg_merge_to_undef_full (&("prefix")) 0 (n+1) 9 ⟨by omega, by omega⟩)
  sep_apply (store_int_undef_store_int naive_C_Rules (&("width")) n)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hresult

theorem proof_of_mergingStones_safety_wit_10 : mergingStones_safety_wit_10 := by
  unfold mergingStones_safety_wit_10
  left
  intro n stones_addr stones pre i table hi hn hnmax hb hu hmap hi0 hin hp
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  have hm := stone_mass stones n hstones hb hu
  have hv := hm.2 i ⟨hi0, hi⟩
  have hsum := StoneMassesBounded_sublist_sum_bounds__prefix_math stones n 0 i hm ⟨by omega, hi0⟩ hin
  have he := hp i ⟨hi0, le_refl _⟩
  split_pures <;> dump_pre_spatial <;> simp only [Int.sub_zero, INT_MAX, INT_MIN] <;> omega

theorem proof_of_mergingStones_safety_wit_25 : mergingStones_safety_wit_25 := by
  unfold mergingStones_safety_wit_25
  left
  intro n stones_addr stones left len pre table hfit hn hnmax hb hu hmap hp hlen hln hl hlnext hprogress
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  have hm := stone_mass stones n hstones hb hu
  have hbounds := prefix_interval_bounds stones pre n left (left+len) hm hp ⟨hl, by omega⟩ hfit
  split_pures <;> dump_pre_spatial <;> simp only [Int.sub_add_cancel, INT_MAX, INT_MIN] <;> omega

theorem proof_of_mergingStones_safety_wit_35 : mergingStones_safety_wit_35 := by
  unfold mergingStones_safety_wit_35
  left
  intro n stones_addr stones pre table len left right split interval_sum best left_value d hn hnmax hb hu hmap hp hlen hln hl hfit hr hls hsr hsum hsum0 hsummax hbest0 hbestmax hprogress hk hleft_value
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.missing_i_Zlength (&("dp")) (split+1) 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hm := stone_mass stones n hstones hb hu
  have hlegacy := split_progress_legacy stones table n len left split best hstones hs
    ⟨hlen, hln⟩ ⟨hl, hfit⟩ ⟨hls, by omega⟩ ⟨hbest0, hbestmax⟩ hprogress
  have hchildren := StoneSplitProgress_child_bounds__interval_min_core stones table n len left split right best d
    hm hnmax hlegacy hr ⟨hls, hk⟩ (by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

theorem proof_of_mergingStones_safety_wit_36 : mergingStones_safety_wit_36 := by
  unfold mergingStones_safety_wit_36
  left
  intro n stones_addr stones pre table len left right split interval_sum best left_value d hn hnmax hb hu hmap hp hlen hln hl hfit hr hls hsr hsum hsum0 hsummax hbest0 hbestmax hprogress hk hleft_value
  prop_apply (intArray.full_Zlength stones_addr n stones)
  Intros_p hstones
  prop_apply (array2.missing_i_Zlength (&("dp")) (split+1) 0 n n table)
  Intros_p htable
  simp only [Int.sub_zero] at htable
  have hs := stone_shape table n htable hmap
  have hm := stone_mass stones n hstones hb hu
  have hlegacy := split_progress_legacy stones table n len left split best hstones hs
    ⟨hlen, hln⟩ ⟨hl, hfit⟩ ⟨hls, by omega⟩ ⟨hbest0, hbestmax⟩ hprogress
  have hchildren := StoneSplitProgress_child_bounds__interval_min_core stones table n len left split right best d
    hm hnmax hlegacy hr ⟨hls, hk⟩ (by omega)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MAX, INT_MIN] <;> omega

end SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_proof_manual
