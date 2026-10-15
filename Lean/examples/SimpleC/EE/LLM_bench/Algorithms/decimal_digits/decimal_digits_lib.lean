import ListLib.Base.Positional
import ListLib.General.Length
import SimpleC.SL.LeanPrinterPrelude
import AUXLib.ListLib
namespace SimpleC.EE.LLM_bench.Algorithms.decimal_digits
open AUXLib
def DecimalRowValues (rows : List (List Int)) (lengths : List Int) : List Int :=
  (List.zip rows lengths).map fun rowLength =>
    (sublist 0 rowLength.2 rowLength.1).foldl (fun value digit => 10 * value + digit) 0
end SimpleC.EE.LLM_bench.Algorithms.decimal_digits

namespace SimpleC.EE.LLM_bench.Algorithms.decimal_digits
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev array2 := naive_C_Rules.IntArray2

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

theorem decimal_rows_lengths_from_map (rows : List (List Int)) (width : Int)
    (h : Forall (Eq width) (rows.map Zlength)) : Forall (fun row => Zlength row = width) rows := by
  rw [Forall.iff_forall_mem] at h ⊢
  intro row hr
  exact (h (Zlength row) (List.mem_map.mpr ⟨row, hr, rfl⟩)).symm

theorem decimal_rows_flat_length (rows : List (List Int)) (width : Int)
    (h : Forall (fun row => Zlength row = width) rows) :
    Zlength rows.flatten = Zlength rows * width := by
  induction rows with
  | nil => simp [Zlength_nil]
  | cons row rows ih =>
    have hr : Zlength row = width := h.mem (by simp)
    have ht : Forall (fun row => Zlength row = width) rows :=
      Forall.iff_forall_mem.mpr (by intro r hm; exact h.mem (by simp [hm]))
    rw [List.flatten_cons, Zlength_app, hr, ih ht, Zlength_cons]
    ring

theorem decimal_rows_flat_row (rows : List (List Int)) (width i : Int)
    (hw : 0 ≤ width) (h : Forall (fun row => Zlength row = width) rows)
    (hi : 0 ≤ i ∧ i < Zlength rows) :
    Znth i rows [] = sublist (i*width) ((i+1)*width) rows.flatten := by
  induction rows generalizing i with
  | nil => simp only [Zlength_nil] at hi; omega
  | cons row rows ih =>
    have hr : Zlength row = width := h.mem (by simp)
    have ht : Forall (fun row => Zlength row = width) rows :=
      Forall.iff_forall_mem.mpr (by intro r hm; exact h.mem (by simp [hm]))
    rw [List.flatten_cons]
    by_cases he : i = 0
    · subst i
      change row = sublist (0*width) ((0+1)*width) (row++rows.flatten)
      simp only [Int.zero_mul, Int.zero_add, Int.one_mul]
      have hsplit := ListLib.sublist_split_app_l 0 width row rows.flatten ⟨by omega, hw⟩ (by change width ≤ Zlength row; omega)
      change sublist 0 width (row++rows.flatten) = sublist 0 width row at hsplit
      rw [hsplit]
      exact (sublist_self row width hr.symm).symm
    · have hip : 0 < i := by omega
      rw [Znth_cons [] i row rows hip]
      rw [sublist_split_app_r (i*width) ((i+1)*width) width row rows.flatten hr (by constructor <;> nlinarith)]
      have hlow : i*width-width = (i-1)*width := by ring
      have hhigh : (i+1)*width-width = ((i-1)+1)*width := by ring
      rw [hlow, hhigh]
      exact ih (i-1) ht ⟨by omega, by rw [Zlength_cons] at hi; omega⟩

private theorem decimal_row_to_seg (x lo width : Int) (row : List Int) :
    array2.row_store width x lo row |-- intArray.seg x (lo*width) ((lo+1)*width) row := by
  change intArray.full (x+lo*width*sizeof(INT)) width row |-- _
  sep_apply (intArray.full_to_seg (x+lo*width*sizeof(INT)) width row)
  have hs := ((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (intArray.seg_shift x (lo*width) 0 width row)).2
  have he : lo*width+width = (lo+1)*width := by ring
  simpa only [Int.zero_mul, Int.add_zero, he] using hs

private theorem decimal_rows_rec_flatten (rows : List (List Int)) (x lo hi width : Int)
    (hw : 0 ≤ width) :
    store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store width) x lo hi rows |--
      intArray.seg x (lo*width) (hi*width) rows.flatten := by
  induction rows generalizing lo with
  | nil =>
    simp only [store_array_rec, List.flatten_nil]
    Intros_p he
    subst hi
    sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (intArray.seg_empty x (lo*width) (lo*width))).2)
    split_pure_spatial
    · Intros_p htrue
      exact naive_C_Rules.toContext.derivable1_refl _
    · dump_pre_spatial
      rfl
  | cons row rows ih =>
    simp only [store_array_rec, List.flatten_cons]
    prop_apply (SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.store_array_rec_valid naive_C_Rules.toSeparationLogicSig
      (List Int) (array2.row_store width) x (lo+1) hi rows)
    Intros_p hb
    sep_apply (ih (lo+1))
    sep_apply (decimal_row_to_seg x lo width row)
    sep_apply (intArray.seg_merge_to_seg x (lo*width) ((lo+1)*width) (hi*width) row rows.flatten
      (by constructor <;> nlinarith))
    cancel

theorem decimal_rows_flatten (rows : List (List Int)) (x count width : Int) (hw : 0 ≤ width) :
    array2.full x count width rows |-- intArray.full x (count*width) rows.flatten := by
  change store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store width) x 0 count rows |-- _
  sep_apply (decimal_rows_rec_flatten rows x 0 count width hw)
  simp only [Int.zero_mul]
  sep_apply (intArray.seg_to_full x 0 (count*width) rows.flatten)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  exact naive_C_Rules.toContext.derivable1_refl _

private theorem decimal_rows_rec_unflatten (rows : List (List Int)) (x lo hi width : Int)
    (hw : 0 ≤ width) (hr : Forall (fun row => Zlength row = width) rows)
    (hlen : Zlength rows = hi-lo) :
    intArray.seg x (lo*width) (hi*width) rows.flatten |--
      store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store width) x lo hi rows := by
  induction rows generalizing lo hi with
  | nil =>
    have he : hi = lo := by simp only [Zlength_nil] at hlen; omega
    rw [he]
    simp only [List.flatten_nil, store_array_rec]
    sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
      (intArray.seg_empty x (lo*width) (lo*width))).1)
    split_pure_spatial
    · Intros_p htrue
      exact naive_C_Rules.toContext.derivable1_refl _
    · split_pures <;> dump_pre_spatial <;> trivial
  | cons row rows ih =>
    have hrow : Zlength row = width := hr.mem (by simp)
    have ht : Forall (fun row => Zlength row = width) rows :=
      Forall.iff_forall_mem.mpr (by intro r hm; exact hr.mem (by simp [hm]))
    have htailLen : Zlength rows = hi-(lo+1) := by rw [Zlength_cons] at hlen; omega
    have htailFlat := decimal_rows_flat_length rows width ht
    have hb : lo*width ≤ (lo+1)*width ∧ (lo+1)*width ≤ hi*width := by
      have hz := Zlength_nonneg rows
      constructor <;> nlinarith
    simp only [List.flatten_cons]
    sep_apply (intArray.seg_split_to_seg x (lo*width) ((lo+1)*width) (hi*width) (row++rows.flatten) hb)
    have hdelta : (lo+1)*width-lo*width = width := by ring
    have hprefix : sublist 0 width (row++rows.flatten) = row := by
      have hh := ListLib.sublist_split_app_l 0 width row rows.flatten ⟨by omega, hw⟩ (by change width ≤ Zlength row; omega)
      change sublist 0 width (row++rows.flatten) = sublist 0 width row at hh
      rw [hh]
      exact sublist_self row width hrow.symm
    have htail : sublist width (hi*width-lo*width) (row++rows.flatten) = rows.flatten := by
      rw [sublist_split_app_r width (hi*width-lo*width) width row rows.flatten hrow ⟨le_refl _, by nlinarith⟩, Int.sub_self]
      have he : hi*width-lo*width-width = Zlength rows.flatten := by rw [htailFlat, htailLen]; ring
      rw [he]
      exact sublist_self rows.flatten (Zlength rows.flatten) rfl
    simp only [hdelta, hprefix, htail]
    sep_apply (ih (lo+1) hi ht htailLen)
    have hrowSL : intArray.seg x (lo*width) ((lo+1)*width) row |-- array2.row_store width x lo row := by
      change _ |-- intArray.full (x+lo*width*sizeof(INT)) width row
      have hh := intArray.seg_to_full x (lo*width) ((lo+1)*width) row
      simpa only [hdelta] using hh
    sep_apply hrowSL
    simp only [store_array_rec]
    first | exact naive_C_Rules.toContext.derivable1_refl _ | (cancel; try exact naive_C_Rules.toContext.derivable1_refl _)

theorem decimal_rows_unflatten (rows : List (List Int)) (x count width : Int) (hw : 0 ≤ width)
    (hr : Forall (fun row => Zlength row = width) rows) (hlen : Zlength rows = count) :
    intArray.full x (count*width) rows.flatten |-- array2.full x count width rows := by
  have hh := decimal_rows_rec_unflatten rows x 0 count width hw hr (by simpa only [Int.sub_zero] using hlen)
  simp only [Int.zero_mul] at hh
  change _ |-- store_array_rec naive_C_Rules.toSeparationLogicSig (array2.row_store width) x 0 count rows
  exact naive_C_Rules.toContext.derivable1_trans _ _ _ (intArray.full_to_seg x (count*width) rows.flatten) hh

theorem decimal_rows_concat_unique (rows : List (List Int)) (flat : List Int) (count width : Int)
    (hw : 0 ≤ width) (hr : Forall (fun row => Zlength row = width) rows)
    (hlen : Zlength rows = count) (hflat : Zlength flat = count*width)
    (hlookup : ∀ i, 0 ≤ i ∧ i < count → Znth i rows [] = sublist (i*width) ((i+1)*width) flat) :
    flat = rows.flatten := by
  induction rows generalizing flat count with
  | nil =>
    have hc : count = 0 := by simp only [Zlength_nil] at hlen; omega
    have hf : (flat.length : Int) = 0 := by change (flat.length : Int) = count*width at hflat; simp only [hc, Int.zero_mul] at hflat; exact hflat
    have hn : flat.length = 0 := by omega
    cases flat with
    | nil => rfl
    | cons a rest => simp only [List.length_cons] at hn; omega
  | cons row rows ih =>
    have hrow : Zlength row = width := hr.mem (by simp)
    have ht : Forall (fun row => Zlength row = width) rows :=
      Forall.iff_forall_mem.mpr (by intro r hm; exact hr.mem (by simp [hm]))
    have hcount : Zlength rows = count-1 := by rw [Zlength_cons] at hlen; omega
    have hc : 1 ≤ count := by have hz := Zlength_nonneg rows; omega
    have hfirst := hlookup 0 ⟨by omega, by omega⟩
    change row = sublist (0*width) ((0+1)*width) flat at hfirst
    simp only [Int.zero_mul, Int.zero_add, Int.one_mul] at hfirst
    let tail := sublist width (count*width) flat
    have htailLen : Zlength tail = (count-1)*width := by
      have hh := ListLib.Zlength_sublist width (count*width) flat ⟨hw, by nlinarith⟩ (by change count*width ≤ Zlength flat; omega)
      change Zlength tail = count*width-width at hh
      rw [hh]
      ring
    have htailLookup : ∀ i, 0 ≤ i ∧ i < count-1 → Znth i rows [] = sublist (i*width) ((i+1)*width) tail := by
      intro i hi
      have hh := hlookup (i+1) ⟨by omega, by omega⟩
      rw [Znth_cons [] (i+1) row rows (by omega), Int.add_sub_cancel] at hh
      have hsub := ListLib.Zsublist_Zsublist ((i+1)*width) (count*width) (i*width) width flat hw
        (by constructor <;> nlinarith) (by nlinarith)
      change sublist (i*width) ((i+1)*width) tail = sublist (i*width+width) ((i+1)*width+width) flat at hsub
      have hlow : i*width+width = (i+1)*width := by ring
      have hhigh : (i+1)*width+width = ((i+1)+1)*width := by ring
      rw [hlow, hhigh] at hsub
      exact hh.trans hsub.symm
    have htail := ih tail (count-1) ht hcount htailLen htailLookup
    change sublist width (count*width) flat = rows.flatten at htail
    have hsplit := sublist_split 0 (count*width) width flat ⟨by omega, hw⟩ ⟨by nlinarith, by omega⟩
    rw [sublist_self flat (count*width) hflat.symm, ← hfirst, htail] at hsplit
    exact hsplit

end SimpleC.EE.LLM_bench.Algorithms.decimal_digits
