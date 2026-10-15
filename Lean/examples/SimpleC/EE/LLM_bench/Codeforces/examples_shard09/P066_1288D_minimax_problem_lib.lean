import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
open AUXLib

abbrev _List_Z := List Int
abbrev concat {A : Type} (xs : List (List A)) : List A := xs.flatten


open MaxMinLib
abbrev fst {A B : Type} (p : A × B) : A := p.1
abbrev snd {A B : Type} (p : A × B) : B := p.2

def CombinedEntry (rows : List (List Int)) (i j c : Int) : Int :=
  max (Znth c (Znth i rows []) 0) (Znth c (Znth j rows []) 0)

def PairScore (rows : List (List Int)) (i j score : Int) : Prop :=
  (0 ≤ i ∧ i < Zlength rows) ∧ (0 ≤ j ∧ j < Zlength rows) ∧
    min_value_of_subset (· ≤ ·) (fun v => ∃ c, (0 ≤ c ∧ c < Zlength (Znth i rows [])) ∧ v = CombinedEntry rows i j c) (fun x => x) score

def Pre (rows : List (List Int)) : Prop := ∃ m, (1 ≤ m ∧ m ≤ 8) ∧ Forall (fun row => Zlength row = m) rows

def MatrixEntriesBounded (rows : List (List Int)) : Prop := Forall (Forall (fun x => 0 ≤ x ∧ x ≤ 1000000000)) rows

def Spec (rows : List (List Int)) (out : Int × Int) : Prop :=
  ∃ best, PairScore rows (out.1 - 1) (out.2 - 1) best ∧
    max_value_of_subset (· ≤ ·) (fun v => ∃ i j, PairScore rows i j v) (fun x => x) best

def PairAtLeast (rows : List (List Int)) (threshold i j : Int) : Prop :=
  (0 ≤ i ∧ i < Zlength rows) ∧ (0 ≤ j ∧ j < Zlength rows) ∧
    ∀ c, (0 ≤ c ∧ c < Zlength (Znth 0 rows [])) → threshold ≤ CombinedEntry rows i j c

def FeasibleAtThreshold (rows : List (List Int)) (threshold : Int) : Prop := ∃ i j, PairAtLeast rows threshold i j

def RowMaskPrefix (rows : List (List Int)) (threshold row cols mask : Int) : Prop :=
  (0 ≤ mask ∧ mask < Z.pow 2 cols) ∧ ∀ c, (0 ≤ c ∧ c < cols) →
    (Z.testbit mask c = true ↔ threshold ≤ Znth c (Znth row rows []) 0)

def RepresentativePrefix (rows : List (List Int)) (threshold width processed_rows : Int) (reps : List Int) : Prop :=
  ∀ mask, (0 ≤ mask ∧ mask < Z.pow 2 width) →
    ((Znth mask reps (-1) = -1 ∧ ∀ row, (0 ≤ row ∧ row < processed_rows) → ¬ RowMaskPrefix rows threshold row width mask) ∨
      (∃ row, (0 ≤ row ∧ row < processed_rows) ∧ Znth mask reps (-1) = row ∧ RowMaskPrefix rows threshold row width mask))

def NoCoverPrefix (reps : List Int) (full first_mask next_second_mask : Int) : Prop :=
  ∀ s u, (0 ≤ s ∧ s ≤ full) → (0 ≤ u ∧ u ≤ full) → (s < first_mask ∨ (s = first_mask ∧ u < next_second_mask)) →
    0 ≤ Znth s reps (-1) → 0 ≤ Znth u reps (-1) → Z.lor s u ≠ full

def OptimalPairScore (rows : List (List Int)) (best : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun v => ∃ i j, PairScore rows i j v) (fun x => x) best

def SolverSearchMeaning (rows : List (List Int)) (lo hi current_i current_j : Int) : Prop :=
  ∃ best, OptimalPairScore rows best ∧ (lo ≤ best ∧ best ≤ hi) ∧ PairAtLeast rows lo current_i current_j

private theorem pow2_nat (w : Int) (hw : 0≤w) : Z.pow 2 w=((2^w.toNat:Nat):Int) := by
  obtain ⟨w,rfl⟩ := Int.eq_ofNat_of_zero_le hw
  change (2:Int)^w=((2^w:Nat):Int)
  exact (Int.natCast_pow 2 w).symm

private theorem pow2_pos (w : Int) (hw : 0≤w) : 0<Z.pow 2 w := by
  rw [pow2_nat w hw]
  exact_mod_cast Nat.two_pow_pos w.toNat

private theorem pow2_succ (w : Int) (hw : 0≤w) : Z.pow 2 (w+1)=2*Z.pow 2 w := by
  rw [pow2_nat w hw,pow2_nat (w+1) (by omega),show (w+1).toNat=w.toNat+1 by omega,Nat.pow_succ]
  push_cast
  ring

private theorem mask_bit (b k : Int) (hb : 0≤b) : Z.testbit (Z.pow 2 b) k=decide (b=k) := by
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb
  cases k with
  | ofNat k =>
    change Z.testbit ((2:Int)^b) (Int.ofNat k)=decide (Int.ofNat b=Int.ofNat k)
    have hp : (2:Int)^b=Int.ofNat (2^b) := (Int.natCast_pow 2 b).symm
    rw [hp]
    simp only [Z.testbit,Nat.testBit_two_pow]
    congr 1
    exact propext Int.ofNat_inj.symm
  | negSucc k => simp [Z.testbit]

private theorem high_bit (mask width c : Int) (hm : 0≤mask ∧ mask<Z.pow 2 width)
    (hw : 0≤width) (hc : width≤c) : Z.testbit mask c=false := by
  obtain ⟨m,rfl⟩ := Int.eq_ofNat_of_zero_le hm.1
  obtain ⟨w,rfl⟩ := Int.eq_ofNat_of_zero_le hw
  obtain ⟨c,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤c by omega)
  rw [pow2_nat (w:Int) (by omega)] at hm
  simp only [Int.toNat_natCast,Int.ofNat_eq_coe] at hm hc
  have hmw : m<2^w := by omega
  have hp : 2^w≤2^c := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hmw hp)

private theorem bounded_or (a b w : Int) (ha : 0≤a ∧ a<Z.pow 2 w) (hb : 0≤b ∧ b<Z.pow 2 w) (hw : 0≤w) :
    0≤Z.lor a b ∧ Z.lor a b<Z.pow 2 w := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le ha.1
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  rw [pow2_nat w hw] at ha hb ⊢
  have han : a<2^w.toNat := by (try simp only [Int.ofNat_eq_coe] at ha); omega
  have hbn : b<2^w.toNat := by (try simp only [Int.ofNat_eq_coe] at hb); omega
  have hor := Nat.or_lt_two_pow han hbn
  change 0≤Int.ofNat (a ||| b) ∧ Int.ofNat (a ||| b)<_
  simp only [Int.ofNat_eq_coe]
  omega

private theorem shift_one (w : Int) (hw : 0≤w) : Z.shiftl 1 w=Z.pow 2 w := by
  obtain ⟨w,rfl⟩ := Int.eq_ofNat_of_zero_le hw
  change (1:Int) <<< w=(2:Int)^w
  simp only [Int.shiftLeft_eq,one_mul]

private theorem full_bit (w c : Int) (hw : 0≤w) (hc : 0≤c) : Z.testbit (Z.shiftl 1 w-1) c=decide (c<w) := by
  rw [shift_one w hw,pow2_nat w hw]
  have hpow := Nat.two_pow_pos w.toNat
  have hcast : ((2^w.toNat:Nat):Int)-1=((2^w.toNat-1:Nat):Int) := by omega
  rw [hcast]
  obtain ⟨c,rfl⟩ := Int.eq_ofNat_of_zero_le hc
  change Nat.testBit (2^w.toNat-1) c=decide (Int.ofNat c<w)
  rw [Nat.testBit_two_pow_sub_one]
  congr 1
  apply propext
  simp only [Int.ofNat_eq_coe]
  omega

theorem row_mask_set_next__row_mask_step (rows : List (List Int)) (threshold row j mask : Int)
    (hj : 0≤j) (hs : RowMaskPrefix rows threshold row j mask)
    (he : threshold≤Znth j (Znth row rows []) 0) : RowMaskPrefix rows threshold row (j+1) (Z.lor mask (Z.pow 2 j)) := by
  have hpos := pow2_pos j hj
  refine ⟨?_,?_⟩
  · apply bounded_or mask (Z.pow 2 j) (j+1) _ _ (by omega)
    · rw [pow2_succ j hj]; exact ⟨hs.1.1,by have hm := hs.1.2; omega⟩
    · rw [pow2_succ j hj]; omega
  · intro c hc
    rw [Z.lor_spec,mask_bit j c hj]
    by_cases hjc : j=c
    · subst c
      rw [show decide (j=j)=true from decide_eq_true rfl,Bool.or_true]
      exact ⟨fun _=>he,fun _=>rfl⟩
    · rw [decide_eq_false hjc,Bool.or_false]
      exact hs.2 c (by omega)

theorem row_mask_clear_next__row_mask_step (rows : List (List Int)) (threshold row j mask : Int)
    (hj : 0≤j) (hs : RowMaskPrefix rows threshold row j mask)
    (he : Znth j (Znth row rows []) 0<threshold) : RowMaskPrefix rows threshold row (j+1) mask := by
  have hp := pow2_pos j hj
  refine ⟨?_,?_⟩
  · rw [pow2_succ j hj]; exact ⟨hs.1.1,by have := hs.1.2; omega⟩
  · intro c hc
    by_cases heq : c=j
    · subst c
      rw [high_bit mask j j hs.1 hj (le_refl _)]
      constructor
      · intro h; contradiction
      · intro h; omega
    · exact hs.2 c (by omega)

theorem row_mask_complete_unique__representative_update (rows : List (List Int)) (threshold row width mask1 mask2 : Int)
    (hw : 0≤width) (h1 : RowMaskPrefix rows threshold row width mask1) (h2 : RowMaskPrefix rows threshold row width mask2) : mask1=mask2 := by
  apply Z.bits_inj'
  intro c hc
  by_cases hcw : c<width
  · apply Bool.eq_iff_iff.mpr
    exact (h1.2 c ⟨hc,hcw⟩).trans (h2.2 c ⟨hc,hcw⟩).symm
  · rw [high_bit mask1 width c h1.1 hw (by omega),high_bit mask2 width c h2.1 hw (by omega)]

theorem row_mask_prefix_exists__feasible_outcomes (rows : List (List Int)) (threshold row cols : Int) (hc : 0≤cols) :
    ∃mask, RowMaskPrefix rows threshold row cols mask := by
  obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hc
  induction n with
  | zero => exact ⟨0,⟨by decide,by intro c hc; omega⟩⟩
  | succ n ih =>
    rcases ih (by omega) with ⟨mask,hs⟩
    by_cases he : threshold≤Znth (n:Int) (Znth row rows []) 0
    · exact ⟨Z.lor mask (Z.pow 2 n),row_mask_set_next__row_mask_step rows threshold row n mask (by omega) hs he⟩
    · exact ⟨mask,row_mask_clear_next__row_mask_step rows threshold row n mask (by omega) hs (by omega)⟩

theorem representative_insert__representative_update (rows : List (List Int)) (threshold width i : Int)
    (reps : List Int) (mask : Int) (hw : 0≤width) (hi : 0≤i) (hm : 0≤mask ∧ mask<Z.pow 2 width)
    (hlen : Z.pow 2 width≤Zlength reps) (hs : RepresentativePrefix rows threshold width i reps)
    (he : Znth mask reps (-1) = -1) (hmask : RowMaskPrefix rows threshold i width mask) :
    RepresentativePrefix rows threshold width (i+1) (replace_Znth mask i reps) := by
  intro q hq
  by_cases heq : q=mask
  · subst q
    right
    exact ⟨i,by omega,Znth_replace_Znth_Same (-1) reps mask i (by omega),hmask⟩
  · rw [Znth_replace_Znth_Diff (-1) reps mask q i (by omega) (by omega) (Ne.symm heq)]
    rcases hs q hq with ⟨hz,ha⟩ | ⟨row,hr,he,hp⟩
    · left
      refine ⟨hz,?_⟩
      intro row hr hp
      by_cases he : row=i
      · subst row
        exact heq (row_mask_complete_unique__representative_update rows threshold i width q mask hw hp hmask)
      · exact ha row (by omega) hp
    · exact Or.inr ⟨row,by omega,he,hp⟩

theorem representative_skip__representative_update (rows : List (List Int)) (threshold width i : Int)
    (reps : List Int) (mask : Int) (hw : 0≤width) (hm : 0≤mask ∧ mask<Z.pow 2 width)
    (hs : RepresentativePrefix rows threshold width i reps) (hrep : 0≤Znth mask reps (-1))
    (hmask : RowMaskPrefix rows threshold i width mask) : RepresentativePrefix rows threshold width (i+1) reps := by
  intro q hq
  rcases hs q hq with ⟨hz,ha⟩ | ⟨row,hr,he,hp⟩
  · left
    refine ⟨hz,?_⟩
    intro row hr hp
    by_cases he : row=i
    · subst row
      have hqm := row_mask_complete_unique__representative_update rows threshold i width q mask hw hp hmask
      rw [hqm] at hz
      omega
    · exact ha row (by omega) hp
  · exact Or.inr ⟨row,by omega,he,hp⟩

theorem no_cover_outer_missing__cover_search (reps : List Int) (full s next : Int)
    (hs : NoCoverPrefix reps full s next) (hm : full<next ∨ Znth s reps (-1)<0) : NoCoverPrefix reps full (s+1) 0 := by
  intro a b ha hb hor hra hrb
  apply hs a b ha hb _ hra hrb
  rcases hm with hm | hm
  · omega
  · by_cases he : a=s
    · subst a; omega
    · omega

theorem no_cover_inner_missing__cover_search (reps : List Int) (full s u : Int)
    (hs : NoCoverPrefix reps full s u) (hm : Znth u reps (-1)<0) : NoCoverPrefix reps full s (u+1) := by
  intro a b ha hb hor hra hrb
  apply hs a b ha hb _ hra hrb
  by_cases he : b=u
  · subst b; omega
  · omega

theorem no_cover_inner_noncover__cover_search (reps : List Int) (full s u : Int)
    (hs : NoCoverPrefix reps full s u) (hm : Z.lor s u≠full) : NoCoverPrefix reps full s (u+1) := by
  intro a b ha hb hor hra hrb
  by_cases he : a=s ∧ b=u
  · rcases he with ⟨hea,heb⟩; subst a; subst b; exact hm
  · exact hs a b ha hb (by omega) hra hrb

theorem row_masks_lor_full__feasible_outcomes (rows : List (List Int)) (threshold width i j left right : Int)
    (hw : 0≤width) (he : width=Zlength (Znth 0 rows []))
    (hp : PairAtLeast rows threshold i j) (hl : RowMaskPrefix rows threshold i width left)
    (hr : RowMaskPrefix rows threshold j width right) : Z.lor left right=Z.shiftl 1 width-1 := by
  apply Z.bits_inj'
  intro c hc
  rw [Z.lor_spec,full_bit width c hw hc]
  by_cases hcw : c<width
  · rw [decide_eq_true hcw]
    have hentry := hp.2.2 c (by omega)
    change threshold≤max (Znth c (Znth i rows []) 0) (Znth c (Znth j rows []) 0) at hentry
    rw [Bool.or_eq_true]
    rcases le_max_iff.mp hentry with h | h
    · exact Or.inl ((hl.2 c ⟨hc,hcw⟩).mpr h)
    · exact Or.inr ((hr.2 c ⟨hc,hcw⟩).mpr h)
  · rw [decide_eq_false hcw,high_bit left width c hl.1 hw (by omega),high_bit right width c hr.1 hw (by omega)]
    rfl

theorem row_masks_cover_pair__feasible_outcomes (rows : List (List Int)) (threshold width i j left right : Int)
    (he : width=Zlength (Znth 0 rows [])) (hi : 0≤i ∧ i<Zlength rows) (hj : 0≤j ∧ j<Zlength rows)
    (hl : RowMaskPrefix rows threshold i width left) (hr : RowMaskPrefix rows threshold j width right)
    (hfull : Z.lor left right=Z.shiftl 1 width-1) : PairAtLeast rows threshold i j := by
  refine ⟨hi,hj,?_⟩
  intro c hc
  have hw : 0≤width := by rw [he]; exact Zlength_nonneg _
  have hbit : Z.testbit (Z.shiftl 1 width-1) c=true := by
    rw [full_bit width c hw hc.1,decide_eq_true (by omega : c<width)]
  rw [←hfull,Z.lor_spec] at hbit
  change threshold≤max (Znth c (Znth i rows []) 0) (Znth c (Znth j rows []) 0)
  rw [Bool.or_eq_true] at hbit
  rcases hbit with hbit | hbit
  · exact le_trans ((hl.2 c (by omega)).mp hbit) (le_max_left _ _)
  · exact le_trans ((hr.2 c (by omega)).mp hbit) (le_max_right _ _)

theorem completed_no_cover_excludes_feasible__feasible_outcomes (rows : List (List Int)) (threshold width processed : Int)
    (reps : List Int) (first full : Int) (hw : 0≤width) (hproc : processed=Zlength rows)
    (hwidth : width=Zlength (Znth 0 rows [])) (hfull : full=Z.shiftl 1 width-1)
    (hrep : RepresentativePrefix rows threshold width processed reps) (hnoc : NoCoverPrefix reps full first 0)
    (hfirst : first>full) : ¬FeasibleAtThreshold rows threshold := by
  rintro ⟨i,j,hpair⟩
  rcases row_mask_prefix_exists__feasible_outcomes rows threshold i width hw with ⟨left,hl⟩
  rcases row_mask_prefix_exists__feasible_outcomes rows threshold j width hw with ⟨right,hr⟩
  have hor : Z.lor left right=full := (row_masks_lor_full__feasible_outcomes rows threshold width i j left right hw hwidth hpair hl hr).trans hfull.symm
  have hfe : full=Z.pow 2 width-1 := by rw [hfull,shift_one width hw]
  have hlr : 0≤left ∧ left≤full := by have := hl.1; omega
  have hrr : 0≤right ∧ right≤full := by have := hr.1; omega
  rcases hrep left hl.1 with ⟨_,ha⟩ | ⟨lr,hlb,hle,hlp⟩
  · exact ha i (by have := hpair.1; omega) hl
  · rcases hrep right hr.1 with ⟨_,ha⟩ | ⟨rr,hrb,hre,hrp⟩
    · exact ha j (by have := hpair.2.1; omega) hr
    · exact hnoc left right hlr hrr (by omega) (by omega) (by omega) hor

private theorem znth_mem {A : Type} (l : List A) (d : A) (i : Int) (hi : 0≤i ∧ i<Zlength l) : Znth i l d∈l := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

private theorem forall_of_znth {A : Type} (P : A → Prop) (l : List A) (d : A)
    (hall : ∀i, (0≤i ∧ i<Zlength l) → P (Znth i l d)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i,hi,he⟩
  have h := hall (i:Int) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he] using h

private theorem znth_app_left {A : Type} (d : A) (l l' : List A) (i : Int)
    (hi : 0≤i ∧ i<Zlength l) : Znth i (l++l') d=Znth i l d := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_append_left hn]

theorem quot_nonnegative__solver_semantics (a b : Int) (ha : 0≤a) (hb : 0≤b) : 0≤Z.quot a b := by
  rw [Z.quot,Int.tdiv_eq_ediv_of_nonneg ha]
  exact Int.ediv_nonneg ha hb

theorem half_positive__solver_semantics (a : Int) (ha : 2≤a) : 1≤Z.quot a 2 := by
  rw [Z.quot,Int.tdiv_eq_ediv_of_nonneg (by omega : 0≤a)]
  omega

theorem half_less_than_input__solver_semantics (a : Int) (ha : 0<a) : Z.quot a 2<a := by
  rw [Z.quot,Int.tdiv_eq_ediv_of_nonneg (by omega : 0≤a)]
  omega

theorem Znth_concat_uniform__solver_semantics (rows : List (List Int)) (m : Int) (d : List Int) (i j : Int)
    (hi : 0≤i ∧ i<Zlength rows) (hlen : ∀r, (0≤r ∧ r<Zlength rows) → Zlength (Znth r rows d)=m)
    (hj : 0≤j ∧ j<m) : Znth (i*m+j) (concat rows) 0=Znth j (Znth i rows d) 0 := by
  induction rows generalizing i with
  | nil => simp only [Zlength_nil] at hi; omega
  | cons row rows ih =>
    have hrow : Zlength row=m := hlen 0 (by simp only [Zlength_cons]; have := Zlength_nonneg rows; omega)
    change Znth (i*m+j) (row++rows.flatten) 0=Znth j (Znth i (row::rows) d) 0
    by_cases hz : i=0
    · subst i
      simpa only [zero_mul,zero_add] using znth_app_left 0 row rows.flatten j (by omega)
    · rw [app_Znth2 0 row rows.flatten (i*m+j) (by have hprod := mul_nonneg (show 0≤i-1 by omega) (show 0≤m by omega); nlinarith),Znth_cons d i row rows (by omega)]
      rw [show i*m+j-Zlength row=(i-1)*m+j by rw [hrow]; ring]
      apply ih (i-1) (by simp only [Zlength_cons] at hi; omega)
      intro r hr
      have h := hlen (r+1) (by simp only [Zlength_cons]; omega)
      rw [Znth_cons d (r+1) row rows (by omega)] at h
      simpa only [Int.add_sub_cancel] using h

theorem matrix_entries_bounded_from_flat__solver_semantics (rows : List (List Int)) (n m : Int) (d : List Int)
    (hp : Pre rows) (hn : 0<n) (hnrows : n=Zlength rows) (hm : m=Zlength (Znth 0 rows d))
    (hf : ∀q, (0≤q ∧ q<n*m) → 0≤Znth q (concat rows) 0 ∧ Znth q (concat rows) 0≤1000000000) :
    MatrixEntriesBounded rows := by
  rcases hp with ⟨width,hw,hwidth⟩
  have hlen : ∀r, (0≤r ∧ r<Zlength rows) → Zlength (Znth r rows d)=width :=
    fun r hr=>hwidth.mem (znth_mem rows d r hr)
  have h0 := hlen 0 (by omega)
  have hmw : m=width := by omega
  apply forall_of_znth (Forall (fun x=>0≤x ∧ x≤1000000000)) rows d
  intro r hr
  apply forall_of_znth (fun x=>0≤x ∧ x≤1000000000) (Znth r rows d) 0
  intro c hc
  have hrl := hlen r hr
  rw [←Znth_concat_uniform__solver_semantics rows width d r c hr hlen (by omega)]
  apply hf
  rw [hmw]
  constructor <;> nlinarith

theorem matrix_entry_bounds__solver_semantics (rows : List (List Int)) (r c : Int)
    (he : MatrixEntriesBounded rows) (hr : 0≤r ∧ r<Zlength rows) (hc : 0≤c ∧ c<Zlength (Znth r rows [])) :
    0≤Znth c (Znth r rows []) 0 ∧ Znth c (Znth r rows []) 0≤1000000000 :=
  (he.mem (znth_mem rows [] r hr)).mem (znth_mem (Znth r rows []) 0 c hc)

theorem combined_entry_bounds__solver_semantics (rows : List (List Int)) (i j c : Int)
    (hp : Pre rows) (he : MatrixEntriesBounded rows) (hi : 0≤i ∧ i<Zlength rows) (hj : 0≤j ∧ j<Zlength rows)
    (hc : 0≤c ∧ c<Zlength (Znth i rows [])) : 0≤CombinedEntry rows i j c ∧ CombinedEntry rows i j c≤1000000000 := by
  rcases hp with ⟨m,hm,hwidth⟩
  have hwi := hwidth.mem (znth_mem rows [] i hi)
  have hwj := hwidth.mem (znth_mem rows [] j hj)
  have hai := matrix_entry_bounds__solver_semantics rows i c he hi hc
  have haj := matrix_entry_bounds__solver_semantics rows j c he hj (by omega)
  exact ⟨le_trans hai.1 (le_max_left _ _),max_le hai.2 haj.2⟩

theorem pair_score_bounds__solver_semantics (rows : List (List Int)) (i j score : Int)
    (hp : Pre rows) (he : MatrixEntriesBounded rows) (hs : PairScore rows i j score) : 0≤score ∧ score≤1000000000 := by
  rcases hs with ⟨hi,hj,v,⟨⟨c,hc,hv⟩,hmin⟩,hid⟩
  change v=score at hid
  have hb := combined_entry_bounds__solver_semantics rows i j c hp he hi hj hc
  omega

theorem pair_at_least_score_lower_bound__solver_semantics (rows : List (List Int)) (threshold i j : Int)
    (hp : Pre rows) (he : MatrixEntriesBounded rows) (hat : PairAtLeast rows threshold i j) :
    ∃score, PairScore rows i j score ∧ threshold≤score := by
  rcases hat with ⟨hi,hj,hthreshold⟩
  rcases hp with ⟨m,hm,hwidth⟩
  have hp : Pre rows := ⟨m,hm,hwidth⟩
  have hw0 := hwidth.mem (znth_mem rows [] 0 (by omega))
  have hwi := hwidth.mem (znth_mem rows [] i hi)
  let Q : Int → Prop := fun v=>∃c, (0≤c ∧ c<Zlength (Znth i rows [])) ∧ v=CombinedEntry rows i j c
  have hqe : ∃v, (0≤v ∧ v≤1000000000) ∧ Q v :=
    ⟨CombinedEntry rows i j 0,combined_entry_bounds__solver_semantics rows i j 0 hp he hi hj (by omega),0,by omega,rfl⟩
  rcases min_n_in_range Q 1000000000 (by omega) hqe with ⟨score,hq,hb,hleast⟩
  refine ⟨score,⟨hi,hj,score,⟨hq,?_⟩,rfl⟩,?_⟩
  · intro v hv
    apply hleast v _ hv
    rcases hv with ⟨c,hc,hv⟩
    rw [hv]
    exact combined_entry_bounds__solver_semantics rows i j c hp he hi hj hc
  · rcases hq with ⟨c,hc,hscore⟩
    rw [hscore]
    exact hthreshold c (by omega)

theorem pair_score_implies_pair_at_least__solver_semantics (rows : List (List Int)) (threshold i j score : Int)
    (hp : Pre rows) (hs : PairScore rows i j score) (ht : threshold≤score) : PairAtLeast rows threshold i j := by
  rcases hp with ⟨m,hm,hwidth⟩
  rcases hs with ⟨hi,hj,v,⟨hv,hmin⟩,he⟩
  change v=score at he
  have hw0 := hwidth.mem (znth_mem rows [] 0 (by omega))
  have hwi := hwidth.mem (znth_mem rows [] i hi)
  refine ⟨hi,hj,?_⟩
  intro c hc
  have hh := hmin (CombinedEntry rows i j c) ⟨c,by omega,rfl⟩
  change v≤CombinedEntry rows i j c at hh
  omega

theorem pair_at_least_zero__solver_semantics (rows : List (List Int)) (hp : Pre rows) (he : MatrixEntriesBounded rows)
    (hr : 0<Zlength rows) : PairAtLeast rows 0 0 0 := by
  refine ⟨by omega,by omega,?_⟩
  intro c hc
  exact (combined_entry_bounds__solver_semantics rows 0 0 c hp he (by omega) (by omega) hc).1

theorem optimal_pair_score_exists__solver_semantics (rows : List (List Int)) (hp : Pre rows)
    (he : MatrixEntriesBounded rows) (hr : 0<Zlength rows) : ∃best, OptimalPairScore rows best := by
  have hpair := pair_at_least_zero__solver_semantics rows hp he hr
  rcases pair_at_least_score_lower_bound__solver_semantics rows 0 0 0 hp he hpair with ⟨score0,hs0,h0⟩
  let Q : Int → Prop := fun score=>∃i j, PairScore rows i j score
  have hqe : ∃score, (0≤score ∧ score≤1000000000) ∧ Q score :=
    ⟨score0,pair_score_bounds__solver_semantics rows 0 0 score0 hp he hs0,0,0,hs0⟩
  rcases max_n_in_range Q 1000000000 (by omega) hqe with ⟨best,hq,hb,hgreat⟩
  refine ⟨best,best,⟨hq,?_⟩,rfl⟩
  intro score hs
  apply hgreat score _ hs
  rcases hs with ⟨i,j,hpair⟩
  exact pair_score_bounds__solver_semantics rows i j score hp he hpair

theorem optimal_pair_score_bounds__solver_semantics (rows : List (List Int)) (best : Int)
    (hp : Pre rows) (he : MatrixEntriesBounded rows) (ho : OptimalPairScore rows best) : 0≤best ∧ best≤1000000000 := by
  rcases ho with ⟨score,⟨⟨i,j,hpair⟩,hgreat⟩,hid⟩
  change score=best at hid
  rw [←hid]
  exact pair_score_bounds__solver_semantics rows i j score hp he hpair

theorem feasible_threshold_optimal_bound__solver_semantics (rows : List (List Int)) (best threshold : Int)
    (hp : Pre rows) (he : MatrixEntriesBounded rows) (ho : OptimalPairScore rows best) :
    (FeasibleAtThreshold rows threshold → threshold≤best) ∧ (¬FeasibleAtThreshold rows threshold → best<threshold) := by
  constructor
  · rintro ⟨i,j,hat⟩
    rcases pair_at_least_score_lower_bound__solver_semantics rows threshold i j hp he hat with ⟨score,hscore,hlo⟩
    rcases ho with ⟨w,⟨hw,hgreat⟩,hid⟩
    have hh := hgreat score ⟨i,j,hscore⟩
    change w=best at hid
    change score≤w at hh
    omega
  · intro hnot
    rcases ho with ⟨w,⟨⟨i,j,hscore⟩,hgreat⟩,hid⟩
    change w=best at hid
    by_contra hn
    exact hnot ⟨i,j,pair_score_implies_pair_at_least__solver_semantics rows threshold i j w hp hscore (by omega)⟩

theorem optimal_pair_to_spec__solver_semantics (rows : List (List Int)) (best i j : Int)
    (hp : Pre rows) (he : MatrixEntriesBounded rows) (ho : OptimalPairScore rows best) (hat : PairAtLeast rows best i j) :
    Spec rows (i+1,j+1) := by
  rcases pair_at_least_score_lower_bound__solver_semantics rows best i j hp he hat with ⟨score,hscore,hlo⟩
  have hhi : score≤best := by
    rcases ho with ⟨w,⟨hw,hgreat⟩,hid⟩
    have hh := hgreat score ⟨i,j,hscore⟩
    change w=best at hid
    change score≤w at hh
    omega
  have heq : score=best := by omega
  subst score
  refine ⟨best,?_,ho⟩
  simpa only [Prod.fst,Prod.snd,Int.add_sub_cancel] using hscore

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
