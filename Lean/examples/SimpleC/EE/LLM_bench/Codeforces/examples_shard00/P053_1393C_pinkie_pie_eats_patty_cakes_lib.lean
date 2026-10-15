import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib
open AUXLib


open MaxMinLib

def MinimumEqualDistance (a : List Int) (d : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun positions : Int × Int =>
    (0 ≤ positions.1 ∧ positions.1 < positions.2) ∧ positions.2 < Zlength a ∧
    Znth positions.1 a 0 = Znth positions.2 a 0) (fun positions => positions.2 - positions.1 - 1) d

def Pre (a : List Int) : Prop :=
  (2 ≤ Zlength a ∧ Zlength a ≤ 100000) ∧ Forall (fun x => 1 ≤ x ∧ x ≤ Zlength a) a ∧
    ∃ x i j, (0 ≤ i ∧ i < Zlength a) ∧ (0 ≤ j ∧ j < Zlength a) ∧ i ≠ j ∧ Znth i a 0 = x ∧ Znth j a 0 = x

def ArrangementSpec (a : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun candidate : List Int × Int =>
    List.Perm a candidate.1 ∧ MinimumEqualDistance candidate.1 candidate.2) Prod.snd out

def CountPrefix (a : List Int) (i : Int) (counts : List Int) : Prop :=
  Zlength counts = Zlength a + 1 ∧ ∀ value, (0 ≤ value ∧ value ≤ Zlength a) →
    Znth value counts 0 = ((sublist 0 i a).count value : Int)

def MaximumFrequencyPrefix (counts : List Int) (i mx multiplicity : Int) : Prop :=
  (1 ≤ i ∧ i ≤ Zlength counts) ∧ (∀ value, (1 ≤ value ∧ value < i) → Znth value counts 0 ≤ mx) ∧
  ((i = 1 ∧ mx = 0 ∧ multiplicity = 0) ∨
    (1 < i ∧ (∃ value, (1 ≤ value ∧ value < i) ∧ Znth value counts 0 = mx) ∧
      multiplicity = ((sublist 1 i counts).count mx : Int)))

def Spec (a : List Int) (out : Int) : Prop :=
  ∃ counts mx multiplicity, CountPrefix a (Zlength a) counts ∧
    MaximumFrequencyPrefix counts (Zlength a + 1) mx multiplicity ∧
    out = Z.div (Zlength a - multiplicity) (mx - 1) - 1

theorem terminal_frequency_summary_implies_Spec (a counts : List Int) (mx multiplicity : Int)
    (hc : CountPrefix a (Zlength a) counts) (hm : MaximumFrequencyPrefix counts (Zlength a+1) mx multiplicity) :
    Spec a (Z.div (Zlength a-multiplicity) (mx-1)-1) := ⟨counts,mx,multiplicity,hc,hm,rfl⟩

theorem length_replace_nth__counting_invariant {A : Type} (n : Nat) (l : List A) (v : A) :
    (replace_nth n l v).length=l.length := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a l ih => cases n <;> simp only [replace_nth,List.length_cons,ih]

theorem Zlength_replace_Znth__counting_invariant {A : Type} (i : Int) (l : List A) (v : A) :
    Zlength (replace_Znth i v l)=Zlength l := AUXLib.Zlength_replace_Znth l i v

theorem sublist_snoc_at__frequency_transitions (l : List Int) (lo i : Int) (hlo : 0≤lo ∧ lo≤i) (hi : i<Zlength l) :
    sublist lo (i+1) l=sublist lo i l++[Znth i l 0] := by
  rw [sublist_split lo (i+1) i l hlo (by omega),sublist_single 0 i l (by omega)]

theorem count_prefix_step__counting_invariant (a counts : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength a)
    (hv : 0≤Znth i a 0 ∧ Znth i a 0≤Zlength a) (h : CountPrefix a i counts) :
    CountPrefix a (i+1) (replace_Znth (Znth i a 0) (Znth (Znth i a 0) counts 0+1) counts) := by
  refine ⟨by rw [AUXLib.Zlength_replace_Znth]; exact h.1,?_⟩
  intro v hvr
  have hlen := h.1
  rw [sublist_snoc_at__frequency_transitions a 0 i (by omega) hi.2]
  by_cases he : Znth i a 0=v
  · rw [he,Znth_replace_Znth_Same 0 counts v _ (by omega),h.2 v hvr]
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,Bool.true_eq,if_true,Int.natCast_add,Int.natCast_one]
    rfl
  · rw [Znth_replace_Znth_Diff 0 counts (Znth i a 0) v _ (by omega) (by omega) he,h.2 v hvr]
    simp only [List.count_append,List.count_cons,List.count_nil,beq_iff_eq,he,if_false,Nat.add_zero]

theorem maximum_frequency_prefix_zero__counting_invariant (counts : List Int) (h : 1≤Zlength counts) : MaximumFrequencyPrefix counts 1 0 0 := by
  exact ⟨by omega,by intro value hv; omega,Or.inl ⟨rfl,rfl,rfl⟩⟩

theorem Znth_in_range_In__terminal_result (A : Type) (l : List A) (i : Int) (d : A) (hi : 0≤i ∧ i<Zlength l) : Znth i l d∈l := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem count_occ_sublist_zero_above__frequency_transitions (l : List Int) (lo hi mx x : Int)
    (hlo : 0≤lo ∧ lo≤hi) (hhi : hi≤Zlength l) (hb : ∀ k, (lo≤k ∧ k<hi) → Znth k l 0≤mx)
    (hx : mx<x) : (sublist lo hi l).count x=0 := by
  apply List.count_eq_zero_of_not_mem
  intro hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨n,hn,he⟩
  have hlen := sublist_length lo hi l hlo hhi
  have hr : 0≤(n:Int) ∧ (n:Int)<hi-lo := by rw [hlen] at hn; omega
  have hv : Znth (n:Int) (sublist lo hi l) 0=x := by
    simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some] using he
  rw [Znth_sublist 0 lo (n:Int) hi l hlo.1 hr] at hv
  have hh := hb ((n:Int)+lo) (by omega)
  omega

theorem maximum_frequency_prefix_raise__frequency_transitions (counts : List Int) (i mx c : Int)
    (hi : 1≤i) (hil : i<Zlength counts) (h : MaximumFrequencyPrefix counts i mx c) (hr : mx<Znth i counts 0) :
    MaximumFrequencyPrefix counts (i+1) (Znth i counts 0) 1 := by
  refine ⟨by omega,?_,Or.inr ⟨by omega,⟨i,by omega,rfl⟩,?_⟩⟩
  · intro v hv
    by_cases hvi : v=i
    · rw [hvi]
    · have hh := h.2.1 v (by omega)
      omega
  · have hz := count_occ_sublist_zero_above__frequency_transitions counts 1 i mx (Znth i counts 0) (by omega) (by omega) h.2.1 hr
    rw [sublist_snoc_at__frequency_transitions counts 1 i (by omega) hil,List.count_append,hz]
    simp only [List.count_cons,List.count_nil,beq_self_eq_true,Bool.true_eq,if_true]
    rfl

theorem maximum_frequency_prefix_tie__frequency_transitions (counts : List Int) (i mx c : Int)
    (hi : 1≤i) (hil : i<Zlength counts) (h : MaximumFrequencyPrefix counts i mx c) (ht : Znth i counts 0=mx) :
    MaximumFrequencyPrefix counts (i+1) mx (c+1) := by
  have hc : c=((sublist 1 i counts).count mx:Int) := by
    rcases h.2.2 with ⟨rfl,hm,hc⟩ | ⟨hi,hw,hc⟩
    · rw [Zsublist_nil counts 1 1 (le_refl _),List.count_nil]
      exact hc
    · exact hc
  refine ⟨by omega,?_,Or.inr ⟨by omega,⟨i,by omega,ht⟩,?_⟩⟩
  · intro v hv
    by_cases hvi : v=i
    · rw [hvi,ht]
    · exact h.2.1 v (by omega)
  · rw [sublist_snoc_at__frequency_transitions counts 1 i (by omega) hil,List.count_append,ht]
    simp only [List.count_cons,List.count_nil,beq_self_eq_true,Bool.true_eq,if_true,Int.natCast_add,Int.natCast_one]
    omega

theorem maximum_frequency_prefix_below__frequency_transitions (counts : List Int) (i mx c : Int)
    (hi : 1≤i) (hil : i<Zlength counts) (h : MaximumFrequencyPrefix counts i mx c)
    (hn : 0≤Znth i counts 0) (hb : Znth i counts 0≤mx) (hne : Znth i counts 0≠mx) :
    MaximumFrequencyPrefix counts (i+1) mx c := by
  rcases h with ⟨hr,hdom,hcase⟩
  rcases hcase with ⟨hi0,hm0,hc0⟩ | ⟨hi',⟨v,hv,hvm⟩,hc⟩
  · omega
  · refine ⟨by omega,?_,Or.inr ⟨by omega,⟨v,by omega,hvm⟩,?_⟩⟩
    · intro v hv
      by_cases hvi : v=i
      · rw [hvi]; exact hb
      · exact hdom v (by omega)
    · rw [sublist_snoc_at__frequency_transitions counts 1 i (by omega) hil,List.count_append]
      simp only [List.count_cons,List.count_nil,beq_iff_eq,hne,if_false,Nat.add_zero]
      exact hc

private theorem getD_mem {A : Type} (l : List A) (n : Nat) (d : A) (hn : n<l.length) : l.getD n d∈l := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem two_occurrences_nat_count_occ__terminal_result (A : Type) (dec : DecidableEq A) (l : List A) (x d : A) (p q : Nat)
    (hp : p<l.length) (hq : q<l.length) (hne : p≠q) (hpx : l.getD p d=x) (hqx : l.getD q d=x) :
    letI := dec
    2≤l.count x := by
  letI := dec
  induction l generalizing p q with
  | nil => simp only [List.length_nil] at hp; omega
  | cons a l ih =>
    cases p with
    | zero =>
      cases q with
      | zero => exact False.elim (hne rfl)
      | succ q =>
        change a=x at hpx
        subst a
        change l.getD q d=x at hqx
        have hm := getD_mem l q d (by simp only [List.length_cons] at hq; omega)
        rw [hqx] at hm
        have hc := List.count_pos_iff.mpr hm
        rw [List.count_cons_self]
        omega
    | succ p =>
      cases q with
      | zero =>
        change a=x at hqx
        subst a
        change l.getD p d=x at hpx
        have hm := getD_mem l p d (by simp only [List.length_cons] at hp; omega)
        rw [hpx] at hm
        have hc := List.count_pos_iff.mpr hm
        rw [List.count_cons_self]
        omega
      | succ q =>
        change l.getD p d=x at hpx
        change l.getD q d=x at hqx
        have hh := ih p q (by simp only [List.length_cons] at hp; omega) (by simp only [List.length_cons] at hq; omega) (by omega) hpx hqx
        rw [List.count_cons]
        split <;> omega

theorem two_distinct_Znth_count_occ__terminal_result (l : List Int) (x i j : Int)
    (hi : 0≤i ∧ i<Zlength l) (hj : 0≤j ∧ j<Zlength l) (hne : i≠j) (hix : Znth i l 0=x) (hjx : Znth j l 0=x) : 2≤l.count x := by
  apply two_occurrences_nat_count_occ__terminal_result Int inferInstance l x 0 i.toNat j.toNat
  · simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  · simp only [Zlength,Int.ofNat_eq_coe] at hj; omega
  · omega
  · exact hix
  · exact hjx

theorem terminal_frequency_bounds__terminal_result (a counts : List Int) (n i mx c : Int)
    (hn : n=Zlength a) (hp : Pre a) (hi : 1≤i) (hin : i≤n+1) (hdone : i>n)
    (hm0 : 0≤mx) (hmn : mx≤n) (hc0 : 0≤c) (hci : c≤i-1)
    (hcounts : CountPrefix a n counts) (hmax : MaximumFrequencyPrefix counts i mx c) :
    i=n+1 ∧ (2≤mx ∧ mx≤n) ∧ (1≤c ∧ c≤n) := by
  have hie : i=n+1 := by omega
  rcases hp with ⟨hlen,ha,x,p,q,hp,hq,hpq,hpx,hqx⟩
  have hxmem := Znth_in_range_In__terminal_result Int a p 0 hp
  rw [hpx] at hxmem
  have hxrange := ha.mem hxmem
  have htwo := two_distinct_Znth_count_occ__terminal_result a x p q hp hq hpq hpx hqx
  have hfreq := hcounts.2 x (by omega)
  rw [sublist_self a n hn] at hfreq
  have hdom := hmax.2.1 x (by omega)
  have hmtwo : 2≤mx := by omega
  have hcpos : 1≤c := by
    rcases hmax.2.2 with ⟨hi1,hm0,hc0⟩ | ⟨hi',⟨v,hv,hvm⟩,hc⟩
    · omega
    · have hslen := sublist_length 1 i counts (by omega) hmax.1.2
      have hzlen : Zlength (sublist 1 i counts)=i-1 := by
        simp only [Zlength,hslen,Int.ofNat_eq_coe]
        omega
      have hmem := Znth_in_range_In__terminal_result Int (sublist 1 i counts) (v-1) 0 (by omega)
      rw [Znth_sublist 0 1 (v-1) i counts (by omega) (by omega),show v-1+1=v by omega,hvm] at hmem
      have hpos := List.count_pos_iff.mpr hmem
      omega
  exact ⟨hie,⟨hmtwo,hmn⟩,by omega⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib
