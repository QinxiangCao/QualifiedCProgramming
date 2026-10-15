import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.List.GetD

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib
open AUXLib


open MaxMinLib

def OneMagneticTransfer (before after : List Int) : Prop :=
  after = before ∨ ∃ i j x, (0 ≤ i ∧ i < Zlength before) ∧ (0 ≤ j ∧ j < Zlength before) ∧ i ≠ j ∧
    x > 0 ∧ x ∣ Znth i before 0 ∧ Zlength after = Zlength before ∧
    ∀ k, (0 ≤ k ∧ k < Zlength before) → Znth k after 0 =
      if k = i then Z.div (Znth k before 0) x else if k = j then Znth k before 0 * x else Znth k before 0

def TotalPower (a : List Int) : Int := a.foldr (· + ·) 0

def Pre (a : List Int) : Prop :=
  (2 ≤ Zlength a ∧ Zlength a ≤ 50000) ∧ Forall (fun power => 1 ≤ power ∧ power ≤ 100) a

def Spec (a : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (OneMagneticTransfer a) TotalPower out

def PrefixSummary (a : List Int) (i total least : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength a) ∧ total = TotalPower (sublist 0 i a) ∧
    ((i = 0 ∧ least = 101) ∨ (0 < i ∧ ∃ least_index,
      (0 ≤ least_index ∧ least_index < i) ∧ least = Znth least_index a 0 ∧
      ∀ k, (0 ≤ k ∧ k < i) → least ≤ Znth k a 0))

def EnumeratedCost (a : List Int) (total least i x cost : Int) : Prop :=
  cost = total ∨ ∃ source factor, (0 ≤ source ∧ source < Zlength a) ∧
    (2 ≤ factor ∧ factor ≤ Znth source a 0) ∧ factor ∣ Znth source a 0 ∧
    (source < i ∨ (source = i ∧ factor < x)) ∧
    cost = total - Znth source a 0 - least + Z.div (Znth source a 0) factor + least * factor

def SearchMinimum (a : List Int) (total least i x answer : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (EnumeratedCost a total least i x) (fun cost => cost) answer

private theorem total_cons (h : Int) (t : List Int) : TotalPower (h::t)=h+TotalPower t := rfl
private theorem total_append (a b : List Int) : TotalPower (a++b)=TotalPower a+TotalPower b := by
  induction a with
  | nil => simp only [List.nil_append]; change TotalPower b=0+TotalPower b; omega
  | cons h t ih => simp only [List.cons_append,total_cons,ih]; omega

private theorem tail_bound (h : Int) (t : List Int) (v : Int)
    (hb : ∀ k, (0≤k ∧ k<Zlength (h::t)) → v≤Znth k (h::t) 0) :
    (v≤h) ∧ ∀ k, (0≤k ∧ k<Zlength t) → v≤Znth k t 0 := by
  constructor
  · exact hb 0 ⟨by omega,by rw [Zlength_cons]; have ht:=Zlength_nonneg t; omega⟩
  · intro k hk
    have hx := hb (k+1) ⟨by omega,by rw [Zlength_cons]; omega⟩
    rw [Znth_cons 0 (k+1) h t (by omega),Int.add_sub_cancel] at hx
    exact hx

theorem total_power_nonnegative__arithmetic_safety (a : List Int)
    (h : ∀ k, (0≤k ∧ k<Zlength a) → 0≤Znth k a 0) : 0≤TotalPower a := by
  induction a with
  | nil => exact le_refl _
  | cons hd t ih =>
    have ht := tail_bound hd t 0 h
    have hx := ih ht.2
    rw [total_cons]
    omega

theorem total_power_dominates_selected__arithmetic_safety (a : List Int) (i : Int)
    (h : ∀ k, (0≤k ∧ k<Zlength a) → 0≤Znth k a 0) (hi : 0≤i ∧ i<Zlength a) :
    Znth i a 0≤TotalPower a := by
  induction a generalizing i with
  | nil => change 0≤i ∧ i<0 at hi; omega
  | cons hd t ih =>
    have ht := tail_bound hd t 0 h
    rw [total_cons]
    by_cases he:i=0
    · rw [he]
      change hd≤hd+TotalPower t
      have hs := total_power_nonnegative__arithmetic_safety t ht.2
      omega
    · rw [Znth_cons 0 i hd t (by omega)]
      have hx := ih (i-1) ht.2 ⟨by omega,by rw [Zlength_cons] at hi; omega⟩
      omega

theorem total_power_dominates_selected_and_lower_bound__arithmetic_safety (a : List Int) (least i : Int)
    (hl : 2≤Zlength a) (hn : ∀ k, (0≤k ∧ k<Zlength a) → 0≤Znth k a 0)
    (hm : ∀ k, (0≤k ∧ k<Zlength a) → least≤Znth k a 0) (hi : 0≤i ∧ i<Zlength a) :
    Znth i a 0+least≤TotalPower a := by
  cases a with
  | nil => change 2≤0 at hl; omega
  | cons hd t =>
    have ht := tail_bound hd t 0 hn
    have hleast := tail_bound hd t least hm
    rw [total_cons]
    by_cases he:i=0
    · rw [he]
      change hd+least≤hd+TotalPower t
      have hti : 0≤(0:Int) ∧ 0<Zlength t := by rw [Zlength_cons] at hl; omega
      have hfirst := hleast.2 0 hti
      have hsum := total_power_dominates_selected__arithmetic_safety t 0 ht.2 hti
      omega
    · rw [Znth_cons 0 i hd t (by omega)]
      have hx := total_power_dominates_selected__arithmetic_safety t (i-1) ht.2 ⟨by omega,by rw [Zlength_cons] at hi; omega⟩
      omega

theorem sublist_full__search_transitions {A : Type} (a : List A) : sublist 0 (Zlength a) a=a :=
  sublist_self a (Zlength a) rfl

theorem prefix_summary_total_dominates_source_and_least__arithmetic_safety (a : List Int) (n total least i : Int)
    (hl : 2≤Zlength a) (he : n=Zlength a) (hp : ∀ k, (0≤k ∧ k<Zlength a) → 1≤Znth k a 0)
    (hs : PrefixSummary a n total least) (hi : 0≤i ∧ i<Zlength a) : Znth i a 0+least≤total := by
  rw [he] at hs
  have ht := hs.2.1
  rw [sublist_full__search_transitions] at ht
  rcases hs.2.2 with ⟨hzero,_⟩ | ⟨_,j,hj,hv,hm⟩
  · omega
  · rw [ht]
    exact total_power_dominates_selected_and_lower_bound__arithmetic_safety a least i hl (fun k hk => by have h:=hp k hk; omega) hm hi

theorem total_power_sublist_snoc__prefix_summary (a : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength a) :
    TotalPower (sublist 0 (i+1) a)=TotalPower (sublist 0 i a)+Znth i a 0 := by
  rw [sublist_split 0 (i+1) i a ⟨by omega,hi.1⟩ ⟨by omega,by omega⟩,sublist_single 0 i a hi,total_append]
  change _ + (Znth i a 0+0)=_
  omega

theorem prefix_summary_step_lt__prefix_summary (a : List Int) (i total least : Int)
    (hi : 0≤i ∧ i<Zlength a) (hs : PrefixSummary a i total least) (hlt : Znth i a 0<least) :
    PrefixSummary a (i+1) (total+Znth i a 0) (Znth i a 0) := by
  refine ⟨⟨by omega,by omega⟩,?_,Or.inr ⟨by omega,i,⟨hi.1,by omega⟩,rfl,?_⟩⟩
  · rw [total_power_sublist_snoc__prefix_summary a i hi,← hs.2.1]
  · intro k hk
    by_cases he:k=i
    · rw [he]
    · rcases hs.2.2 with ⟨he,_⟩ | ⟨_,j,hj,hv,hm⟩
      · omega
      · have hh := hm k ⟨hk.1,by omega⟩
        omega

theorem prefix_summary_step_ge__prefix_summary (a : List Int) (i total least : Int)
    (hi : 0<i ∧ i<Zlength a) (hs : PrefixSummary a i total least) (hge : least≤Znth i a 0) :
    PrefixSummary a (i+1) (total+Znth i a 0) least := by
  refine ⟨⟨by omega,by omega⟩,?_,?_⟩
  · rw [total_power_sublist_snoc__prefix_summary a i ⟨by omega,hi.2⟩,← hs.2.1]
  · rcases hs.2.2 with ⟨he,_⟩ | ⟨_,j,hj,hv,hm⟩
    · omega
    · refine Or.inr ⟨by omega,j,⟨hj.1,by omega⟩,hv,?_⟩
      intro k hk
      by_cases he:k=i
      · simpa only [he] using hge
      · exact hm k ⟨hk.1,by omega⟩

private theorem seen_step (a : List Int) (total least i x cost : Int)
    (h : EnumeratedCost a total least i x cost) : EnumeratedCost a total least i (x+1) cost := by
  rcases h with h | ⟨s,f,hs,hf,hd,hseen,hcost⟩
  · exact Or.inl h
  · exact Or.inr ⟨s,f,hs,hf,hd,by rcases hseen with h | ⟨he,h⟩; exact Or.inl h; exact Or.inr ⟨he,by omega⟩,hcost⟩

theorem enumerated_cost_extend_factor__search_transitions (a : List Int) (total least i x cost : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x ∧ x≤Znth i a 0) (hr : Z.rem (Znth i a 0) x=0) :
    EnumeratedCost a total least i (x+1) cost ↔ EnumeratedCost a total least i x cost ∨
      cost=total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x := by
  constructor
  · rintro (he | ⟨s,f,hs,hf,hd,hseen,hcost⟩)
    · exact Or.inl (Or.inl he)
    · by_cases he:s=i ∧ f=x
      · rcases he with ⟨rfl,rfl⟩; exact Or.inr hcost
      · refine Or.inl (Or.inr ⟨s,f,hs,hf,hd,?_,hcost⟩)
        rcases hseen with h | ⟨hs,hf⟩
        · exact Or.inl h
        · exact Or.inr ⟨hs,by omega⟩
  · rintro (h | h)
    · exact seen_step a total least i x cost h
    · exact Or.inr ⟨i,x,hi,hx,Int.dvd_iff_tmod_eq_zero.mpr hr,Or.inr ⟨rfl,by omega⟩,h⟩

theorem search_minimum_extend_factor__search_transitions (a : List Int) (total least i x answer : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x ∧ x≤Znth i a 0) (hr : Z.rem (Znth i a 0) x=0)
    (hm : SearchMinimum a total least i x answer) :
    SearchMinimum a total least i (x+1) (le_min (·≤·) answer (total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x)) := by
  apply min_union_1_right (·≤·) answer (total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x) _ (fun cost => cost) _ _ hm rfl
  intro cost
  rw [enumerated_cost_extend_factor__search_transitions a total least i x cost hi hx hr]
  exact or_congr Iff.rfl eq_comm

theorem search_minimum_extend_factor_lower__search_transitions (a : List Int) (total least i x answer : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x ∧ x≤Znth i a 0) (hr : Z.rem (Znth i a 0) x=0)
    (hb : total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x<answer)
    (hm : SearchMinimum a total least i x answer) :
    SearchMinimum a total least i (x+1) (total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x) := by
  have hs := search_minimum_extend_factor__search_transitions a total least i x answer hi hx hr hm
  rw [MaxMinLib.min_l (fun a b : Int=>a≤b) answer (total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x) (by omega)] at hs
  exact hs

theorem search_minimum_extend_factor_upper__search_transitions (a : List Int) (total least i x answer : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x ∧ x≤Znth i a 0) (hr : Z.rem (Znth i a 0) x=0)
    (hb : answer≤total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x)
    (hm : SearchMinimum a total least i x answer) : SearchMinimum a total least i (x+1) answer := by
  have hs := search_minimum_extend_factor__search_transitions a total least i x answer hi hx hr hm
  rw [MaxMinLib.min_r (·≤·) _ _ hb] at hs
  exact hs

theorem enumerated_cost_skip_nondivisor__search_transitions (a : List Int) (total least i x cost : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x ∧ x≤Znth i a 0) (hr : Z.rem (Znth i a 0) x≠0) :
    EnumeratedCost a total least i (x+1) cost ↔ EnumeratedCost a total least i x cost := by
  refine ⟨?_,seen_step a total least i x cost⟩
  rintro (he | ⟨s,f,hs,hf,hd,hseen,hcost⟩)
  · exact Or.inl he
  · refine Or.inr ⟨s,f,hs,hf,hd,?_,hcost⟩
    rcases hseen with h | ⟨he,h⟩
    · exact Or.inl h
    · refine Or.inr ⟨he,?_⟩
      have hne : f≠x := by
        intro hh
        rw [he,hh] at hd
        exact hr (Int.tmod_eq_zero_of_dvd hd)
      omega

private theorem minimum_congr (P Q : Int → Prop) (answer : Int) (he : ∀ c, P c↔Q c)
    (hm : min_value_of_subset (·≤·) P (fun c=>c) answer) :
    min_value_of_subset (·≤·) Q (fun c=>c) answer := by
  rcases hm with ⟨c,⟨hc,hmin⟩,heq⟩
  exact ⟨c,⟨(he c).mp hc,fun d hd => hmin d ((he d).mpr hd)⟩,heq⟩

theorem search_minimum_skip_nondivisor__search_transitions (a : List Int) (total least i x answer : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x ∧ x≤Znth i a 0) (hr : Z.rem (Znth i a 0) x≠0)
    (hm : SearchMinimum a total least i x answer) : SearchMinimum a total least i (x+1) answer :=
  minimum_congr _ _ answer (fun c => (enumerated_cost_skip_nondivisor__search_transitions a total least i x c hi hx hr).symm) hm

theorem enumerated_cost_advance_source__search_transitions (a : List Int) (total least i x cost : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x) (hdone : Znth i a 0<x ∧ x≤Znth i a 0+1) :
    EnumeratedCost a total least i x cost ↔ EnumeratedCost a total least (i+1) 2 cost := by
  constructor
  · rintro (he | ⟨s,f,hs,hf,hd,hseen,hcost⟩)
    · exact Or.inl he
    · refine Or.inr ⟨s,f,hs,hf,hd,Or.inl ?_,hcost⟩
      rcases hseen with h | ⟨he,h⟩ <;> omega
  · rintro (he | ⟨s,f,hs,hf,hd,hseen,hcost⟩)
    · exact Or.inl he
    · refine Or.inr ⟨s,f,hs,hf,hd,?_,hcost⟩
      by_cases he:s=i
      · refine Or.inr ⟨he,?_⟩
        rw [he] at hf
        omega
      · rcases hseen with h | ⟨he,h⟩
        · exact Or.inl (by omega)
        · omega

theorem search_minimum_advance_source__search_transitions (a : List Int) (total least i x answer : Int)
    (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x) (hdone : Znth i a 0<x ∧ x≤Znth i a 0+1)
    (hm : SearchMinimum a total least i x answer) : SearchMinimum a total least (i+1) 2 answer :=
  minimum_congr _ _ answer (fun c => enumerated_cost_advance_source__search_transitions a total least i x c hi hx hdone) hm

theorem total_power_nonnegative__search_transitions (a : List Int)
    (h : ∀ k, (0≤k ∧ k<Zlength a) → 0≤Znth k a 0) : 0≤TotalPower a :=
  total_power_nonnegative__arithmetic_safety a h

theorem total_power_ge_entry__search_transitions (a : List Int) (i : Int)
    (h : ∀ k, (0≤k ∧ k<Zlength a) → 0≤Znth k a 0) (hi : 0≤i ∧ i<Zlength a) : Znth i a 0≤TotalPower a :=
  total_power_dominates_selected__arithmetic_safety a i h hi

theorem total_power_ge_entry_plus_lower__search_transitions (a : List Int) (i least : Int)
    (hn : ∀ k, (0≤k ∧ k<Zlength a) → 0≤Znth k a 0) (hm : ∀ k, (0≤k ∧ k<Zlength a) → least≤Znth k a 0)
    (_ : 0≤least) (hl : 2≤Zlength a) (hi : 0≤i ∧ i<Zlength a) : Znth i a 0+least≤TotalPower a :=
  total_power_dominates_selected_and_lower_bound__arithmetic_safety a least i hl hn hm hi

theorem enumerated_candidate_nonnegative__search_transitions (a : List Int) (total least i x : Int)
    (hl : 2≤Zlength a) (hi : 0≤i ∧ i<Zlength a) (hx : 2≤x)
    (hp : ∀ k, (0≤k ∧ k<Zlength a) → 1≤Znth k a 0) (hs : PrefixSummary a (Zlength a) total least) :
    0≤total-Znth i a 0-least+Z.div (Znth i a 0) x+least*x := by
  have ht := prefix_summary_total_dominates_source_and_least__arithmetic_safety a (Zlength a) total least i hl rfl hp hs hi
  rcases hs.2.2 with ⟨he,_⟩ | ⟨_,j,hj,hv,hm⟩
  · omega
  · have hh := hp j hj
    have hpi := hp i hi
    have hd : 0≤Z.div (Znth i a 0) x := Int.fdiv_nonneg (by omega) (by omega)
    have hm := Int.mul_nonneg (show 0≤least by omega) (show 0≤x by omega)
    omega

theorem Zlength_replace_Znth__final_spec {A : Type} (l : List A) (i : Int) (v : A) :
    Zlength (replace_Znth i v l)=Zlength l := Zlength_replace_Znth l i v

theorem total_power_replace_Znth__final_spec (a : List Int) (i v : Int) (hi : 0≤i ∧ i<Zlength a) :
    TotalPower (replace_Znth i v a)=TotalPower a-Znth i a 0+v := by
  induction a generalizing i with
  | nil => change 0≤i ∧ i<0 at hi; omega
  | cons hd t ih =>
    by_cases he:i=0
    · subst i
      change v+TotalPower t=hd+TotalPower t-hd+v
      omega
    · rw [replace_Znth_cons i v hd t (by omega),total_cons,Znth_cons 0 i hd t (by omega),total_cons,
        ih (i-1) ⟨by omega,by rw [Zlength_cons] at hi; omega⟩]
      omega

theorem total_power_two_index_update__final_spec (a : List Int) (source recipient factor : Int)
    (hs : 0≤source ∧ source<Zlength a) (hr : 0≤recipient ∧ recipient<Zlength a) (hne : source≠recipient) :
    let after := replace_Znth recipient (Znth recipient a 0*factor) (replace_Znth source (Z.div (Znth source a 0) factor) a)
    Zlength after=Zlength a ∧
    (∀ k, (0≤k ∧ k<Zlength a) → Znth k after 0=
      if k=source then Z.div (Znth k a 0) factor else if k=recipient then Znth k a 0*factor else Znth k a 0) ∧
    TotalPower after=TotalPower a-Znth source a 0-Znth recipient a 0+Z.div (Znth source a 0) factor+Znth recipient a 0*factor := by
  dsimp only
  have hl := Zlength_replace_Znth a source (Z.div (Znth source a 0) factor)
  have hri : 0≤recipient ∧ recipient<Zlength (replace_Znth source (Z.div (Znth source a 0) factor) a) := by rw [hl]; exact hr
  refine ⟨by rw [Zlength_replace_Znth,hl],?_,?_⟩
  · intro k hk
    by_cases hks:k=source
    · subst k
      rw [if_pos rfl,Znth_replace_Znth_Diff 0 _ recipient source _ hri ⟨hs.1,by rw [hl]; exact hs.2⟩ (Ne.symm hne),
        Znth_replace_Znth_Same 0 a source _ hs]
    · rw [if_neg hks]
      by_cases hkr:k=recipient
      · subst k
        rw [if_pos rfl,Znth_replace_Znth_Same 0 _ recipient _ hri]
      · rw [if_neg hkr,Znth_replace_Znth_Diff 0 _ recipient k _ hri ⟨hk.1,by rw [hl]; exact hk.2⟩ (Ne.symm hkr),
          Znth_replace_Znth_Diff 0 a source k _ hs hk (Ne.symm hks)]
  · rw [total_power_replace_Znth__final_spec _ recipient _ hri,
      total_power_replace_Znth__final_spec a source _ hs,Znth_replace_Znth_Diff 0 a source recipient _ hs hr hne]
    ring

theorem least_recipient_minimizes_transfer_cost__final_spec (total source_power least recipient_power factor : Int)
    (hf : 1≤factor) (hl : least≤recipient_power) :
    total-source_power-least+Z.div source_power factor+least*factor≤
      total-source_power-recipient_power+Z.div source_power factor+recipient_power*factor := by nlinarith

theorem enumerated_cost_realizable_or_no_better__final_spec (a : List Int) (total least cost least_index : Int)
    (ht : total=TotalPower a) (hl : 0≤least_index ∧ least_index<Zlength a) (hv : least=Znth least_index a 0)
    (hc : EnumeratedCost a total least (Zlength a) 2 cost) :
    ∃ after,OneMagneticTransfer a after ∧ TotalPower after≤cost := by
  rcases hc with he | ⟨s,f,hs,hf,hd,hseen,hcost⟩
  · exact ⟨a,Or.inl rfl,by omega⟩
  · by_cases hsl:s=least_index
    · rw [hsl] at hf hcost
      have hdiv : 0≤Z.div (Znth least_index a 0) f := Int.fdiv_nonneg (by omega) (by omega)
      refine ⟨a,Or.inl rfl,?_⟩
      nlinarith
    · have hu := total_power_two_index_update__final_spec a s least_index f hs hl hsl
      refine ⟨_,Or.inr ⟨s,least_index,f,hs,hl,hsl,by omega,hd,hu.1,hu.2.1⟩,?_⟩
      rw [hu.2.2]
      rw [hv] at hcost
      omega

private theorem list_eq_of_Znth (a b : List Int) (hl : Zlength a=Zlength b)
    (hv : ∀ k, (0≤k ∧ k<Zlength a) → Znth k a 0=Znth k b 0) : a=b := by
  have hlen : a.length=b.length := by simp only [Zlength,Int.ofNat_eq_coe] at hl; omega
  apply List.ext_getElem hlen
  intro i hi hj
  have hh := hv (i : Int) ⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem a 0 hi,List.getD_eq_getElem b 0 hj] using hh

theorem magnetic_transfer_dominated_by_enumeration__final_spec (a : List Int) (total least least_index : Int) (after : List Int)
    (ht : total=TotalPower a) (hl : 0≤least_index ∧ least_index<Zlength a) (hv : least=Znth least_index a 0)
    (hp : ∀ k, (0≤k ∧ k<Zlength a) → 1≤Znth k a 0)
    (hm : ∀ k, (0≤k ∧ k<Zlength a) → least≤Znth k a 0)
    (htransfer : OneMagneticTransfer a after) :
    ∃ cost,EnumeratedCost a total least (Zlength a) 2 cost ∧ cost≤TotalPower after := by
  rcases htransfer with rfl | ⟨s,r,f,hs,hr,hne,hf,hd,halen,hav⟩
  · exact ⟨total,Or.inl rfl,by omega⟩
  · have hu := total_power_two_index_update__final_spec a s r f hs hr hne
    have hae : after=replace_Znth r (Znth r a 0*f) (replace_Znth s (Z.div (Znth s a 0) f) a) := by
      apply list_eq_of_Znth _ _ (halen.trans hu.1.symm)
      intro k hk
      rw [halen] at hk
      exact (hav k hk).trans (hu.2.1 k hk).symm
    rw [hae,hu.2.2]
    by_cases he:f=1
    · refine ⟨total,Or.inl rfl,?_⟩
      rw [he]
      have hdiv : Z.div (Znth s a 0) 1=Znth s a 0 := Int.fdiv_one _
      rw [hdiv]
      omega
    · have hsp := hp s hs
      have hfu : f≤Znth s a 0 := Int.le_of_dvd (by omega) hd
      refine ⟨_,Or.inr ⟨s,f,hs,⟨by omega,hfu⟩,hd,Or.inl hs.2,rfl⟩,?_⟩
      rw [ht]
      exact least_recipient_minimizes_transfer_cost__final_spec _ _ _ _ _ (by omega) (hm r hr)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib
