import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import AUXLib.ListLib.Interval
import Mathlib.Data.List.Basic

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib
open AUXLib


def Pre (w : List Int) : Prop := True

def WeightValues (w : List Int) : Prop :=
  ∀ i, (0 ≤ i ∧ i < Zlength w) → Znth i w 0 = 100 ∨ Znth i w 0 = 200

def FairSplit (w : List Int) : Prop :=
  ∃ chosen : List Int, Zlength chosen = Zlength w ∧ Forall (fun b => b = 0 ∨ b = 1) chosen ∧
    2 * ((chosen.zip w).map (fun q => q.1 * q.2)).foldr (· + ·) 0 = w.foldr (· + ·) 0

def Spec (w : List Int) (out : Int) : Prop := (out = 1 ∧ FairSplit w) ∨ (out = 0 ∧ ¬ FairSplit w)
def SolverReturnBridge (out ret : Int) : Prop := (out = 1 ∧ ret = 1) ∨ (out = 0 ∧ ret = 0)
def UnitWeight (x : Int) : Int := Z.div x 100
def UnitSum (w : List Int) : Int := (w.map UnitWeight).foldr (· + ·) 0

def PrefixUnitTotal (w : List Int) (i total : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength w) ∧ total = UnitSum (sublist 0 i w)

def UnitSelectableSum (w : List Int) (target : Int) : Prop :=
  ∃ chosen : List Int, Zlength chosen = Zlength w ∧ Forall (fun b => b = 0 ∨ b = 1) chosen ∧
    target = ((chosen.zip w).map (fun q => q.1 * UnitWeight q.2)).foldr (· + ·) 0

def ReachTable (w : List Int) (i total : Int) (table : List Int) : Prop :=
  Zlength table = 205 ∧ (∀ k, (0 ≤ k ∧ k < 205) → Znth k table 0 = 0 ∨ Znth k table 0 = 1) ∧
    ∀ k, (0 ≤ k ∧ k ≤ total) → (Znth k table 0 ≠ 0 ↔ UnitSelectableSum (sublist 0 i w) k)

def ReachInnerProgress (w : List Int) (i s total : Int) (table : List Int) : Prop :=
  Zlength table = 205 ∧ (∀ k, (0 ≤ k ∧ k < 205) → Znth k table 0 = 0 ∨ Znth k table 0 = 1) ∧
    (∀ k, (0 ≤ k ∧ k ≤ total) → s < k → (Znth k table 0 ≠ 0 ↔ UnitSelectableSum (sublist 0 (i + 1) w) k)) ∧
    ∀ k, (0 ≤ k ∧ k ≤ total) → k ≤ s → (Znth k table 0 ≠ 0 ↔ UnitSelectableSum (sublist 0 i w) k)


theorem weight_values_of_explicit_require (w : List Int) (n : Int) (hn : n=Zlength w)
    (h : ∀ i, 0≤i ∧ i<n → Znth i w 0=100 ∨ Znth i w 0=200) : WeightValues w :=
  fun i hi => h i (by omega)

theorem weight_at_from_pre__prefix_scan (weights : List Int) (i : Int)
    (hw : WeightValues weights) (hi : 0≤i ∧ i<Zlength weights) :
    Znth i weights 0=100 ∨ Znth i weights 0=200 := hw i hi

theorem unit_weight_at_from_pre__prefix_scan (weights : List Int) (i : Int)
    (hw : WeightValues weights) (hi : 0≤i ∧ i<Zlength weights) :
    UnitWeight (Znth i weights 0)=1 ∨ UnitWeight (Znth i weights 0)=2 := by
  rcases hw i hi with he|he <;> rw [he]
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fold_right_Z_add_acc__inner_dp_transitions (l : List Int) (acc : Int) :
    l.foldr (·+·) acc=l.foldr (·+·) 0+acc := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons,ih];omega

theorem fold_right_Z_add_singleton__inner_dp_transitions (z : Int) : [z].foldr (·+·) 0=z := by simp

private theorem fold_add_append (a b : List Int) : (a++b).foldr (·+·) 0=a.foldr (·+·) 0+b.foldr (·+·) 0 := by
  rw [List.foldr_append,fold_right_Z_add_acc__inner_dp_transitions]

theorem prefix_unit_total_step__prefix_scan (weights : List Int) (i total : Int)
    (hi : 0≤i ∧ i<Zlength weights) (ht : PrefixUnitTotal weights i total) :
    PrefixUnitTotal weights (i+1) (total+UnitWeight (Znth i weights 0)) := by
  rcases ht with ⟨hib,ht⟩
  refine ⟨⟨by omega,by omega⟩,?_⟩
  rw [sublist_split 0 (i+1) i weights ⟨by omega,hi.1⟩ ⟨by omega,by omega⟩,sublist_single 0 i weights hi,ht]
  unfold UnitSum
  rw [List.map_append,fold_add_append]
  simp

theorem reach_table_to_inner_at_total__reach_initialization (w : List Int) (i total : Int) (table : List Int)
    (h : ReachTable w i total table) : ReachInnerProgress w i total total table :=
  ⟨h.1,h.2.1,fun k hk hgt => False.elim (by omega),fun k hk _ => h.2.2 k hk⟩

theorem pre_unit_weight_bounds__reach_initialization (w : List Int) (i : Int)
    (hw : WeightValues w) (hi : 0≤i ∧ i<Zlength w) : 1≤UnitWeight (Znth i w 0) ∧ UnitWeight (Znth i w 0)≤2 := by
  have hh := unit_weight_at_from_pre__prefix_scan w i hw hi
  omega

theorem pre_weight_classification__reach_initialization (w : List Int) (i : Int)
    (hw : WeightValues w) (hi : 0≤i ∧ i<Zlength w) : Znth i w 0=100 ∨ Znth i w 0=200 := hw i hi

private theorem weights_forall (w : List Int) (hw : WeightValues w) : Forall (fun x => x=100 ∨ x=200) w := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i,hi,he⟩
  have hh := hw (i:Int) ⟨by omega,by change (i:Int)<(w.length:Int);omega⟩
  change w.getD i 0=100 ∨ w.getD i 0=200 at hh
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he] using hh

theorem pre_unit_sum_lower_bound__reach_initialization (w : List Int) (hw : WeightValues w) : Zlength w≤UnitSum w := by
  have hh := weights_forall w hw
  clear hw
  induction hh with
  | nil => decide
  | @cons x xs hx ht ih =>
    unfold UnitSum at *
    rw [Zlength_cons,List.map_cons,List.foldr_cons]
    rcases hx with rfl|rfl
    · change Zlength xs+1≤1+_
      omega
    · change Zlength xs+1≤2+_
      omega

theorem combine_app_same_length__inner_dp_transitions {A B : Type} (l1 l2 : List A) (r1 r2 : List B)
    (h : l1.length=r1.length) : (l1++l2).zip (r1++r2)=l1.zip r1++l2.zip r2 := by
  induction l1 generalizing r1 with
  | nil => cases r1 <;> simp_all
  | cons x l1 ih =>
    cases r1 with
    | nil => simp at h
    | cons y r1 =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      simp only [List.cons_append,List.zip_cons_cons,ih r1 h]

private theorem forall_append {A : Type} (P : A → Prop) (a b : List A) : Forall P (a++b) ↔ Forall P a ∧ Forall P b := by
  simp only [Forall.iff_forall_mem,List.mem_append]
  constructor
  · intro h;exact ⟨fun x hx => h x (Or.inl hx),fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨ha,hb⟩ x (hx|hx)
    · exact ha x hx
    · exact hb x hx

private theorem selected_snoc (chosen w : List Int) (b x : Int) (hlen : chosen.length=w.length) :
    (((chosen++[b]).zip (w++[x])).map (fun q => q.1*UnitWeight q.2)).foldr (·+·) 0=
    ((chosen.zip w).map (fun q => q.1*UnitWeight q.2)).foldr (·+·) 0+b*UnitWeight x := by
  rw [combine_app_same_length__inner_dp_transitions chosen [b] w [x] hlen,List.map_append,fold_add_append]
  simp

theorem unit_selectable_sum_app_singleton__inner_dp_transitions (w : List Int) (x k : Int) :
    UnitSelectableSum (w++[x]) k ↔ UnitSelectableSum w k ∨ UnitSelectableSum w (k-UnitWeight x) := by
  constructor
  · rintro ⟨chosen,hlen,hbits,hsum⟩
    rcases List.eq_nil_or_concat' chosen with rfl|⟨chosenPre,b,rfl⟩
    · rw [Zlength_nil,Zlength_app,Zlength_cons,Zlength_nil] at hlen
      have hw := Zlength_nonneg w
      omega
    · rw [Zlength_app,Zlength_cons,Zlength_nil,Zlength_app,Zlength_cons,Zlength_nil] at hlen
      have hpre : Zlength chosenPre=Zlength w := by omega
      have hnat : chosenPre.length=w.length := Int.ofNat.inj hpre
      rcases (forall_append _ chosenPre [b]).mp hbits with ⟨hpb,hbb⟩
      have hb := hbb.mem (by simp : b∈[b])
      rw [selected_snoc chosenPre w b x hnat] at hsum
      rcases hb with rfl|rfl
      · exact Or.inl ⟨chosenPre,hpre,hpb,by omega⟩
      · exact Or.inr ⟨chosenPre,hpre,hpb,by omega⟩
  · rintro (⟨chosen,hlen,hbits,hsum⟩|⟨chosen,hlen,hbits,hsum⟩)
    · refine ⟨chosen++[0],?_,?_,?_⟩
      · rw [Zlength_app,Zlength_cons,Zlength_nil,Zlength_app,Zlength_cons,Zlength_nil,hlen]
      · exact (forall_append _ chosen [0]).mpr ⟨hbits,Forall.cons (Or.inl rfl) Forall.nil⟩
      · rw [selected_snoc chosen w 0 x (Int.ofNat.inj hlen)]
        omega
    · refine ⟨chosen++[1],?_,?_,?_⟩
      · rw [Zlength_app,Zlength_cons,Zlength_nil,Zlength_app,Zlength_cons,Zlength_nil,hlen]
      · exact (forall_append _ chosen [1]).mpr ⟨hbits,Forall.cons (Or.inr rfl) Forall.nil⟩
      · rw [selected_snoc chosen w 1 x (Int.ofNat.inj hlen)]
        omega

theorem unit_selectable_sum_snoc_cases__inner_dp_transitions (weights : List Int) (i u k : Int)
    (hi : 0≤i ∧ i<Zlength weights) (hu : u=UnitWeight (Znth i weights 0)) :
    UnitSelectableSum (sublist 0 (i+1) weights) k ↔
      UnitSelectableSum (sublist 0 i weights) k ∨ UnitSelectableSum (sublist 0 i weights) (k-u) := by
  rw [sublist_split 0 (i+1) i weights ⟨by omega,hi.1⟩ ⟨by omega,by omega⟩,sublist_single 0 i weights hi,
      unit_selectable_sum_app_singleton__inner_dp_transitions,hu]

theorem Forall_firstn__inner_dp_transitions {A : Type} (P : A → Prop) (n : Nat) (l : List A)
    (h : Forall P l) : Forall P (firstn n l) :=
  Forall.iff_forall_mem.mpr fun x hx => h.mem (List.mem_of_mem_take hx)

theorem Forall_skipn__inner_dp_transitions {A : Type} (P : A → Prop) (n : Nat) (l : List A)
    (h : Forall P l) : Forall P (skipn n l) :=
  Forall.iff_forall_mem.mpr fun x hx => h.mem (List.mem_of_mem_drop hx)

theorem Forall_sublist__inner_dp_transitions {A : Type} (P : A → Prop) (lo hi : Int) (l : List A)
    (h : Forall P l) : Forall P (sublist lo hi l) :=
  Forall_skipn__inner_dp_transitions P lo.toNat _ (Forall_firstn__inner_dp_transitions P hi.toNat l h)

theorem unit_selectable_sum_nonnegative__inner_dp_transitions (w : List Int) (k : Int)
    (hw : Forall (fun x => x=100 ∨ x=200) w) (h : UnitSelectableSum w k) : 0≤k := by
  rcases h with ⟨chosen,hlen,hbits,hsum⟩
  subst k
  induction hbits generalizing w with
  | nil => simp
  | @cons b chosen hb hbits ih =>
    cases w with
    | nil => simp
    | cons x w =>
      cases hw with
      | cons hx hw =>
        have hlen' : Zlength chosen=Zlength w := by rw [Zlength_cons,Zlength_cons] at hlen;omega
        have ht := ih w hw hlen'
        simp only [List.zip_cons_cons,List.map_cons,List.foldr_cons]
        rcases hb with rfl|rfl <;> rcases hx with rfl|rfl
        all_goals change 0≤_+_
        all_goals first | omega | (change 0≤1+_;omega) | (change 0≤2+_;omega)

theorem Zlength_replace_Znth__inner_dp_transitions {A : Type} (l : List A) (i : Int) (v : A) :
    Zlength (replace_Znth i v l)=Zlength l := AUXLib.Zlength_replace_Znth l i v

theorem valid_Znth__inner_dp_transitions (weights : List Int) (i : Int)
    (hw : WeightValues weights) (hi : 0≤i ∧ i<Zlength weights) : Znth i weights 0=100 ∨ Znth i weights 0=200 := hw i hi

theorem unit_weight_quot__inner_dp_transitions (x : Int) (hx : x=100 ∨ x=200) : Z.quot x 100=UnitWeight x := by
  rcases hx with rfl|rfl <;> rfl


theorem reach_inner_finish__inner_dp_transitions (weights : List Int) (i s u total : Int) (table : List Int)
    (hw : WeightValues weights) (hi : 0≤i ∧ i<Zlength weights)
    (hu : u=Z.quot (Znth i weights 0) 100) (hup : 1≤u) (hsu : s<u) (hus : u-1≤s)
    (hr : ReachInnerProgress weights i s total table) : ReachTable weights (i+1) total table := by
  have hunit : u=UnitWeight (Znth i weights 0) := hu.trans (unit_weight_quot__inner_dp_transitions _ (hw i hi))
  have hweights := weights_forall weights hw
  rcases hr with ⟨hlen,hbits,hnew,hold⟩
  refine ⟨hlen,hbits,?_⟩
  intro k hk
  by_cases hsk : s<k
  · exact hnew k hk hsk
  · have hn : ¬UnitSelectableSum (sublist 0 i weights) (k-u) := by
      intro ht
      have hh := unit_selectable_sum_nonnegative__inner_dp_transitions _ (k-u)
        (Forall_sublist__inner_dp_transitions _ 0 i weights hweights) ht
      omega
    rw [unit_selectable_sum_snoc_cases__inner_dp_transitions weights i u k hi hunit]
    have hh := hold k hk (by omega)
    tauto

theorem reach_inner_mark_step__inner_dp_transitions (weights : List Int) (i s u total : Int) (table : List Int)
    (hw : WeightValues weights) (hi : 0≤i ∧ i<Zlength weights)
    (hu : u=Z.quot (Znth i weights 0) 100) (hup : 1≤u) (hsu : s≥u) (hst : s≤total) (ht : total≤200)
    (hr : ReachInnerProgress weights i s total table) (hp : Znth (s-u) table 0≠0) :
    ReachInnerProgress weights i (s-1) total (replace_Znth s 1 table) := by
  have hunit : u=UnitWeight (Znth i weights 0) := hu.trans (unit_weight_quot__inner_dp_transitions _ (hw i hi))
  rcases hr with ⟨hlen,hbits,hnew,hold⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [Zlength_replace_Znth__inner_dp_transitions,hlen]
  · intro k hk
    by_cases he : k=s
    · subst k
      rw [Znth_replace_Znth_Same 0 table s 1 (by omega)]
      exact Or.inr rfl
    · rw [Znth_replace_Znth_Diff 0 table s k 1 (by omega) (by omega) (Ne.symm he)]
      exact hbits k hk
  · intro k hk hb
    by_cases he : k=s
    · subst k
      rw [Znth_replace_Znth_Same 0 table s 1 (by omega),unit_selectable_sum_snoc_cases__inner_dp_transitions weights i u s hi hunit]
      exact ⟨fun _ => Or.inr ((hold (s-u) (by omega) (by omega)).mp hp),fun _ => by omega⟩
    · rw [Znth_replace_Znth_Diff 0 table s k 1 (by omega) (by omega) (Ne.symm he)]
      exact hnew k hk (by omega)
  · intro k hk hb
    rw [Znth_replace_Znth_Diff 0 table s k 1 (by omega) (by omega) (by omega)]
    exact hold k hk (by omega)

theorem reach_inner_skip_step__inner_dp_transitions (weights : List Int) (i s u total : Int) (table : List Int)
    (hw : WeightValues weights) (hi : 0≤i ∧ i<Zlength weights)
    (hu : u=Z.quot (Znth i weights 0) 100) (hup : 1≤u) (hsu : s≥u)
    (hr : ReachInnerProgress weights i s total table) (hp : Znth (s-u) table 0=0) :
    ReachInnerProgress weights i (s-1) total table := by
  have hunit : u=UnitWeight (Znth i weights 0) := hu.trans (unit_weight_quot__inner_dp_transitions _ (hw i hi))
  rcases hr with ⟨hlen,hbits,hnew,hold⟩
  refine ⟨hlen,hbits,?_,fun k hk hb => hold k hk (by omega)⟩
  intro k hk hb
  by_cases he : k=s
  · subst k
    rw [unit_selectable_sum_snoc_cases__inner_dp_transitions weights i u s hi hunit]
    have hn : ¬UnitSelectableSum (sublist 0 i weights) (s-u) := fun hh =>
      ((hold (s-u) (by omega) (by omega)).mpr hh) hp
    have hs := hold s hk (by omega)
    tauto
  · exact hnew k hk (by omega)

theorem weight_sum_unit_scale__final_result (w : List Int)
    (hw : Forall (fun x => x=100 ∨ x=200) w) : w.foldr (·+·) 0=100*UnitSum w := by
  induction hw with
  | nil => rfl
  | @cons x xs hx ht ih =>
    unfold UnitSum at *
    simp only [List.foldr_cons,List.map_cons]
    rw [ih]
    rcases hx with rfl|rfl
    · change 100+100*_=100*(1+_)
      omega
    · change 200+100*_=100*(2+_)
      omega

theorem selected_sum_unit_scale__final_result (w chosen : List Int)
    (hw : Forall (fun x => x=100 ∨ x=200) w) (hlen : Zlength chosen=Zlength w) :
    ((chosen.zip w).map (fun q => q.1*q.2)).foldr (·+·) 0=
      100*((chosen.zip w).map (fun q => q.1*UnitWeight q.2)).foldr (·+·) 0 := by
  induction hw generalizing chosen with
  | nil => cases chosen <;> simp
  | @cons x xs hx ht ih =>
    cases chosen with
    | nil => simp
    | cons b bs =>
      have he : Zlength bs=Zlength xs := by rw [Zlength_cons,Zlength_cons] at hlen;omega
      simp only [List.zip_cons_cons,List.map_cons,List.foldr_cons]
      rw [ih bs he]
      rcases hx with rfl|rfl
      · change b*100+100*_=100*(b*1+_)
        omega
      · change b*200+100*_=100*(b*2+_)
        omega

theorem fair_split_unit_balance__final_result (w chosen : List Int)
    (hw : WeightValues w) (hlen : Zlength chosen=Zlength w) (hb : Forall (fun b => b=0 ∨ b=1) chosen) :
    (2*((chosen.zip w).map (fun q => q.1*q.2)).foldr (·+·) 0=w.foldr (·+·) 0 ↔
      2*((chosen.zip w).map (fun q => q.1*UnitWeight q.2)).foldr (·+·) 0=UnitSum w) := by
  have hweights := weights_forall w hw
  rw [selected_sum_unit_scale__final_result w chosen hweights hlen,weight_sum_unit_scale__final_result w hweights]
  omega

theorem fair_split_iff_half_selectable__final_result (w : List Int) (total : Int)
    (hw : WeightValues w) (ht : total=UnitSum w) (he : Z.modulo total 2=0) :
    FairSplit w ↔ UnitSelectableSum w (Z.div total 2) := by
  have hd := Int.fdiv_mul_add_fmod total 2
  change Z.div total 2*2+Z.modulo total 2=total at hd
  constructor
  · rintro ⟨chosen,hlen,hbits,hgrams⟩
    have hu := (fair_split_unit_balance__final_result w chosen hw hlen hbits).mp hgrams
    exact ⟨chosen,hlen,hbits,by omega⟩
  · rintro ⟨chosen,hlen,hbits,hunits⟩
    exact ⟨chosen,hlen,hbits,(fair_split_unit_balance__final_result w chosen hw hlen hbits).mpr (by omega)⟩

theorem solver_return_bridge_of_bit__final_result (x : Int) (hx : x=0 ∨ x=1) : SolverReturnBridge x x := by
  rcases hx with rfl|rfl
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib
