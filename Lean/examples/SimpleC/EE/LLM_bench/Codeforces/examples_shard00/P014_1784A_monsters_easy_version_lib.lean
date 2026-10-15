import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.List.GetD

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib
open AUXLib


open MaxMinLib

def OneSingleDamage (before after : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength before) ∧ Znth i before 0 > 0 ∧
    Zlength after = Zlength before ∧ ∀ j, (0 ≤ j ∧ j < Zlength before) →
      Znth j after 0 = if i = j then Znth j before 0 - 1 else Znth j before 0

def SingleDamageTrace (initial final : List Int) (casts : Int) : Prop :=
  ∃ states, Zlength states = casts + 1 ∧ Znth 0 states [] = initial ∧
    Znth casts states [] = final ∧ ∀ k, (0 ≤ k ∧ k < casts) →
      OneSingleDamage (Znth k states []) (Znth (k + 1) states [])

def OneGlobalDamage (before after : List Int) : Prop :=
  List.Forall₂ (fun before_hp after_hp => after_hp = max 0 (before_hp - 1)) before after

def AMonsterDies (before after : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength before) ∧ Znth i before 0 > 0 ∧ Znth i after 0 = 0

def GlobalSpellCascade (initial final : List Int) : Prop :=
  ∃ states, 2 ≤ Zlength states ∧ Znth 0 states [] = initial ∧ Znth (Zlength states - 1) states [] = final ∧
    (∀ k, (0 ≤ k ∧ k < Zlength states - 1) → OneGlobalDamage (Znth k states []) (Znth (k + 1) states [])) ∧
    (∀ k, (0 ≤ k ∧ k < Zlength states - 2) → AMonsterDies (Znth k states []) (Znth (k + 1) states [])) ∧
    ¬ AMonsterDies (Znth (Zlength states - 2) states []) (Znth (Zlength states - 1) states [])

def KillsWithSingleCasts (initial : List Int) (casts : Int) : Prop :=
  ∃ before_global after_global final before_count after_count,
    SingleDamageTrace initial before_global before_count ∧
    (after_global = before_global ∨ GlobalSpellCascade before_global after_global) ∧
    SingleDamageTrace after_global final after_count ∧ Forall (fun hp => hp = 0) final ∧ casts = before_count + after_count

def Pre (health : List Int) : Prop :=
  (1 ≤ Zlength health ∧ Zlength health ≤ 200000) ∧ Forall (fun hp => 1 ≤ hp ∧ hp ≤ Zlength health) health

def Spec (health : List Int) (out : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (KillsWithSingleCasts health) (fun casts => casts) out

def ZListSum : List Int → Int
  | [] => 0
  | x :: tail => x + ZListSum tail

def CascadePreparation (health prepared : List Int) : Prop :=
  Zlength prepared = Zlength health ∧
  (∀ i, (0 ≤ i ∧ i < Zlength health) → (1 ≤ Znth i prepared 0 ∧ Znth i prepared 0 ≤ Znth i health 0)) ∧
  (0 < Zlength prepared → Znth 0 prepared 0 ≤ 1) ∧
  (∀ i, (0 ≤ i ∧ i < Zlength prepared - 1) → Znth (i + 1) prepared 0 ≤ Znth i prepared 0 + 1)

def MaximalCascadePreparation (health prepared : List Int) : Prop :=
  CascadePreparation health prepared ∧ ∀ alternative, CascadePreparation health alternative →
    ∀ i, (0 ≤ i ∧ i < Zlength health) → Znth i alternative 0 ≤ Znth i prepared 0

def PrefixGreedyState (original sorted : List Int) (processed kept spent : Int) : Prop :=
  (0 ≤ processed ∧ processed ≤ Zlength sorted) ∧ ∃ prepared,
    MaximalCascadePreparation (sublist 0 processed sorted) prepared ∧ kept = prepared.getLastD 0 ∧
    spent = ZListSum (sublist 0 processed sorted) - ZListSum prepared ∧ (processed = Zlength sorted → Spec original spent)

def FullPreparationSpecBridge (original sorted : List Int) : Prop :=
  ∀ prepared, MaximalCascadePreparation sorted prepared → Spec original (ZListSum sorted - ZListSum prepared)



set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem Forall_Znth_bounds__greedy_transitions (xs : List Int) (lo hi : Int)
    (h : ∀ i, (0≤i ∧ i<Zlength xs) → lo≤Znth i xs 0 ∧ Znth i xs 0≤hi) :
    Forall (fun x=>lo≤x ∧ x≤hi) xs := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hx
  have hh := h k ⟨by omega,Int.ofNat_lt.mpr hk⟩
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some,he] using hh

theorem Forall_Znth_elim__greedy_transitions (xs : List Int) (lo hi i : Int)
    (h : Forall (fun x=>lo≤x ∧ x≤hi) xs) (hb : 0≤i ∧ i<Zlength xs) :
    lo≤Znth i xs 0 ∧ Znth i xs 0≤hi := by
  have hk : i.toNat<xs.length := by simp only [Zlength,Int.ofNat_eq_coe] at hb;omega
  have hh:=h.mem (List.getElem_mem hk)
  simpa only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using hh

theorem last_app_singleton__greedy_transitions (xs : List Int) (d x : Int) : (xs++[x]).getLastD d=x := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs => simpa only [List.cons_append,List.getLastD_cons] using ih

theorem ZListSum_app__greedy_transitions (xs ys : List Int) : ZListSum (xs++ys)=ZListSum xs+ZListSum ys := by
  induction xs with
  | nil => simp [ZListSum]
  | cons x xs ih => simp only [List.cons_append,ZListSum,ih];omega

theorem last_as_Znth__greedy_transitions (xs : List Int) (d : Int) (hl : 0<Zlength xs) :
    xs.getLastD d=Znth (Zlength xs-1) xs d := by
  induction xs with
  | nil => simp only [Zlength_nil] at hl;omega
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      have ht : 0<Zlength (b::xs) := by have := Zlength_nonneg xs;rw [Zlength_cons];omega
      rw [Znth_cons d _ _ _ (by simp only [Zlength_cons];have := Zlength_nonneg xs;omega)]
      rw [show Zlength (a::b::xs)-1-1=Zlength (b::xs)-1 by simp only [Zlength_cons];omega]
      simpa only [List.getLastD_cons] using ih ht

private theorem nth_app_left (xs ys : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength xs) :
    Znth i (xs++ys) 0=Znth i xs 0 := by
  unfold Znth
  apply List.getD_append
  simp only [Zlength,Int.ofNat_eq_coe] at hi
  omega

private theorem nth_app_last (xs : List Int) (x : Int) : Znth (Zlength xs) (xs++[x]) 0=x := by
  rw [app_Znth2 0 xs [x] (Zlength xs) (by omega)]
  simp only [Int.sub_self,Znth0_cons]

private theorem sub_length (xs : List Int) (n : Int) (hn : 0≤n ∧ n≤Zlength xs) : Zlength (sublist 0 n xs)=n := by
  have hl : n.toNat≤xs.length := by simp only [Zlength,Int.ofNat_eq_coe] at hn;omega
  unfold Zlength sublist
  rw [Int.toNat_zero,List.drop_zero,List.length_take,Nat.min_eq_left hl]
  simp only [Int.ofNat_eq_coe]
  omega

private theorem nth_sub (xs : List Int) (n i : Int) (hn : 0≤n) (hi : 0≤i ∧ i<n) :
    Znth i (sublist 0 n xs) 0=Znth i xs 0 := by
  simpa only [Int.add_zero] using Znth_sublist 0 0 i n xs (by omega) (by omega)

private theorem preparation_prefix (health alt : List Int) (hp : Int)
    (ha : CascadePreparation (health++[hp]) alt) : CascadePreparation health (sublist 0 (Zlength health) alt) := by
  obtain ⟨hlen,hbounds,hfirst,hadj⟩ := ha
  have hal : Zlength alt=Zlength health+1 := by simpa only [Zlength_app,Zlength_cons,Zlength_nil,Int.zero_add] using hlen
  have hh0:=Zlength_nonneg health
  have hslen := sub_length alt (Zlength health) (by omega)
  refine ⟨hslen,?_,?_,?_⟩
  · intro k hk
    rw [nth_sub alt (Zlength health) k hh0 hk]
    have hh := hbounds k (by simp only [Zlength_app,Zlength_cons,Zlength_nil];omega)
    rw [nth_app_left health [hp] k hk] at hh
    exact hh
  · intro hpos
    rw [hslen] at hpos
    rw [nth_sub alt (Zlength health) 0 hh0 (by omega)]
    exact hfirst (by omega)
  · intro k hk
    rw [hslen] at hk
    rw [nth_sub alt (Zlength health) (k+1) hh0 (by omega),nth_sub alt (Zlength health) k hh0 (by omega)]
    exact hadj k (by omega)

theorem maximal_cascade_preparation_app_step__greedy_transitions (health prepared : List Int) (hp : Int)
    (hm : MaximalCascadePreparation health prepared) (hhp : 1≤hp) :
    MaximalCascadePreparation (health++[hp]) (prepared++[min (prepared.getLastD 0+1) hp]) := by
  obtain ⟨⟨hlen,hbounds,hfirst,hadj⟩,hmax⟩ := hm
  have hp0:=Zlength_nonneg prepared
  have hh0:=Zlength_nonneg health
  have hlast : 0≤prepared.getLastD 0 := by
    cases prepared with
    | nil => exact le_refl _
    | cons p ps =>
      have hpos : 0<Zlength (p::ps) := by simp only [Zlength_cons];have := Zlength_nonneg ps;omega
      rw [last_as_Znth__greedy_transitions _ _ hpos]
      have hh := hbounds (Zlength (p::ps)-1) (by omega)
      omega
  let cap := min (prepared.getLastD 0+1) hp
  have hc0 : 1≤cap := le_min (by omega) hhp
  have hch : cap≤hp := min_le_right _ _
  have hcp : cap≤prepared.getLastD 0+1 := min_le_left _ _
  change MaximalCascadePreparation (health++[hp]) (prepared++[cap])
  constructor
  · refine ⟨by simp only [Zlength_app,Zlength_cons,Zlength_nil];omega,?_,?_,?_⟩
    · intro j hj
      simp only [Zlength_app,Zlength_cons,Zlength_nil] at hj
      by_cases hjp : j<Zlength prepared
      · rw [nth_app_left prepared [cap] j (by omega),nth_app_left health [hp] j (by omega)]
        exact hbounds j (by omega)
      · have he : j=Zlength prepared := by omega
        rw [he,nth_app_last,hlen,nth_app_last]
        exact ⟨hc0,hch⟩
    · intro hpos
      by_cases he : Zlength prepared=0
      · have hpnil : prepared=[] := by apply List.length_eq_zero_iff.mp;simp only [Zlength,Int.ofNat_eq_coe] at he;omega
        simp only [hpnil,List.nil_append,Znth0_cons]
        change min (prepared.getLastD 0+1) hp≤1
        simp only [hpnil,List.getLastD_nil,Int.zero_add,min_eq_left hhp]
        omega
      · rw [nth_app_left prepared [cap] 0 (by omega)]
        exact hfirst (by omega)
    · intro j hj
      simp only [Zlength_app,Zlength_cons,Zlength_nil] at hj
      by_cases hjp : j<Zlength prepared-1
      · rw [nth_app_left prepared [cap] (j+1) (by omega),nth_app_left prepared [cap] j (by omega)]
        exact hadj j (by omega)
      · have he : j=Zlength prepared-1 := by omega
        rw [he,show Zlength prepared-1+1=Zlength prepared by omega,nth_app_last,nth_app_left prepared [cap] _ (by omega)]
        rw [←last_as_Znth__greedy_transitions prepared 0 (by omega)]
        exact hcp
  · intro alt ha j hj
    have halt := ha.1
    simp only [Zlength_app,Zlength_cons,Zlength_nil] at halt hj
    have hal : Zlength alt=Zlength health+1 := by omega
    have hpre := preparation_prefix health alt hp ha
    have hmaxpre : ∀ k, (0≤k ∧ k<Zlength health) → Znth k alt 0≤Znth k prepared 0 := by
      intro k hk
      have hh := hmax (sublist 0 (Zlength health) alt) hpre k hk
      rw [nth_sub alt (Zlength health) k hh0 hk] at hh
      exact hh
    by_cases hjp : j<Zlength prepared
    · rw [nth_app_left prepared [cap] j (by omega)]
      exact hmaxpre j (by omega)
    · have he : j=Zlength prepared := by omega
      rw [he,nth_app_last]
      have hfinal := ha.2.1 (Zlength prepared) (by simp only [Zlength_app,Zlength_cons,Zlength_nil];omega)
      rw [hlen,nth_app_last] at hfinal
      change Znth (Zlength prepared) alt 0≤min (prepared.getLastD 0+1) hp
      apply _root_.le_min
      · by_cases hz : Zlength prepared=0
        · have hpnil : prepared=[] := by apply List.length_eq_zero_iff.mp;simp only [Zlength,Int.ofNat_eq_coe] at hz;omega
          have hh := ha.2.2.1 (by omega)
          simpa only [hz,hpnil,List.getLastD_nil,Int.zero_add] using hh
        · have hprev := hmaxpre (Zlength prepared-1) (by omega)
          rw [←last_as_Znth__greedy_transitions prepared 0 (by omega)] at hprev
          have hh := ha.2.2.2 (Zlength prepared-1) (by omega)
          rw [show Zlength prepared-1+1=Zlength prepared by omega] at hh
          omega
      · simpa only [hlen] using hfinal.2

theorem prefix_greedy_step__greedy_transitions (original sorted : List Int) (processed kept spent next : Int)
    (hi : 0≤processed ∧ processed<Zlength sorted) (hhp : 1≤Znth processed sorted 0)
    (hb : FullPreparationSpecBridge original sorted) (hs : PrefixGreedyState original sorted processed kept spent)
    (hn : next=min (kept+1) (Znth processed sorted 0)) :
    PrefixGreedyState original sorted (processed+1) next (spent+(Znth processed sorted 0-next)) := by
  obtain ⟨hp,prepared,hm,hkept,hspent,hterm⟩ := hs
  have hprefix : sublist 0 (processed+1) sorted=sublist 0 processed sorted++[Znth processed sorted 0] := by
    rw [sublist_split 0 (processed+1) processed sorted (by omega) (by omega),sublist_single 0 processed sorted hi]
  have hmnext : MaximalCascadePreparation (sublist 0 (processed+1) sorted) (prepared++[next]) := by
    rw [hprefix,hn,hkept]
    exact maximal_cascade_preparation_app_step__greedy_transitions _ _ _ hm hhp
  have hcost : spent+(Znth processed sorted 0-next)=ZListSum (sublist 0 (processed+1) sorted)-ZListSum (prepared++[next]) := by
    rw [hprefix,ZListSum_app__greedy_transitions,ZListSum_app__greedy_transitions]
    simp only [ZListSum]
    omega
  refine ⟨by omega,prepared++[next],hmnext,(last_app_singleton__greedy_transitions _ _ _).symm,hcost,?_⟩
  intro hfull
  have hself := sublist_self sorted (processed+1) hfull
  rw [hself] at hmnext hcost
  rw [hcost]
  exact hb _ hmnext
end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib
