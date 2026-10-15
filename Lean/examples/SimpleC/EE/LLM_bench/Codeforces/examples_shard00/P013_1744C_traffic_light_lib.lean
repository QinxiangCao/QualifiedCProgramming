import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.List.GetD

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib
open AUXLib


open MaxMinLib

def WaitsUntilGreen (s : List Int) (start wait : Int) : Prop :=
  (0 ≤ start ∧ start < Zlength s) ∧
  min_value_of_subset (· ≤ ·) (fun candidate : Int => (0 ≤ candidate ∧ candidate < Zlength s) ∧
    Znth (Z.modulo (start + candidate) (Zlength s)) s 0 = 103) (fun candidate => candidate) wait

def Pre (current : Int) (s : List Int) : Prop :=
  (1 ≤ Zlength s ∧ Zlength s ≤ 200000) ∧ (current = 114 ∨ current = 121 ∨ current = 103) ∧
  Forall (fun c => c = 114 ∨ c = 121 ∨ c = 103) s ∧ 103 ∈ s ∧ current ∈ s

def Spec (current : Int) (s : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun candidate : Int × Int => Znth candidate.1 s 0 = current ∧
    WaitsUntilGreen s candidate.1 candidate.2) Prod.snd out

def DoubledTrafficChar (s : List Int) (index : Int) : Int := Znth (Z.modulo index (Zlength s)) s 0

def FirstProcessedGreen (s : List Int) (i next : Int) : Prop :=
  (next = -1 ∧ ∀ j, (i < j ∧ j < 2 * Zlength s) → DoubledTrafficChar s j ≠ 103) ∨
  ((i < next ∧ next < 2 * Zlength s) ∧ DoubledTrafficChar s next = 103 ∧
    ∀ j, (i < j ∧ j < next) → DoubledTrafficChar s j ≠ 103)

def ProcessedTrafficMaximum (current : Int) (s : List Int) (i ans : Int) : Prop :=
  max_value_of_subset_with_default (· ≤ ·)
    (fun candidate : Int × Int => i < candidate.1 ∧ Znth candidate.1 s 0 = current ∧
      WaitsUntilGreen s candidate.1 candidate.2) Prod.snd 0 ans

def TrafficScanState (current : Int) (s : List Int) (i ans next : Int) : Prop :=
  FirstProcessedGreen s i next ∧ ProcessedTrafficMaximum current s i ans

private theorem modulo_eq (s : List Int) (i : Int) : Z.modulo i (Zlength s)=i%Zlength s :=
  Int.fmod_eq_emod_of_nonneg i (Zlength_nonneg s)

theorem in_Znth_exists__final_results (x default : Int) (s : List Int) (hx : x ∈ s) :
    ∃ i, (0≤i ∧ i<Zlength s) ∧ Znth i s default=x := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  refine ⟨(i:Int),?_,?_⟩
  · simp only [Zlength,Int.ofNat_eq_coe]; omega
  · simpa only [Znth,Int.toNat_ofNat,List.getD_eq_getElem _ default hi] using he

private theorem wait_info (s : List Int) (i w : Int) (hw : WaitsUntilGreen s i w) :
    (0≤w ∧ w<Zlength s) ∧ DoubledTrafficChar s (i+w)=103 ∧
      ∀ c, (0≤c ∧ c<Zlength s) → DoubledTrafficChar s (i+c)=103 → w≤c := by
  rcases hw.2 with ⟨c,⟨⟨hr,hg⟩,hm⟩,he⟩
  dsimp only at he
  subst w
  exact ⟨hr,hg,fun c hc hg => hm c ⟨hc,hg⟩⟩

theorem waits_until_green_exists__final_results (s : List Int) (start : Int)
    (hi : 0≤start ∧ start<Zlength s) (hg : 103 ∈ s) : ∃ wait, WaitsUntilGreen s start wait := by
  obtain ⟨green,hgr,hgc⟩ := in_Znth_exists__final_results 103 0 s hg
  have hn : 0<Zlength s := by omega
  have hr : 0≤(green-start)%Zlength s ∧ (green-start)%Zlength s<Zlength s :=
    ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hn⟩
  have hc : Znth ((start+(green-start)%Zlength s)%Zlength s) s 0=103 := by
    rw [Int.add_emod_emod,show start+(green-start)=green from by omega,Int.emod_eq_of_lt hgr.1 hgr.2]
    exact hgc
  obtain ⟨w,hg,hw,hm⟩ := min_n_in_range (fun w => Znth ((start+w)%Zlength s) s 0=103)
    (Zlength s-1) (by omega) ⟨(green-start)%Zlength s,⟨hr.1,by omega⟩,hc⟩
  refine ⟨w,hi,w,⟨⟨⟨hw.1,by omega⟩,by simpa only [modulo_eq] using hg⟩,?_⟩,rfl⟩
  intro c hc
  exact hm c ⟨hc.1.1,by omega⟩ (by simpa only [modulo_eq] using hc.2)

theorem waits_until_green_nonnegative__final_results (s : List Int) (start wait : Int)
    (hw : WaitsUntilGreen s start wait) : 0≤wait := (wait_info s start wait hw).1.1

theorem waits_until_green_zero_if_start_green__final_results (s : List Int) (start wait : Int)
    (hi : 0≤start ∧ start<Zlength s) (hg : Znth start s 0=103)
    (hw : WaitsUntilGreen s start wait) : wait=0 := by
  have h := wait_info s start wait hw
  have hm := h.2.2 0 ⟨by omega,by omega⟩ (by
    unfold DoubledTrafficChar
    rw [modulo_eq]
    rw [Int.add_zero,Int.emod_eq_of_lt hi.1 hi.2]
    exact hg)
  omega

theorem first_processed_green_step_nongreen__stable_transition (s : List Int) (i next : Int)
    (hf : FirstProcessedGreen s i next) (hn : DoubledTrafficChar s i≠103) :
    FirstProcessedGreen s (i-1) next := by
  rcases hf with ⟨he,ha⟩ | ⟨hr,hg,ha⟩
  · refine Or.inl ⟨he,?_⟩
    intro j hj
    by_cases he:j=i
    · simpa only [he] using hn
    · exact ha j ⟨by omega,hj.2⟩
  · refine Or.inr ⟨⟨by omega,hr.2⟩,hg,?_⟩
    intro j hj
    by_cases he:j=i
    · simpa only [he] using hn
    · exact ha j ⟨by omega,hj.2⟩

theorem first_processed_green_wait_exact__stable_transition (s : List Int) (i next wait : Int)
    (hi : 0≤i ∧ i<Zlength s) (hn : DoubledTrafficChar s i≠103)
    (hf : FirstProcessedGreen s i next) (hw : WaitsUntilGreen s i wait) : wait=next-i := by
  have h := wait_info s i wait hw
  have hp : 0<wait := by
    by_contra hh
    have he : wait=0 := by omega
    have hg := h.2.1
    rw [he,Int.add_zero] at hg
    exact hn hg
  rcases hf with ⟨he,ha⟩ | ⟨hr,hg,ha⟩
  · exact False.elim (ha (i+wait) ⟨by omega,by omega⟩ h.2.1)
  · have hb : next≤i+wait := by
      by_contra hh
      exact ha (i+wait) ⟨by omega,by omega⟩ h.2.1
    have hc := h.2.2 (next-i) ⟨by omega,by omega⟩ (by simpa only [show i+(next-i)=next from by omega] using hg)
    omega

theorem traffic_scan_state_initial__initialization (current : Int) (lights : List Int)
    (hl : 1≤Zlength lights) : TrafficScanState current lights (2*Zlength lights-1) 0 (-1) := by
  refine ⟨Or.inl ⟨rfl,by intro j hj; omega⟩,Or.inr ⟨?_,rfl⟩⟩
  rintro ⟨p,w⟩ ⟨hp,hc,hw⟩
  have hi := hw.1
  dsimp only at hp hi
  omega

private theorem max_bound (current : Int) (s : List Int) (i ans : Int)
    (hm : ProcessedTrafficMaximum current s i ans) (p w : Int)
    (hp : i<p) (hc : Znth p s 0=current) (hw : WaitsUntilGreen s p w) : w≤ans := by
  rcases hm with ⟨⟨a,⟨ha,hu⟩,he⟩,hn⟩ | ⟨hu,he⟩
  · have hb := hu (p,w) ⟨hp,hc,hw⟩
    dsimp only at hb
    omega
  · have hb := hu (p,w) ⟨hp,hc,hw⟩
    dsimp only at hb
    omega

private theorem max_stable (current : Int) (s : List Int) (i ans : Int)
    (hm : ProcessedTrafficMaximum current s i ans)
    (hex : ∀ w, ¬(Znth i s 0=current ∧ WaitsUntilGreen s i w)) :
    ProcessedTrafficMaximum current s (i-1) ans := by
  apply max_default_eq_forward (·≤·) Prod.snd Prod.snd _ _ 0 ans hm
  · rintro ⟨p,w⟩ ⟨hp,hc,hw⟩
    exact ⟨(p,w),⟨by dsimp only at hp ⊢; omega,hc,hw⟩,le_refl _⟩
  · rintro ⟨p,w⟩ ⟨hp,hc,hw⟩
    have he : p≠i := by intro he; subst p; exact hex w ⟨hc,hw⟩
    exact ⟨(p,w),⟨by dsimp only at hp ⊢; omega,hc,hw⟩,le_refl _⟩

theorem traffic_scan_step_green_noncurrent__green_transition (current : Int) (s : List Int) (i ans next : Int)
    (hi : 0≤i ∧ i<Zlength s) (hg : DoubledTrafficChar s i=103) (hc : Znth i s 0≠current)
    (hs : TrafficScanState current s i ans next) : TrafficScanState current s (i-1) ans i := by
  refine ⟨Or.inr ⟨⟨by omega,by omega⟩,hg,by intro j hj; omega⟩,?_⟩
  exact max_stable current s i ans hs.2 (fun _ h => hc h.1)

theorem traffic_scan_step_green_outside_original__green_transition (current : Int) (s : List Int) (i ans next : Int)
    (hi : Zlength s≤i ∧ i<2*Zlength s) (hg : DoubledTrafficChar s i=103)
    (hs : TrafficScanState current s i ans next) : TrafficScanState current s (i-1) ans i := by
  refine ⟨Or.inr ⟨⟨by omega,hi.2⟩,hg,by intro j hj; omega⟩,?_⟩
  apply max_stable current s i ans hs.2
  intro w h
  have hb := h.2.1
  omega

theorem traffic_scan_step_noncurrent_nongreen__stable_transition (current : Int) (s : List Int) (i ans next : Int)
    (hi : 0≤i ∧ i<Zlength s) (hc : Znth i s 0≠current) (hn : DoubledTrafficChar s i≠103)
    (hs : TrafficScanState current s i ans next) : TrafficScanState current s (i-1) ans next :=
  ⟨first_processed_green_step_nongreen__stable_transition s i next hs.1 hn,
    max_stable current s i ans hs.2 (fun _ h => hc h.1)⟩

theorem traffic_scan_step_nongreen_outside_original__stable_transition (current : Int) (s : List Int) (i ans next : Int)
    (hi : Zlength s≤i) (hn : DoubledTrafficChar s i≠103)
    (hs : TrafficScanState current s i ans next) : TrafficScanState current s (i-1) ans next := by
  refine ⟨first_processed_green_step_nongreen__stable_transition s i next hs.1 hn,?_⟩
  apply max_stable current s i ans hs.2
  intro w h
  have hb := h.2.1
  omega

theorem traffic_scan_step_current_keep__stable_transition (current : Int) (s : List Int) (i ans next : Int)
    (hi : 0≤i ∧ i<Zlength s) (hn : DoubledTrafficChar s i≠103) (hb : next-i≤ans)
    (hs : TrafficScanState current s i ans next) : TrafficScanState current s (i-1) ans next := by
  refine ⟨first_processed_green_step_nongreen__stable_transition s i next hs.1 hn,?_⟩
  have hu : ∀ p w, (i-1<p ∧ Znth p s 0=current ∧ WaitsUntilGreen s p w) → w≤ans := by
    rintro p w ⟨hp,hc,hw⟩
    by_cases he:p=i
    · rw [he] at hw
      rw [first_processed_green_wait_exact__stable_transition s i next w hi hn hs.1 hw]
      exact hb
    · apply max_bound current s i ans hs.2 p w (by omega) hc hw
  rcases hs.2 with ⟨⟨a,⟨ha,hmax⟩,he⟩,hn⟩ | ⟨hmax,he⟩
  · exact Or.inl ⟨⟨a,⟨⟨by have hp:=ha.1; omega,ha.2⟩,fun b hb => by have h:=hu b.1 b.2 hb; omega⟩,he⟩,hn⟩
  · exact Or.inr ⟨fun a ha => by have h:=hu a.1 a.2 ha; omega,he⟩

theorem traffic_scan_step_current_raise__current_max_update (current : Int) (s : List Int) (i ans next : Int)
    (hp : Pre current s) (hi : 0≤i ∧ i<Zlength s) (hc : current≠103)
    (hchar : DoubledTrafficChar s i=current) (hs : TrafficScanState current s i ans next)
    (ha : 0≤ans) (hb : next-i>ans) : TrafficScanState current s (i-1) (next-i) next ∧ next-i≤Zlength s := by
  have hn : DoubledTrafficChar s i≠103 := by rw [hchar]; exact hc
  obtain ⟨w,hw⟩ := waits_until_green_exists__final_results s i hi hp.2.2.2.1
  have he := first_processed_green_wait_exact__stable_transition s i next w hi hn hs.1 hw
  rw [he] at hw
  have hiw := (wait_info s i (next-i) hw).1
  have hc' : Znth i s 0=current := by
    unfold DoubledTrafficChar at hchar
    rw [modulo_eq] at hchar
    simpa only [Int.emod_eq_of_lt hi.1 hi.2] using hchar
  refine ⟨⟨first_processed_green_step_nongreen__stable_transition s i next hs.1 hn,
    Or.inl ⟨⟨(i,next-i),⟨⟨by dsimp only; omega,hc',hw⟩,?_⟩,rfl⟩,by omega⟩⟩,by omega⟩
  rintro ⟨p,v⟩ ⟨hpi,hpc,hpw⟩
  dsimp only at hpi hpc hpw ⊢
  by_cases he:p=i
  · rw [he] at hpw
    rw [first_processed_green_wait_exact__stable_transition s i next v hi hn hs.1 hpw]
  · have hh := max_bound current s i ans hs.2 p v (by omega) hpc hpw
    omega

theorem traffic_scan_exit_implies_spec__final_results (current : Int) (lights : List Int) (i ans next : Int)
    (hi : -1≤i ∧ i<0) (hp : Pre current lights) (hs : TrafficScanState current lights i ans next) :
    Spec current lights ans := by
  have hex : ∀ a : Int×Int, (Znth a.1 lights 0=current ∧ WaitsUntilGreen lights a.1 a.2) → i<a.1 := by
    intro a ha
    have hb := ha.2.1
    omega
  rcases hs.2 with ⟨⟨a,⟨ha,hu⟩,he⟩,hn⟩ | ⟨hu,he⟩
  · exact ⟨a,⟨ha.2,fun b hb => hu b ⟨hex b hb,hb⟩⟩,he⟩
  · obtain ⟨start,hir,hc⟩ := in_Znth_exists__final_results current 0 lights hp.2.2.2.2
    obtain ⟨w,hw⟩ := waits_until_green_exists__final_results lights start hir hp.2.2.2.1
    have hb := hu (start,w) ⟨by dsimp only; omega,hc,hw⟩
    have hn := waits_until_green_nonnegative__final_results lights start w hw
    refine ⟨(start,w),⟨⟨hc,hw⟩,?_⟩,by dsimp only at hb ⊢; omega⟩
    intro b hb'
    have hh := hu b ⟨hex b hb',hb'⟩
    dsimp only at hb hh ⊢
    omega

theorem green_current_spec_zero__final_results (lights : List Int) (hp : Pre 103 lights) : Spec 103 lights 0 := by
  obtain ⟨start,hi,hg⟩ := in_Znth_exists__final_results 103 0 lights hp.2.2.2.1
  obtain ⟨w,hw⟩ := waits_until_green_exists__final_results lights start hi hp.2.2.2.1
  have he := waits_until_green_zero_if_start_green__final_results lights start w hi hg hw
  refine ⟨(start,w),⟨⟨hg,hw⟩,?_⟩,he⟩
  rintro ⟨p,v⟩ ⟨hc,hw⟩
  dsimp only at hc hw ⊢
  rw [waits_until_green_zero_if_start_green__final_results lights p v hw.1 hc hw,he]

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib
