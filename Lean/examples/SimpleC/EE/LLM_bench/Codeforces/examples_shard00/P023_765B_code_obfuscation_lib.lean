import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.List.GetD

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib
open AUXLib


open MaxMinLib

def FirstOccurrence (s : List Int) (c i : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun candidate : Int => (0 ≤ candidate ∧ candidate < Zlength s) ∧ Znth candidate s 0 = c)
    (fun candidate => candidate) i

def ValidObfuscatedNames (s : List Int) : Prop :=
  Forall (fun c => 97 ≤ c ∧ c ≤ 122) s ∧ ∀ c d j,
    97 ≤ c → c < d → d ≤ 122 → FirstOccurrence s d j → ∃ i, FirstOccurrence s c i ∧ i < j

def Pre (s : List Int) : Prop :=
  (1 ≤ Zlength s ∧ Zlength s ≤ 500) ∧ Forall (fun c => 97 ≤ c ∧ c ≤ 122) s

def Spec (s : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ ValidObfuscatedNames s)

def ObfuscationPrefixState (s : List Int) (processed next : Int) : Prop :=
  (0 ≤ processed ∧ processed ≤ Zlength s) ∧ (97 ≤ next ∧ next ≤ 122) ∧
  (∀ c d j, 97 ≤ c → c < d → d ≤ 122 → FirstOccurrence s d j → j < processed → ∃ k, FirstOccurrence s c k ∧ k < j) ∧
  (∀ k, (0 ≤ k ∧ k < processed) → Znth k s 0 ≤ next) ∧
  (∀ c, (97 ≤ c ∧ c < next) → ∃ k, FirstOccurrence s c k ∧ k < processed) ∧
  (next < 122 → ∀ k, (0 ≤ k ∧ k < processed) → Znth k s 0 ≠ next)



set_option maxHeartbeats 2000000

private theorem first_facts (s : List Int) (c i : Int) (h : FirstOccurrence s c i) :
    (0≤i ∧ i<Zlength s) ∧ Znth i s 0=c := by
  obtain ⟨a,⟨ha,_⟩,he⟩:=h
  change a=i at he
  rwa [←he]

theorem nth_app_left (s t : List Int) (i : Int) (hi : 0≤i ∧ i<Zlength s) :
    Znth i (s++t) 0=Znth i s 0 := by
  unfold Znth
  apply List.getD_append
  simp only [Zlength,Int.ofNat_eq_coe] at hi
  omega

theorem obfuscation_prefix_init__initialization (text : List Int) (hl : 1≤Zlength text)
    (hc : ∀ i, (0≤i ∧ i<Zlength text) → 97≤Znth i text 0 ∧ Znth i text 0≤122) :
    ObfuscationPrefixState text 0 97 := by
  refine ⟨by omega,by omega,?_,?_,?_,?_⟩
  · intro c d j hc hcd hd hf hj
    have := first_facts text d j hf
    omega
  · intro k hk;omega
  · intro c hc;omega
  · intro h k hk;omega

theorem app_zero_nonzero_index_lt_length__prefix_transitions (text : List Int) (i : Int)
    (hi : 0≤i ∧ i≤Zlength text) (hn : Znth i (text++[0]) 0≠0) : i<Zlength text := by
  by_contra hh
  have he : i=Zlength text := by omega
  rw [he,app_Znth2 0 text [0] (Zlength text) (by omega),Int.sub_self,Znth0_cons] at hn
  exact hn rfl

private theorem order_step (text : List Int) (i next : Int) (hc : Znth i text 0≤next)
    (hs : ObfuscationPrefixState text i next) :
    ∀ c d j, 97≤c → c<d → d≤122 → FirstOccurrence text d j → j<i+1 →
      ∃ k, FirstOccurrence text c k ∧ k<j := by
  intro c d j hcl hcd hd hf hj
  by_cases hji : j<i
  · exact hs.2.2.1 c d j hcl hcd hd hf hji
  · have he : j=i := by omega
    have hh := (first_facts text d j hf).2
    rw [he] at hh
    obtain ⟨k,hk,hki⟩ := hs.2.2.2.2.1 c (by omega)
    exact ⟨k,hk,by omega⟩

theorem obfuscation_prefix_step_equal_increment__prefix_transitions (text : List Int) (i next : Int)
    (hi : 0≤i ∧ i<Zlength text) (hc : Znth i text 0=next) (hn : next<122)
    (hs : ObfuscationPrefixState text i next) : ObfuscationPrefixState text (i+1) (next+1) := by
  have hord := order_step text i next (by omega) hs
  obtain ⟨hb,hnb,ho,hp,hcomplete,habs⟩ := hs
  refine ⟨by omega,by omega,hord,?_,?_,?_⟩
  · intro k hk
    by_cases hki : k<i
    · have := hp k (by omega);omega
    · have he : k=i := by omega
      rw [he,hc];omega
  · intro c hcc
    by_cases hcn : c<next
    · obtain ⟨k,hkf,hki⟩ := hcomplete c (by omega)
      exact ⟨k,hkf,by omega⟩
    · have he : c=next := by omega
      rw [he]
      refine ⟨i,⟨i,⟨⟨hi,hc⟩,?_⟩,rfl⟩,by omega⟩
      intro b hbb
      change i≤b
      by_contra hh
      exact habs hn b (by omega) hbb.2
  · intro hnext k hk heq
    by_cases hki : k<i
    · have := hp k (by omega);omega
    · have he : k=i := by omega
      rw [he,hc] at heq;omega

theorem obfuscation_prefix_step_below__prefix_transitions (text : List Int) (i next : Int)
    (hi : 0≤i ∧ i<Zlength text) (hcl : 97≤Znth i text 0) (hcu : Znth i text 0≤next)
    (hcn : Znth i text 0≠next) (hs : ObfuscationPrefixState text i next) :
    ObfuscationPrefixState text (i+1) next := by
  have hord := order_step text i next hcu hs
  obtain ⟨hb,hnb,ho,hp,hcomplete,habs⟩ := hs
  refine ⟨by omega,hnb,hord,?_,?_,?_⟩
  · intro k hk
    by_cases hki : k<i
    · exact hp k (by omega)
    · have he : k=i := by omega
      rw [he];exact hcu
  · intro c hc
    obtain ⟨k,hkf,hki⟩ := hcomplete c hc
    exact ⟨k,hkf,by omega⟩
  · intro hn k hk
    by_cases hki : k<i
    · exact habs hn k (by omega)
    · have he : k=i := by omega
      rw [he];exact hcn

theorem obfuscation_prefix_step_max__prefix_transitions (text : List Int) (i next : Int)
    (hi : 0≤i ∧ i<Zlength text) (hc : Znth i text 0=next) (hnl : next≥122) (hnu : next≤122)
    (hs : ObfuscationPrefixState text i next) : ObfuscationPrefixState text (i+1) next := by
  have hord := order_step text i next (by omega) hs
  obtain ⟨hb,hnb,ho,hp,hcomplete,habs⟩ := hs
  refine ⟨by omega,hnb,hord,?_,?_,?_⟩
  · intro k hk
    by_cases hki : k<i
    · exact hp k (by omega)
    · have he : k=i := by omega
      rw [he,hc]
  · intro c hcc
    obtain ⟨k,hkf,hki⟩ := hcomplete c hcc
    exact ⟨k,hkf,by omega⟩
  · intro hn;omega

theorem app_zero_terminator_index_eq_length__final_results (text : List Int) (i : Int)
    (hl : ∀ k, (0≤k ∧ k<Zlength text) → 97≤Znth k text 0)
    (hi : 0≤i ∧ i≤Zlength text) (hz : Znth i (text++[0]) 0=0) : i=Zlength text := by
  by_contra hh
  have hb : 0≤i ∧ i<Zlength text := by omega
  rw [nth_app_left text [0] i hb] at hz
  have := hl i hb
  omega

theorem obfuscation_prefix_success_spec__final_results (text : List Int) (next : Int)
    (hb : ∀ k, (0≤k ∧ k<Zlength text) → 97≤Znth k text 0 ∧ Znth k text 0≤122)
    (hs : ObfuscationPrefixState text (Zlength text) next) : Spec text 1 := by
  refine ⟨Or.inr rfl,⟨?_,fun _=>rfl⟩⟩
  intro he
  refine ⟨?_,?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro x hx
    obtain ⟨k,hk,hx⟩ := List.mem_iff_getElem.mp hx
    have hh:=hb k ⟨by omega,Int.ofNat_lt.mpr hk⟩
    simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some,hx] using hh
  · intro c d j hc hcd hd hf
    exact hs.2.2.1 c d j hc hcd hd hf (first_facts text d j hf).1.2

theorem obfuscation_prefix_failure_spec__final_results (text : List Int) (next i : Int)
    (hg : Znth i (text++[0]) 0>next)
    (hb : ∀ k, (0≤k ∧ k<Zlength text) → 97≤Znth k text 0 ∧ Znth k text 0≤122)
    (hi : 0≤i ∧ i≤Zlength text) (hn : 97≤next ∧ next≤122)
    (hs : ObfuscationPrefixState text i next) (hnz : Znth i (text++[0]) 0≠0) : Spec text 0 := by
  have hil := app_zero_nonzero_index_lt_length__prefix_transitions text i hi hnz
  rw [nth_app_left text [0] i ⟨hi.1,hil⟩] at hg
  have hcur:=hb i ⟨hi.1,hil⟩
  refine ⟨Or.inl rfl,⟨by omega,?_⟩⟩
  intro hv
  obtain ⟨j,hj,hjbound,hjmin⟩ := min_n_in_range (fun k=>Znth k text 0=Znth i text 0) i hi.1 ⟨i,by omega,rfl⟩
  have hfirst : FirstOccurrence text (Znth i text 0) j := by
    refine ⟨j,⟨⟨by omega,hj⟩,?_⟩,rfl⟩
    intro b hb
    change j≤b
    by_cases he : b≤i
    · exact hjmin b ⟨hb.1.1,he⟩ hb.2
    · omega
  obtain ⟨k,hkf,hkj⟩ := hv.2 next (Znth i text 0) j hn.1 hg hcur.2 hfirst
  have hk:=first_facts text next k hkf
  exact False.elim (hs.2.2.2.2.2 (by omega) k (by omega) hk.2)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib
