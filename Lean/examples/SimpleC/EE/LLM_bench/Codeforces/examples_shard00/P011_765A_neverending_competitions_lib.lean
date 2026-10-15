import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib
open AUXLib

abbrev _List_Z := List Int
abbrev _Prod__List_Z__List_Z := List Int × List Int
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none
abbrev fst {A : Type u} {B : Type v} (p : A × B) : A := p.1
abbrev snd {A : Type u} {B : Type v} (p : A × B) : B := p.2

def AirportName (a : List Int) : Prop :=
  Zlength a = 3 ∧ Forall (fun c => 65 ≤ c ∧ c ≤ 90) a

def ItineraryEndsAt (home : List Int) (flights : List (List Int × List Int))
    (current : List Int) : Prop :=
  ∃ (ordered : List (List Int × List Int)) (locations : List (List Int)),
    Permutation flights ordered ∧ Zlength locations = Zlength ordered + 1 ∧
    Znth 0 locations [] = home ∧
    (∀ i : Int, (0 ≤ i ∧ i < Zlength ordered) →
      (Znth i ordered ([], [])).1 = Znth i locations [] ∧
      (Znth i ordered ([], [])).2 = Znth (i + 1) locations []) ∧
    Znth (Zlength locations - 1) locations [] = current

def Pre (home : List Int) (flights : List (List Int × List Int)) : Prop :=
  AirportName home ∧ (1 ≤ Zlength flights ∧ Zlength flights ≤ 100) ∧
  Forall (fun f => AirportName f.1 ∧ AirportName f.2 ∧
    ((f.1 = home ∧ f.2 ≠ home) ∨ (f.1 ≠ home ∧ f.2 = home))) flights ∧
  ∃ current, ItineraryEndsAt home flights current

def Spec (home : List Int) (flights : List (List Int × List Int)) (out : List Int) : Prop :=
  (out = [104,111,109,101] ∧ ItineraryEndsAt home flights home) ∨
  (out = [99,111,110,116,101,115,116] ∧
    ∃ current, current ≠ home ∧ ItineraryEndsAt home flights current)


theorem itinerary_endpoint_parity__return_parity
    (home : List Int) (flights : List (List Int × List Int)) (current : List Int)
    (hf : Forall (fun f => (f.1 = home ∧ f.2 ≠ home) ∨
      (f.1 ≠ home ∧ f.2 = home)) flights)
    (hit : ItineraryEndsAt home flights current) :
    current = home ↔ Z.modulo (Zlength flights) 2 = 0 := by
  rcases hit with ⟨ordered, locations, hp, hlen, hstart, hedges, hend⟩
  have hparity : ∀ k : Nat, (k : Int) ≤ Zlength ordered →
      (Znth (k : Int) locations [] = home ↔ (k : Int) % 2 = 0) := by
    intro k
    induction k with
    | zero =>
      intro hb
      simpa only [Nat.cast_zero, Int.zero_emod, hstart]
    | succ k ih =>
      intro hb
      have hi : (k : Int) < Zlength ordered := by omega
      have hk : k < ordered.length := by exact Int.ofNat_lt.mp hi
      have hm : Znth (k : Int) ordered ([], []) ∈ ordered := by
        simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hk, Option.getD_some] using List.getElem_mem hk
      have hf' := hf.mem (hp.mem_iff.mpr hm)
      have he := hedges k ⟨by omega, hi⟩
      have ih' := ih (by omega)
      simp only [Nat.cast_add, Nat.cast_one]
      rw [he.1, he.2] at hf'
      rcases hf' with ⟨hhome, hnext⟩ | ⟨hnothome, hnext⟩
      · have hmod := ih'.mp hhome
        constructor
        · exact fun hc => False.elim (hnext hc)
        · intro hc
          omega
      · have hmod : (k : Int) % 2 ≠ 0 := fun hh => hnothome (ih'.mpr hh)
        constructor
        · intro _; omega
        · intro _; exact hnext
  have hsame : Zlength flights = Zlength ordered := by
    exact congrArg Int.ofNat hp.length_eq
  have heq : Zlength locations - 1 = Zlength ordered := by omega
  rw [heq] at hend
  rw [hsame, Z.modulo, Int.fmod_eq_emod_of_nonneg _ (by decide), ← hend]
  exact hparity ordered.length (by rfl)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P011_765A_neverending_competitions_lib
