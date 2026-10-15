import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib
open AUXLib

abbrev _List_Z := List Int
abbrev concat {A : Type u} (rows : List (List A)) : List A := rows.flatten

def Pixel (c : Int) : Prop := c = 67 ∨ c = 77 ∨ c = 89 ∨ c = 87 ∨ c = 71 ∨ c = 66

def Pre (photo : List (List Int)) : Prop := True

def HasColor (photo : List (List Int)) : Prop :=
  ∃ row c, row ∈ photo ∧ c ∈ row ∧ (c = 67 ∨ c = 77 ∨ c = 89)

def Spec (photo : List (List Int)) (out : Bool) : Prop :=
  (out = true ∧ HasColor photo) ∨ (out = false ∧ ¬ HasColor photo)

def SolverReturnBridge (out : Bool) (ret : Int) : Prop :=
  (out = true ∧ ret = 1) ∨ (out = false ∧ ret = 0)


theorem Zlength_concat_uniform__initialization (rows : List (List Int)) (width : Int)
    (h : Forall (fun row => Zlength row = width) rows) :
    Zlength (concat rows) = Zlength rows * width := by
  induction h with
  | nil => simp only [concat, List.flatten_nil, Zlength_nil, Int.zero_mul]
  | @cons row rows hr hrs ih =>
    simp only [concat, List.flatten_cons, Zlength_app, Zlength_cons] at *
    rw [hr, ih]
    ring

theorem Znth_In_range__results {A : Type u} (l : List A) (i : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) : In (Znth i l d) l := by
  have hk : i.toNat < l.length := by
    cases i with
    | ofNat n => exact Int.ofNat_lt.mp hi.2
    | negSucc n => omega
  simpa only [Znth, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.getD_some] using List.getElem_mem hk

theorem In_Znth_Zlength__results {A : Type u} (l : List A) (x d : A) (hx : In x l) :
    ∃ i, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l d = x := by
  rcases List.mem_iff_getElem.mp hx with ⟨k, hk, he⟩
  refine ⟨k, ⟨by omega, Int.ofNat_lt.mpr hk⟩, ?_⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.getD_some] using he

theorem pre_rectangular_facts__initialization (photo : List (List Int))
    (n m : Int) (d : List Int) (hn : n = Zlength photo)
    (hr : ∀ i, (0 ≤ i ∧ i < n) → Zlength (Znth i photo d) = m) :
    Zlength (concat photo) = n * m := by
  have hall : Forall (fun row => Zlength row = m) photo := by
    apply Forall.iff_forall_mem.mpr
    intro row hrow
    rcases In_Znth_Zlength__results photo row d hrow with ⟨i, hi, he⟩
    have hh := hr i (by rw [hn]; exact hi)
    rwa [he] at hh
  rw [Zlength_concat_uniform__initialization photo m hall, hn]

theorem has_color_concat_characterization__results (photo : List (List Int)) :
    HasColor photo ↔ ∃ c, In c (concat photo) ∧ (c = 67 ∨ c = 77 ∨ c = 89) := by
  constructor
  · rintro ⟨row, c, hr, hc, hp⟩
    exact ⟨c, List.mem_flatten.mpr ⟨row, hr, hc⟩, hp⟩
  · rintro ⟨c, hc, hp⟩
    rcases List.mem_flatten.mp hc with ⟨row, hr, hcr⟩
    exact ⟨row, c, hr, hcr, hp⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib
