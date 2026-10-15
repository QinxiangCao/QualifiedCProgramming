import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
namespace SimpleC.EE.LLM_bench.Data_structures.stack.stack_lib
open AUXLib SimpleC.SL.CommonAssertion SimpleC.SL.SeparationLogic
open SimpleC.SL.CommonAssertion.DerivedPredSig
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

def sll := List Int
def sll_empty : sll := []
def sll_cons (x : Int) (contents : sll) : sll := x :: contents
def sll_from_array (concrete : List Int) : sll := concrete.reverse
def stack_capacity : Int := 100000

def stack_representation (contents : sll) (concrete : List Int) (size : Int) : Prop :=
  0 ≤ size ∧ size ≤ stack_capacity ∧ Zlength contents = size ∧
  Zlength concrete = size ∧ concrete = contents.reverse

noncomputable def store_stack (p : Int) (contents : sll) (size : Int) : Assertion :=
  EX concrete : List Int, “ stack_representation contents concrete size ” &&
    naive_C_Rules.IntArray.full p size concrete

def BuildStackPrefix (contents : sll) (input : List Int) (processed : Int) : Prop :=
  contents = sll_from_array (sublist 0 processed input)

def StackConcreteView (contents : sll) (concrete : List Int) (size : Int) : Prop :=
  stack_representation contents concrete size

theorem stack_representation_push__push_state (before : sll) (concrete : List Int)
    (n x : Int) (h : stack_representation before concrete n) (hc : n < stack_capacity) :
    stack_representation (sll_cons x before) (concrete ++ [x]) (n + 1) := by
  rcases h with ⟨hn, hb, hl, hcl, hr⟩
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · simpa [sll_cons, Zlength_cons, hl]
  · simp only [Zlength_app, Zlength_cons, Zlength_nil, hcl]
    omega
  · simpa [sll_cons] using congrArg (· ++ [x]) hr

theorem stack_representation_pop__pop_state (top : Int) (rest : sll)
    (concrete : List Int) (size : Int) (hs : 1 ≤ size)
    (h : stack_representation (sll_cons top rest) concrete size) :
    concrete = rest.reverse ++ [top] ∧ Zlength rest.reverse = size - 1 ∧
    stack_representation rest rest.reverse (size - 1) ∧ Znth (size - 1) concrete 0 = top := by
  rcases h with ⟨hn, hb, hl, hcl, hr⟩
  have hrest : Zlength rest = size - 1 := by
    simp only [sll_cons, Zlength_cons] at hl
    omega
  have hrev : Zlength rest.reverse = size - 1 := by simpa [Zlength] using hrest
  have heq : concrete = rest.reverse ++ [top] := by simpa [sll_cons] using hr
  refine ⟨heq, hrev, ⟨by omega, by omega, hrest, hrev, rfl⟩, ?_⟩
  rw [heq, app_Znth2 0 rest.reverse [top] (size - 1) (by omega), hrev]
  simp [Znth]

theorem stack_representation_prefix__build_loop (input : List Int) (k : Int)
    (hr : 0 ≤ k ∧ k ≤ Zlength input) (hc : k ≤ stack_capacity) :
    stack_representation (sll_from_array (sublist 0 k input)) (sublist 0 k input) k := by
  have hl : Zlength (sublist 0 k input) = k := by
    have h := sublist_length 0 k input ⟨by omega, hr.1⟩ hr.2
    simp only [Zlength, h, Int.sub_zero, Int.ofNat_eq_coe]
    omega
  exact ⟨hr.1, hc, by simpa [sll_from_array, Zlength] using hl, hl,
    by simp [sll_from_array]⟩

theorem build_stack_prefix_succ__build_loop (pfx : sll) (input : List Int) (i x : Int)
    (hr : 0 ≤ i ∧ i < Zlength input) (hp : BuildStackPrefix pfx input i)
    (hx : x = Znth i input 0) : BuildStackPrefix (sll_cons x pfx) input (i + 1) := by
  unfold BuildStackPrefix sll_cons sll_from_array at *
  rw [hp, hx, sublist_split 0 (i + 1) i input (by omega) (by omega),
    sublist_single 0 i input hr, List.reverse_append]
  rfl

theorem build_stack_prefix_complete__build_completion (pfx : sll) (input : List Int)
    (processed size : Int) (hge : processed ≥ size) (hle : processed ≤ size)
    (hl : Zlength input = size) (hp : BuildStackPrefix pfx input processed) :
    processed = size ∧ pfx = sll_from_array input := by
  have heq : processed = size := by omega
  refine ⟨heq, ?_⟩
  unfold BuildStackPrefix at hp
  rw [sublist_self input processed (by omega)] at hp
  exact hp

end SimpleC.EE.LLM_bench.Data_structures.stack.stack_lib
namespace SimpleC.EE.LLM_bench.Data_structures.stack
export stack_lib (sll sll_empty sll_cons sll_from_array stack_capacity stack_representation
  store_stack BuildStackPrefix StackConcreteView)
end SimpleC.EE.LLM_bench.Data_structures.stack
