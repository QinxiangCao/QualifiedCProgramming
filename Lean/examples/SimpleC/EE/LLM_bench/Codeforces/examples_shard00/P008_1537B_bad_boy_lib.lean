import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib
open AUXLib

def zpair_fst (p : Int × Int) : Int := p.1

def zpair_snd (p : Int × Int) : Int := p.2

def Manhattan (p q : Int × Int) : Int := Z.abs (p.1 - q.1) + Z.abs (p.2 - q.2)

def RoundTripThroughTwo (start p q : Int × Int) : Int :=
  Manhattan start p + Manhattan p q + Manhattan q start

def InRoom (n m : Int) (p : Int × Int) : Prop :=
  (1 ≤ p.1 ∧ p.1 ≤ n) ∧ (1 ≤ p.2 ∧ p.2 ≤ m)

def Pre (n m : Int) (start : Int × Int) : Prop :=
  (1 ≤ n ∧ n ≤ 1000000000) ∧ (1 ≤ m ∧ m ≤ 1000000000) ∧ InRoom n m start

def Spec (n m : Int) (start p q : Int × Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun candidate : (Int × Int) × (Int × Int) => InRoom n m candidate.1 ∧ InRoom n m candidate.2)
    (fun candidate => RoundTripThroughTwo start candidate.1 candidate.2)
    (RoundTripThroughTwo start p q) ∧ InRoom n m p ∧ InRoom n m q

private theorem abs_cases (x : Int) : Z.abs x = x ∨ Z.abs x = -x := by
  by_cases hx : 0 ≤ x
  · exact Or.inl ((Z.abs_eq_iff x).2 hx)
  · exact Or.inr (Int.ofNat_natAbs_of_nonpos (by omega))

theorem cycle_span_bound__final_result (lo hi s p q : Int)
    (hs : lo ≤ s ∧ s ≤ hi) (hp : lo ≤ p ∧ p ≤ hi) (hq : lo ≤ q ∧ q ≤ hi) :
    Z.abs (s - p) + Z.abs (p - q) + Z.abs (q - s) ≤ 2 * (hi - lo) := by
  rcases abs_cases (s - p) with hsp | hsp <;>
    rcases abs_cases (p - q) with hpq | hpq <;>
      rcases abs_cases (q - s) with hqs | hqs <;> omega

theorem opposite_corners_spec__final_result (n m : Int) (start : Int × Int)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hs : InRoom n m start) :
    Spec n m start (1, 1) (n, m) := by
  have hp : InRoom n m (1, 1) := ⟨⟨by omega, hn⟩, ⟨by omega, hm⟩⟩
  have hq : InRoom n m (n, m) := ⟨⟨hn, by omega⟩, ⟨hm, by omega⟩⟩
  refine ⟨⟨((1, 1), (n, m)), ⟨⟨hp, hq⟩, ?_⟩, rfl⟩, hp, hq⟩
  intro candidate hc
  have hx := cycle_span_bound__final_result 1 n start.1 candidate.1.1 candidate.2.1
    hs.1 hc.1.1 hc.2.1
  have hy := cycle_span_bound__final_result 1 m start.2 candidate.1.2 candidate.2.2
    hs.2 hc.1.2 hc.2.2
  have hxs := (Z.abs_eq_iff (start.1 - 1)).2 (by have := hs.1; omega)
  have hys := (Z.abs_eq_iff (start.2 - 1)).2 (by have := hs.2; omega)
  have hnx : Z.abs (1 - n) = -(1 - n) := Int.ofNat_natAbs_of_nonpos (by omega)
  have hmy : Z.abs (1 - m) = -(1 - m) := Int.ofNat_natAbs_of_nonpos (by omega)
  have hxn := (Z.abs_eq_iff (n - start.1)).2 (by have := hs.1; omega)
  have hym := (Z.abs_eq_iff (m - start.2)).2 (by have := hs.2; omega)
  dsimp [RoundTripThroughTwo, Manhattan]
  omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P008_1537B_bad_boy_lib
