import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_orbit_optimality

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_WalkBridge

theorem sum_nat_range_head (first count : Nat) (f : Nat→Int) :
    sum_nat_range first (Nat.succ count) f=f first+sum_nat_range (Nat.succ first) count f := rfl

theorem sum_nat_range_app (first left right : Nat) (f : Nat→Int) :
    sum_nat_range first (left+right) f=sum_nat_range first left f+sum_nat_range (first+left) right f :=
  P090_OrbitOptimality.sum_nat_range_app first left right f

theorem sum_nat_range_nonnegative (first count : Nat) (f : Nat→Int) :
    (∀ k, (first≤k ∧ k<first+count) → 0≤f k) → 0≤sum_nat_range first count f := by
  induction count generalizing first with
  | zero => simp [sum_nat_range]
  | succ n ih =>
    intro h
    rw [sum_nat_range]
    exact add_nonneg (h first ⟨le_refl _,by omega⟩) (ih (first+1) (by intro k hk; exact h k ⟨by omega,by omega⟩))

theorem sum_nat_range_nonnegative_pointwise (first count : Nat) (f : Nat→Int) :
    (∀ k, 0≤f k) → 0≤sum_nat_range first count f := sum_nat_range_nonnegative_local first count f

theorem walk_exp_suffix_head_tail (pr pe : List Int) (x i next_e d : Int) :
    (0≤next_e ∧ next_e≤Znth i pe 0) →
    WalkExpSuffix pr pe x i next_e d=
      WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) next_e)+WalkExpSuffix pr pe x i (next_e+1) d := by
  intro h
  unfold WalkExpSuffix
  dsimp only
  have hn : (Znth i pe 0-next_e+1).toNat=Nat.succ (Znth i pe 0-next_e).toNat := by omega
  rw [hn,sum_nat_range]
  have he : Int.ofNat next_e.toNat=next_e := by simpa using Int.toNat_of_nonneg h.1
  have hs : Nat.succ next_e.toNat=(next_e+1).toNat := by omega
  have ht : Znth i pe 0-(next_e+1)+1=Znth i pe 0-next_e := by omega
  rw [he,hs,ht]

theorem walk_exp_suffix_exact_exhaustion (pr pe : List Int) (x i d : Int) :
    WalkExpSuffix pr pe x i (Znth i pe 0+1) d=0 := walk_exp_suffix_exhausted pr pe x i d _ (by omega)

theorem walk_exp_suffix_past_exhaustion (pr pe : List Int) (x i next_e d : Int) :
    Znth i pe 0+1≤next_e → WalkExpSuffix pr pe x i next_e d=0 := by
  intro h
  exact walk_exp_suffix_exhausted pr pe x i d next_e (by omega)

theorem walk_exp_suffix_nonnegative (pr pe : List Int) (x i next_e d : Int) :
    (∀ e : Nat, 0≤WalkSuffix pr pe x (i+1) (d*Z.pow (Znth i pr 0) (Int.ofNat e))) →
    0≤WalkExpSuffix pr pe x i next_e d := by
  intro h
  exact sum_nat_range_nonnegative_pointwise _ _ _ h

theorem prefix_selected_at_zero (pr pe : List Int) (d : Int) : PrefixSelected pr pe 0 d → d=1 := by
  have hgen : ∀ i d, PrefixSelected pr pe i d → i=0 → d=1 := by
    intro i d h
    induction h with
    | prefix_selected_zero => simp
    | prefix_selected_step i d e hs hi he ih => intro hzero; omega
  exact fun h=>hgen 0 d h rfl

theorem prefix_selected_successor_product (pr pe : List Int) (i d : Int) :
    0<i → PrefixSelected pr pe i d →
    ∃ previous exponent, PrefixSelected pr pe (i-1) previous ∧ (0≤i-1 ∧ i-1<Zlength pr) ∧
      (0≤exponent ∧ exponent≤Znth (i-1) pe 0) ∧ d=previous*Z.pow (Znth (i-1) pr 0) exponent := by
  intro hip hs
  cases hs with
  | prefix_selected_zero => omega
  | prefix_selected_step j prev e hs hj he =>
    refine ⟨prev,e,?_⟩
    simpa using (show PrefixSelected pr pe j prev ∧ (0≤j ∧ j<Zlength pr) ∧
      (0≤e ∧ e≤Znth j pe 0) ∧ prev*Z.pow (Znth j pr 0) e=prev*Z.pow (Znth j pr 0) e from ⟨hs,hj,he,rfl⟩)

theorem prefix_selected_positive (pr pe : List Int) (i d : Int) :
    PrefixSelected pr pe i d → (∀ k, (0≤k ∧ k<i) → 0<Znth k pr 0) → 0<d := by
  intro h
  induction h with
  | prefix_selected_zero => intro h; omega
  | prefix_selected_step i d e hs hi he ih =>
    intro hb
    have hdp := ih (by intro k hk; exact hb k ⟨hk.1,by omega⟩)
    have hp := hb i ⟨hi.1,by omega⟩
    exact mul_pos hdp (coq_pow_pos _ _ hp he.1)

theorem prefix_selected_index_bounds (pr pe : List Int) (i d : Int) :
    PrefixSelected pr pe i d → (0≤i ∧ i≤Zlength pr) := by
  intro h
  induction h with
  | prefix_selected_zero => exact ⟨le_refl _,Zlength_nonneg _⟩
  | prefix_selected_step i d e hs hi he ih => omega

theorem prefix_selected_positive_from_valid_table (m : Int) (pr pe : List Int) (i d : Int) :
    ValidFactorTable m pr pe → PrefixSelected pr pe i d → 0<d := by
  intro ht hs
  have hi := prefix_selected_index_bounds pr pe i d hs
  apply prefix_selected_positive pr pe i d hs
  intro k hk
  have he := ht.2.2.2.1 k ⟨hk.1,by omega⟩
  have hp := he.1.1
  omega

theorem prefix_selected_step_product (pr pe : List Int) (i d exponent : Int) :
    PrefixSelected pr pe i d → (0≤i ∧ i<Zlength pr) → (0≤exponent ∧ exponent≤Znth i pe 0) →
    PrefixSelected pr pe (i+1) (d*Z.pow (Znth i pr 0) exponent) := prefix_selected_extend pr pe i d exponent

theorem prime_power_transition_build (x d phi ord p e pk ph o g next_d next_phi next_ord : Int) :
    0<d → 1<p → 1≤e → pk=Z.pow p e → ph=EulerPhi pk → o=Ord (x mod pk) pk → g=Z.gcd ord o →
    next_d=d*pk → next_phi=phi*ph → next_ord=ord /ᶻ g * o → Z.gcd d pk=1 →
    EulerPhi next_d=EulerPhi d*EulerPhi pk → Ord x next_d=next_ord → 0<next_d → 0<next_phi → 0<next_ord →
    PrimePowerTransition x d phi ord p e pk ph o g next_d next_phi next_ord := by
  unfold PrimePowerTransition
  tauto

theorem walk_completed_from_exhausted_loop (pr pe : List Int) (x total next_e : Int) :
    WalkLoopState pr pe x 0 1 0 total next_e → Znth 0 pe 0<next_e → WalkCompleted pr pe x total := by
  intro hl he
  unfold WalkLoopState at hl
  rw [walk_exp_suffix_exhausted pr pe x 0 1 next_e he] at hl
  unfold WalkCompleted
  omega

theorem orbit_cover_bounds_imply_spec (m x cycle_count : Int) :
    OrbitCoverUpperBound m x cycle_count → OrbitCoverLowerBound m x cycle_count → Spec m x (cycle_count+1) := by
  rintro ⟨traps,hc,hl⟩ hlow
  refine ⟨cycle_count+1,⟨⟨traps,hc,hl.symm⟩,?_⟩,rfl⟩
  rintro candidate ⟨ts,ht,he⟩
  subst candidate
  exact hlow ts ht

theorem walk_completed_and_orbit_bounds_imply_spec (pr pe : List Int) (m x total : Int) :
    WalkCompleted pr pe x total → OrbitCoverUpperBound m x (WalkSuffix pr pe x 0 1) →
    OrbitCoverLowerBound m x (WalkSuffix pr pe x 0 1) → Spec m x (total+1) := by
  intro he hu hl
  rw [show total=WalkSuffix pr pe x 0 1 from he]
  exact orbit_cover_bounds_imply_spec m x _ hu hl

end P090_WalkBridge
export P090_WalkBridge (sum_nat_range_head sum_nat_range_nonnegative sum_nat_range_nonnegative_pointwise walk_exp_suffix_head_tail walk_exp_suffix_exact_exhaustion walk_exp_suffix_past_exhaustion walk_exp_suffix_nonnegative prefix_selected_at_zero prefix_selected_successor_product prefix_selected_positive prefix_selected_index_bounds prefix_selected_positive_from_valid_table prefix_selected_step_product prime_power_transition_build walk_completed_from_exhausted_loop orbit_cover_bounds_imply_spec walk_completed_and_orbit_bounds_imply_spec)
-- Both Coq modules export the same sum_nat_range_app interface; the root forwarding declaration above is definitionally the same statement.

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
