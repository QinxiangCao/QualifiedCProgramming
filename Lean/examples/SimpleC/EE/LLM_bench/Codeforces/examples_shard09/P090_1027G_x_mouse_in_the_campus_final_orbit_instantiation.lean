import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_divisor_strata_keys
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_FinalOrbitInstantiation

theorem coprime_with_positive_divisor (m x divisor : Int) :
    Z.gcd x m = 1 → divisor ∣ᶻ m → Z.gcd x divisor = 1 := gcd_with_divisor_of_coprime_modulus x divisor m

theorem concrete_zero_block_exact (m x : Int) : 0 < m → ExactZeroStratumSystem m x (ConcreteZeroBlock m) := by
  intro hm
  simpa [ExactZeroStratumSystem,ConcreteZeroBlock,Z.div] using divisor_one_zero_stratum_transport m x hm

theorem concrete_nonunit_block_exact (m x divisor : Int) :
    0 < m → Z.gcd x m = 1 → divisor ∈ concrete_nonunit_divisors m →
    1 < divisor ∧ divisor ∣ᶻ m ∧ P090_OrbitQuotient.StratumRepresentativeSystem m x (m /ᶻ divisor) (ConcreteNonUnitBlock m x divisor) ∧
    Zlength (ConcreteNonUnitBlock m x divisor) = CycleTerm x divisor := by
  intro hm hx hin
  obtain ⟨hd,hdle,hdiv⟩ := (concrete_nonunit_divisor_spec m divisor hm).mp hin
  have hxd := coprime_with_positive_divisor m x divisor hx hdiv
  obtain ⟨hs,hl,hp⟩ := reduced_unit_representatives_exact x divisor (by omega) hxd
  obtain ⟨ht,hlt⟩ := transport_unit_stratum_system m divisor x (UnitRepresentatives divisor (x mod divisor)) hm hd hdiv hx hs
  refine ⟨hd,hdiv,ht,?_⟩
  unfold ConcreteNonUnitBlock
  rw [hlt,hl]
  have hne : divisor ≠ 1 := by omega
  simp [CycleTerm,hne]

theorem concrete_nonunit_subsystems (m x : Int) (divisors : List Int) :
    0 < m → Z.gcd x m = 1 → (∀ divisor, divisor ∈ divisors → divisor ∈ concrete_nonunit_divisors m) →
    ExactNonUnitDivisorSystems m x divisors (divisors.map (ConcreteNonUnitBlock m x)) := by
  intro hm hx hsub
  induction divisors with
  | nil => exact .nil
  | cons d ds ih =>
    exact .cons (concrete_nonunit_block_exact m x d hm hx (hsub d List.mem_cons_self))
      (ih (fun q hq => hsub q (List.mem_cons_of_mem _ hq)))

theorem concrete_exact_nonunit_divisor_systems (m x : Int) :
    0 < m → Z.gcd x m = 1 → ExactNonUnitDivisorSystems m x (concrete_nonunit_divisors m) (ConcreteNonUnitBlocks m x) := by
  intro hm hx
  exact concrete_nonunit_subsystems m x _ hm hx (fun _ h => h)

theorem concrete_room_zero_cycle_spec (m x : Int) :
    2 ≤ m → Z.gcd x m = 1 → Spec m x (RoomZeroCycleTotal m x) := by
  intro hm hx
  obtain ⟨hk,hc⟩ := concrete_divisor_strata_key_premises m (by omega)
  exact concrete_divisor_strata_imply_spec m x (ConcreteZeroBlock m) (ConcreteNonUnitBlocks m x)
    (by omega) hx (concrete_zero_block_exact m x (by omega)) (concrete_exact_nonunit_divisor_systems m x (by omega) hx) hk hc

theorem valid_factor_table_walk_spec (m x : Int) (pr pe : List Int) :
    2 ≤ m → Z.gcd x m = 1 → ValidFactorTable m pr pe → Spec m x (1+WalkSuffix pr pe x 0 1) := by
  intro hm hx hv
  rw [room_zero_final_decomposition m x pr pe hv]
  exact concrete_room_zero_cycle_spec m x hm hx

theorem valid_factor_table_walk_spec_solver_order (m x : Int) (pr pe : List Int) :
    2 ≤ m → Z.gcd x m = 1 → ValidFactorTable m pr pe → Spec m x (WalkSuffix pr pe x 0 1+1) := by
  intro hm hx hv
  simpa only [add_comm] using valid_factor_table_walk_spec m x pr pe hm hx hv

theorem walk_global_bounds_factor_table_spec (m x : Int) (pr pe : List Int) :
    WalkGlobalBounds m x → ValidFactorTable m pr pe → Spec m x (WalkSuffix pr pe x 0 1+1) := by
  intro hg hv
  exact valid_factor_table_walk_spec_solver_order m x pr pe hg.1.1 hg.2.2 hv
end P090_FinalOrbitInstantiation
export P090_FinalOrbitInstantiation (coprime_with_positive_divisor concrete_zero_block_exact concrete_nonunit_block_exact
  concrete_nonunit_subsystems concrete_exact_nonunit_divisor_systems concrete_room_zero_cycle_spec
  valid_factor_table_walk_spec valid_factor_table_walk_spec_solver_order walk_global_bounds_factor_table_spec)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
