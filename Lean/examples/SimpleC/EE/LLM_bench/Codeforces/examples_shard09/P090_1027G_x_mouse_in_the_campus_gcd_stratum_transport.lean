import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_exponent_consumer
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_unit_orbit_partition
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_GcdStratumTransport

theorem divisor_quotient_factorization (m d : Int) :
    0 < d → d ∣ᶻ m → m = (m /ᶻ d)*d := by
  intro hd hdiv
  have h := coq_div_factor m d (Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).mp hdiv))
  nlinarith

theorem positive_divisor_quotient_positive (m d : Int) :
    0 < m → 0 < d → d ∣ᶻ m → 0 < m /ᶻ d := by
  intro hm hd hdiv
  have hf := divisor_quotient_factorization m d hd hdiv
  nlinarith

theorem coprime_mod_positive_divisor (m d x : Int) :
    0 < d → d ∣ᶻ m → Z.gcd x m = 1 → Z.gcd (x mod d) d = 1 := by
  intro hd hdiv hg
  rw [coq_gcd_mod]
  exact gcd_with_divisor_of_coprime_modulus x d m hg hdiv

private theorem gcd_scale (q a b : Int) (hq : 0 ≤ q) : Z.gcd (q*a) (q*b) = q*Z.gcd a b := by
  simp only [Z.gcd,Int.gcd_mul_left,Int.ofNat_eq_coe,Nat.cast_mul,Int.natCast_natAbs,abs_of_nonneg hq]

theorem stratum_lift_range_and_gcd (m d unit : Int) :
    0 < m → 0 < d → d ∣ᶻ m → (0 ≤ unit ∧ unit < d) → Z.gcd unit d = 1 →
    (0 ≤ StratumLift m d unit ∧ StratumLift m d unit < m) ∧ Z.gcd (StratumLift m d unit) m = m /ᶻ d := by
  intro hm hd hdiv hu hg
  have hq := positive_divisor_quotient_positive m d hm hd hdiv
  have hf := divisor_quotient_factorization m d hd hdiv
  refine ⟨⟨by unfold StratumLift; nlinarith,by unfold StratumLift; nlinarith⟩,?_⟩
  change Z.gcd ((m /ᶻ d)*unit) m = m /ᶻ d
  conv_lhs => arg 2; rw [hf]
  rw [gcd_scale _ _ _ (by omega),hg,mul_one]

theorem stratum_extract_unit (m d room : Int) :
    0 < m → 0 < d → d ∣ᶻ m → (0 ≤ room ∧ room < m) → Z.gcd room m = m /ᶻ d →
    room = StratumLift m d (StratumProject m d room) ∧
    (0 ≤ StratumProject m d room ∧ StratumProject m d room < d) ∧ Z.gcd (StratumProject m d room) d = 1 := by
  intro hm hd hdiv hr hg
  have hq := positive_divisor_quotient_positive m d hm hd hdiv
  have hf := divisor_quotient_factorization m d hd hdiv
  have hqd : (m /ᶻ d) ∣ room := by rw [← hg]; exact Int.gcd_dvd_left room m
  have hroom := coq_div_factor room (m /ᶻ d) (Int.fmod_eq_zero_of_dvd hqd)
  have hproj : 0 ≤ StratumProject m d room ∧ StratumProject m d room < d := by
    unfold StratumProject
    constructor <;> nlinarith
  have hunit : Z.gcd (StratumProject m d room) d = 1 := by
    conv_lhs at hg => arg 1; rw [hroom]
    conv_lhs at hg => arg 2; rw [hf]
    rw [gcd_scale _ _ _ (by omega)] at hg
    unfold StratumProject
    nlinarith
  exact ⟨hroom,hproj,hunit⟩

theorem stratum_project_lift (m d unit : Int) :
    0 < m → 0 < d → d ∣ᶻ m → StratumProject m d (StratumLift m d unit) = unit := by
  intro hm hd hdiv
  have hq := positive_divisor_quotient_positive m d hm hd hdiv
  exact Int.mul_fdiv_cancel_left unit (by omega)

theorem stratum_lift_injective (m d left right : Int) :
    0 < m → 0 < d → d ∣ᶻ m → StratumLift m d left = StratumLift m d right → left = right := by
  intro hm hd hdiv he
  have hq := positive_divisor_quotient_positive m d hm hd hdiv
  unfold StratumLift at he
  nlinarith

theorem stratum_lift_mul_mod (m d unit x time : Int) :
    0 < m → 0 < d → d ∣ᶻ m → 0 ≤ time →
    (StratumLift m d unit*Z.pow x time) mod m =
      StratumLift m d ((unit*Z.pow (x mod d) time) mod d) := by
  intro hm hd hdiv ht
  have hq := positive_divisor_quotient_positive m d hm hd hdiv
  have hf := divisor_quotient_factorization m d hd hdiv
  unfold StratumLift
  conv_lhs => arg 2; rw [hf]
  rw [mul_assoc]
  change ((m /ᶻ d)*(unit*Z.pow x time)).fmod ((m /ᶻ d)*d) = _
  rw [Int.mul_fmod_mul_of_pos _ _ hq]
  congr 1
  change (unit*Z.pow x time).fmod d = (unit*Z.pow (x mod d) time).fmod d
  conv_lhs => rw [Int.mul_fmod]
  conv_rhs => rw [Int.mul_fmod]
  have hp := OE.pow_mod_base x d time (by omega) ht
  change (unit.fmod d*(Z.pow x time).fmod d).fmod d = (unit.fmod d*(Z.pow (x mod d) time).fmod d).fmod d
  exact congrArg (fun r => (unit.fmod d*r).fmod d) hp.symm

theorem stratum_lift_orbit_hit (m d x unit representative : Int) :
    0 < m → 0 < d → d ∣ᶻ m → OQ.OrbitHit d (x mod d) unit representative →
    OQ.OrbitHit m x (StratumLift m d unit) (StratumLift m d representative) := by
  rintro hm hd hdiv ⟨t,ht,hr⟩
  refine ⟨t,ht,?_⟩
  rw [stratum_lift_mul_mod m d unit x t hm hd hdiv ht,hr]

theorem stratum_lift_orbit_hit_inverse (m d x unit room : Int) :
    0 < m → 0 < d → d ∣ᶻ m → OQ.OrbitHit m x (StratumLift m d unit) room →
    ∃ quotient_room, room = StratumLift m d quotient_room ∧ OQ.OrbitHit d (x mod d) unit quotient_room := by
  rintro hm hd hdiv ⟨t,ht,hr⟩
  exact ⟨(unit*Z.pow (x mod d) t) mod d,by rw [hr,stratum_lift_mul_mod m d unit x t hm hd hdiv ht],t,ht,rfl⟩

theorem coprime_stratum_orbit_compatibility (m d x unit representative : Int) :
    0 < m → 0 < d → d ∣ᶻ m → Z.gcd x m = 1 → OQ.OrbitHit d (x mod d) unit representative →
    OQ.OrbitHit m x (StratumLift m d unit) (StratumLift m d representative) := by
  intro hm hd hdiv hg hh
  exact stratum_lift_orbit_hit m d x unit representative hm hd hdiv hh

theorem lifted_representatives_length (m d : Int) (representatives : List Int) :
    (LiftedRepresentatives m d representatives).length = representatives.length := List.length_map _

theorem lifted_representatives_zlength (m d : Int) (representatives : List Int) :
    Zlength (LiftedRepresentatives m d representatives) = Zlength representatives := by simp [Zlength,LiftedRepresentatives]

theorem transport_unit_stratum_system (m d x : Int) (unit_representatives : List Int) :
    0 < m → 1 < d → d ∣ᶻ m → Z.gcd x m = 1 →
    OQ.StratumRepresentativeSystem d (x mod d) 1 unit_representatives →
    OQ.StratumRepresentativeSystem m x (m /ᶻ d) (LiftedRepresentatives m d unit_representatives) ∧
    Zlength (LiftedRepresentatives m d unit_representatives) = Zlength unit_representatives := by
  rintro hm hd hdiv hg ⟨hn,hf,hcover,hsep⟩
  refine ⟨⟨?_,?_,?_,?_⟩,lifted_representatives_zlength m d unit_representatives⟩
  · exact P090_OrbitQuotient.nodup_map_on _ _ hn
      (fun l r _ _ => stratum_lift_injective m d l r hm (by omega) hdiv)
  · apply Forall.iff_forall_mem.mpr
    intro room hmem
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hmem
    have hh := (Forall.iff_forall_mem.mp hf) u hu
    exact stratum_lift_range_and_gcd m d u hm (by omega) hdiv hh.1 hh.2
  · intro start hs hgs
    obtain ⟨hsl,hur,hu⟩ := stratum_extract_unit m d start hm (by omega) hdiv hs hgs
    obtain ⟨r,hr,hhit⟩ := hcover (StratumProject m d start) hur hu
    refine ⟨StratumLift m d r,List.mem_map.mpr ⟨r,hr,rfl⟩,?_⟩
    rw [hsl]
    exact stratum_lift_orbit_hit m d x (StratumProject m d start) r hm (by omega) hdiv hhit
  · intro left right room hl hr hleft hright
    obtain ⟨lu,hlu,rfl⟩ := List.mem_map.mp hl
    obtain ⟨ru,hru,rfl⟩ := List.mem_map.mp hr
    obtain ⟨lr,hlr,hlhit⟩ := stratum_lift_orbit_hit_inverse m d x lu room hm (by omega) hdiv hleft
    obtain ⟨rr,hrr,hrhit⟩ := stratum_lift_orbit_hit_inverse m d x ru room hm (by omega) hdiv hright
    have heq := stratum_lift_injective m d lr rr hm (by omega) hdiv (hlr.symm.trans hrr)
    subst rr
    have hh := hsep lu ru lr hlu hru hlhit hrhit
    rw [hh]

theorem divisor_one_lift_zero (m : Int) : StratumLift m 1 0 = 0 := by simp [StratumLift]

theorem divisor_one_zero_stratum_transport (m x : Int) :
    0 < m → OQ.StratumRepresentativeSystem m x (m /ᶻ 1) (LiftedRepresentatives m 1 [0]) ∧
    Zlength (LiftedRepresentatives m 1 [0]) = 1 := by
  intro hm
  simpa [LiftedRepresentatives,StratumLift,Z.div,Zlength] using
    (show OQ.StratumRepresentativeSystem m x m [0] ∧ Zlength ([0] : List Int) = 1 from
      ⟨P090_OrbitQuotient.zero_singleton_stratum_system m x hm,rfl⟩)
end P090_GcdStratumTransport
export P090_GcdStratumTransport (divisor_quotient_factorization positive_divisor_quotient_positive coprime_mod_positive_divisor
  stratum_lift_range_and_gcd stratum_extract_unit stratum_project_lift stratum_lift_injective stratum_lift_mul_mod
  stratum_lift_orbit_hit stratum_lift_orbit_hit_inverse coprime_stratum_orbit_compatibility lifted_representatives_length
  lifted_representatives_zlength transport_unit_stratum_system divisor_one_lift_zero divisor_one_zero_stratum_transport)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
