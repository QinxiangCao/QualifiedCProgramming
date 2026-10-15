import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_walk_bridge

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_OrderInputBridge

theorem ord_search_exact_from_terminal (x modulus phi : Int) :
    1<modulus → phi=EulerPhi modulus → 0<phi → Z.pow x phi mod modulus=1 →
    (1 ≤ Ord x modulus ∧ Ord x modulus ≤ phi) ∧
    Z.pow x (Ord x modulus) mod modulus = 1 ∧
    (∀ candidate, (1 ≤ candidate ∧ candidate < Ord x modulus) → Z.pow x candidate mod modulus ≠ 1) := by
  intro hm hphi hpb hpp
  have hcount : 0 < phi.toNat := by omega
  obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : phi.toNat ≠ 0)
  have hf : 1 + Int.ofNat fuel = phi := by
    simp only [Int.ofNat_eq_coe]
    omega
  have ht : Z.pow (x mod modulus) (1 + Int.ofNat fuel) mod modulus = 1 := by
    rw [hf, order_ex_pow_mod_base x modulus phi (by omega) (by omega)]
    exact hpp
  have hs := order_ex_search_terminal_spec (x mod modulus) modulus 1 fuel (by omega) ht
  have ho : Ord x modulus = order_search (x mod modulus) modulus 1 (Nat.succ fuel) := by
    unfold Ord
    dsimp only
    have hm1 : (modulus == 1) = false := by simp; omega
    rw [hm1]
    simp only [Bool.false_eq_true, if_false]
    rw [← hphi, hfuel]
  rw [ho]
  refine ⟨⟨hs.1.1, ?_⟩, ?_, ?_⟩
  · rw [← hf]; exact hs.1.2
  · rw [← order_ex_pow_mod_base x modulus _ (by omega) (by omega)]
    exact hs.2
  · intro c hc hcproof
    apply order_ex_search_minimal (x mod modulus) modulus 1 (Nat.succ fuel) c (by omega) hc
    rw [order_ex_pow_mod_base x modulus c (by omega) (by omega)]
    exact hcproof


theorem reduced_base_coprime (x modulus : Int) :
    modulus≠0 → Z.gcd x modulus=1 → Z.gcd (x mod modulus) modulus=1 := by
  intro hm hg
  rw [coq_gcd_mod,hg]

theorem reduced_base_positive (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → (0<x mod modulus ∧ x mod modulus<modulus) := by
  intro hm hg
  have hn : 0≤x mod modulus := Int.fmod_nonneg_of_pos x (by omega)
  have hl : x mod modulus<modulus := Int.fmod_lt_of_pos x (by omega)
  have hzero : x mod modulus≠0 := by
    intro he
    have hgm := reduced_base_coprime x modulus (by omega) hg
    rw [he] at hgm
    have hgm' : Z.gcd 0 modulus=modulus := by
      simp [Z.gcd,Int.natAbs_of_nonneg (show 0≤modulus by omega)]
    rw [hgm'] at hgm
    omega
  exact ⟨by omega,hl⟩

theorem euler_power_for_case_phi (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → Z.pow x (EulerPhi modulus) mod modulus=1 := by
  intro hm hg
  have hr := reduced_base_positive x modulus hm hg
  have hrg := reduced_base_coprime x modulus (by omega) hg
  have h := ETI.euler_power_totient_mod__inverse_final_result (x mod modulus) modulus hr.1 hr.2 (by omega) hrg
  rw [← euler_phi_bridge,order_ex_pow_mod_base x modulus _ (by omega) (euler_phi_nonnegative modulus)] at h
  exact h

theorem coprime_implies_order_input (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → OrderInput x modulus (EulerPhi modulus) := by
  intro hm hg
  have hb := euler_phi_positive_bounded modulus (by omega)
  have he := euler_power_for_case_phi x modulus hm hg
  obtain ⟨hob,hop,hmin⟩ := ord_search_exact_from_terminal x modulus (EulerPhi modulus) hm rfl (by omega) he
  have hd := order_ex_minimal_success_divides x modulus (Ord x modulus) (EulerPhi modulus) hm (by omega) hop hmin (by omega) he
  exact ⟨hm,rfl,hg,⟨by omega,hb.2⟩,by omega,hd,he⟩

theorem ord_reduced_base (x modulus : Int) : modulus≠0 → Ord (x mod modulus) modulus=Ord x modulus := by
  intro hm
  unfold Ord
  have h : (x mod modulus) mod modulus=x mod modulus := Int.fmod_fmod _ _
  rw [h]

theorem coprime_implies_reduced_order_input (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → OrderInput (x mod modulus) modulus (EulerPhi modulus) := by
  intro hm hg
  exact coprime_implies_order_input _ modulus hm (reduced_base_coprime x modulus (by omega) hg)

theorem coprime_implies_exact_order_criterion (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → ExactOrderCriterion x modulus (Ord x modulus) := by
  intro hm hg
  have hi := coprime_implies_order_input x modulus hm hg
  exact ⟨hi.2.2.2.2.1,order_input_power_law x modulus (EulerPhi modulus) hi⟩

theorem coprime_implies_reduced_exact_order_criterion (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → ExactOrderCriterion (x mod modulus) modulus (Ord (x mod modulus) modulus) := by
  intro hm hg
  exact coprime_implies_exact_order_criterion _ modulus hm (reduced_base_coprime x modulus (by omega) hg)

theorem exact_order_criterion_unique (x modulus first second : Int) :
    ExactOrderCriterion x modulus first → ExactOrderCriterion x modulus second → first=second := by
  rintro ⟨hfp,hf⟩ ⟨hsp,hs⟩
  have hd1 : first ∣ᶻ second := (hf second (by omega)).mp ((hs second (by omega)).mpr ⟨1,by ring⟩)
  have hd2 : second ∣ᶻ first := (hs first (by omega)).mp ((hf first (by omega)).mpr ⟨1,by ring⟩)
  have hle1 := Int.le_of_dvd hsp ((Z.divide_iff_dvd _ _).mp hd1)
  have hle2 := Int.le_of_dvd hfp ((Z.divide_iff_dvd _ _).mp hd2)
  omega

theorem exact_order_criterion_is_ord (x modulus candidate : Int) :
    1<modulus → Z.gcd x modulus=1 → ExactOrderCriterion x modulus candidate → candidate=Ord x modulus := by
  intro hm hg hc
  exact exact_order_criterion_unique x modulus candidate (Ord x modulus) hc (coprime_implies_exact_order_criterion x modulus hm hg)

theorem coprime_implies_order_result (x modulus : Int) :
    1<modulus → Z.gcd x modulus=1 → OrderResult x modulus (Ord x modulus) := by
  intro hm hg
  have hi := coprime_implies_order_input x modulus hm hg
  have he := order_ex_ord_search_exact x modulus (EulerPhi modulus) hi
  exact ⟨rfl,hi.2.2.2.2.1,hi.2.2.2.2.2.1,he.2.1⟩

end P090_OrderInputBridge
export P090_OrderInputBridge (ord_search_exact_from_terminal reduced_base_coprime reduced_base_positive euler_power_for_case_phi coprime_implies_order_input ord_reduced_base coprime_implies_reduced_order_input coprime_implies_exact_order_criterion coprime_implies_reduced_exact_order_criterion exact_order_criterion_unique exact_order_criterion_is_ord coprime_implies_order_result)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
