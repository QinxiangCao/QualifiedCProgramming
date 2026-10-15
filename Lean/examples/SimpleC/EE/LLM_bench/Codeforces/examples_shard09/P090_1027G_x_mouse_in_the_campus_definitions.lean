import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

/-! Mathematical definitions from the corresponding Coq library. Its theorem proofs are migrated separately. -/
set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 4000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime
open MaxMinLib

-- Coq integer operations retain their behavior for negative operands and exponents.
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infixr:80 " ^ᶻ " => Z.pow
local infix:50 " ∣ᶻ " => Z.divide

private def coq_existsb {A : Type} (f : A → Bool) (xs : List A) : Bool := xs.any f

def CatchesAll (m x : Int) (traps : List Int) : Prop :=
  NoDup traps ∧ Forall (fun r => (0 ≤ r ∧ r < m)) traps ∧
  ∀ start, (0 ≤ start ∧ start < m) → ∃ t room, t ≥ 0 ∧ room = start * Z.pow x t mod m ∧ (room ∈ traps)

def Pre (m x : Int) : Prop :=
  
  Z.gcd x m = 1

def Spec (m x out : Int) : Prop :=
  min_value_of_subset (fun (a b : Int) => a ≤ b) (fun v => ∃ traps, CatchesAll m x traps ∧ v = Zlength traps) (fun x => x) out

def coprime_count (n : Int) (fuel : Nat) : Int :=
  match fuel with
  | 0 => 0
  | Nat.succ k =>
      coprime_count n k +
      if (· == ·) (Z.gcd (Int.ofNat (Nat.succ k)) n) 1 then 1 else 0

def EulerPhi (n : Int) : Int := coprime_count n (Int.toNat n)

def order_search (x n k : Int) (fuel : Nat) : Int :=
  match fuel with
  | 0 => 1
  | Nat.succ fuel' =>
      if (· == ·) (Z.pow x k mod n) 1
      then k
      else order_search x n (k + 1) fuel'

def Ord (x n : Int) : Int :=
  if (· == ·) n 1 then 1
  else order_search (x mod n) n 1 (Int.toNat (EulerPhi n))

def IsPrime (p : Int) : Prop :=
  1 < p ∧
  ∀ q, (1 < q ∧ q < p) → p mod q ≠ 0

def CycleTerm (x d : Int) : Int :=
  if (· == ·) d 1 then 0 else EulerPhi d /ᶻ Ord (x mod d) d

def sum_nat_range (first count : Nat) (f : Nat → Int) : Int :=
  match count with
  | 0 => 0
  | Nat.succ count' => f first + sum_nat_range (Nat.succ first) count' f

def walk_suffix_lists (pr pe : List Int) (x d : Int) : Int :=
  match pr, pe with
  | p :: pr', exponent :: pe' =>
      sum_nat_range 0 (Nat.succ (Int.toNat exponent))
        (fun e => walk_suffix_lists pr' pe' x (d * Z.pow p (Int.ofNat e)))
  | _, _ => CycleTerm x d

def WalkSuffix (pr pe : List Int) (x i d : Int) : Int :=
  walk_suffix_lists (List.drop (Int.toNat i) pr) (List.drop (Int.toNat i) pe) x d

def WalkExpSuffix
    (pr pe : List Int) (x i next_e d : Int) : Int :=
  let exponent := Znth i pe 0;
  sum_nat_range (Int.toNat next_e)
    (Int.toNat (exponent - next_e + 1))
    (fun e =>
       WalkSuffix pr pe x (i + 1)
         (d * Z.pow (Znth i pr 0) (Int.ofNat e)))

def WalkLoopState
    (pr pe : List Int) (x i d before current next_e : Int) : Prop :=
  current + WalkExpSuffix pr pe x i next_e d =
  before + WalkSuffix pr pe x i d

def WalkGlobalBounds (m x : Int) : Prop :=
  (2 ≤ m ∧ m ≤ 100000000000000) ∧
  (1 ≤ x ∧ x < m) ∧
  Z.gcd x m = 1

def WalkMachineBounds (m d phi ord : Int) : Prop :=
  (0 < d ∧ d ≤ m) ∧ (0 < phi ∧ phi ≤ m) ∧ (0 < ord ∧ ord ≤ m)

def WalkBudget (m before work : Int) : Prop :=
  0 ≤ before ∧ 0 ≤ work ∧ before + work ≤ m

def WalkPendingState
    (pr pe : List Int) (m x i d before current next_e : Int) : Prop :=
  WalkLoopState pr pe x i d before current next_e ∧
  WalkBudget m current (WalkExpSuffix pr pe x i next_e d)

def WalkExponentState
    (m p exponent max_exponent pk ph : Int) : Prop :=
  (2 ≤ p ∧ p ≤ m) ∧
  (1 ≤ exponent ∧ exponent ≤ max_exponent + 1) ∧
  (1 ≤ pk ∧ pk ≤ m) ∧ (1 ≤ ph ∧ ph ≤ m) ∧
  pk = Z.pow p (exponent - 1) ∧
  ph = EulerPhi pk

def MulLoopState (a0 b0 modulus a b r : Int) : Prop :=
  (r + a * b) mod modulus = (a0 * b0) mod modulus

def PowLoopState (base exponent modulus b e r : Int) : Prop :=
  (r * Z.pow b e) mod modulus = Z.pow base exponent mod modulus

def GcdLoopState (a0 b0 a b : Int) : Prop :=
  Z.gcd a b = Z.gcd a0 b0

def OrderInput (x modulus phi : Int) : Prop :=
  1 < modulus ∧
  phi = EulerPhi modulus ∧
  Z.gcd x modulus = 1 ∧
  (0 < phi ∧ phi ≤ modulus) ∧
  0 < Ord x modulus ∧
  (Ord x modulus ∣ᶻ phi) ∧
  Z.pow x phi mod modulus = 1

def OrderResult (x modulus result : Int) : Prop :=
  result = Ord x modulus ∧
  0 < result ∧
  (result ∣ᶻ EulerPhi modulus) ∧
  Z.pow x result mod modulus = 1

def OrderTrialState
    (x modulus phi q t ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  0 < t ∧ t ≤ phi ∧ (t ∣ᶻ phi) ∧
  0 < ord ∧ ord ≤ phi ∧ (ord ∣ᶻ phi) ∧
  (Ord x modulus ∣ᶻ ord) ∧
  Z.pow x ord mod modulus = 1 ∧
  ∀ prime, IsPrime prime → prime < q → t mod prime ≠ 0

def OrderFactorState
    (x modulus phi q t ord : Int) : Prop :=
  OrderTrialState x modulus phi q t ord ∧ IsPrime q

def OrderStripState
    (x modulus phi q t ord : Int) : Prop :=
  OrderFactorState x modulus phi q t ord ∧ t mod q ≠ 0

def factor_product (pr pe : List Int) : Int :=
  match pr, pe with
  | p :: pr', e :: pe' => Z.pow p e * factor_product pr' pe'
  | _, _ => 1

def FactorPrefix
    (m candidate remainder : Int) (pr pe : List Int) : Prop :=
  Zlength pr = Zlength pe ∧
  (0 ≤ Zlength pr ∧ Zlength pr ≤ 64) ∧
  2 ≤ candidate ∧
  (0 < remainder ∧ remainder ≤ m) ∧
  m = factor_product pr pe * remainder ∧
  (∀ k, (0 ≤ k ∧ k < Zlength pr) →
     IsPrime (Znth k pr 0) ∧
     1 ≤ Znth k pe 0 ∧
     Znth k pr 0 < candidate) ∧
  (∀ prime, IsPrime prime → prime < candidate →
     remainder mod prime ≠ 0)

def TrialState
    (m candidate remainder : Int) (pr pe : List Int) : Prop :=
  FactorPrefix m candidate remainder pr pe

def FactorAtPrime
    (m candidate original_remainder remainder exponent : Int)
    (pr pe : List Int) : Prop :=
  FactorPrefix m candidate original_remainder pr pe ∧
  IsPrime candidate ∧
  original_remainder mod candidate = 0 ∧
  0 ≤ exponent ∧
  original_remainder = Z.pow candidate exponent * remainder ∧
  (0 < remainder ∧ remainder ≤ original_remainder)

def ValidFactorTable (m : Int) (pr pe : List Int) : Prop :=
  Zlength pr = Zlength pe ∧
  (0 ≤ Zlength pr ∧ Zlength pr ≤ 64) ∧
  m = factor_product pr pe ∧
  (∀ k, (0 ≤ k ∧ k < Zlength pr) →
     IsPrime (Znth k pr 0) ∧ 1 ≤ Znth k pe 0) ∧
  (∀ j k,
     0 ≤ j ∧ j < k ∧ k < Zlength pr →
     Znth j pr 0 < Znth k pr 0)

inductive PrefixSelected (pr pe : List Int) : Int → Int → Prop where
| prefix_selected_zero :
    PrefixSelected pr pe 0 1
| prefix_selected_step : ∀ i d e,
    PrefixSelected pr pe i d →
    (0 ≤ i ∧ i < Zlength pr) →
    (0 ≤ e ∧ e ≤ Znth i pe 0) →
    PrefixSelected pr pe (i + 1)
      (d * Z.pow (Znth i pr 0) e)
export PrefixSelected (prefix_selected_zero prefix_selected_step)

def PrefixChoice
    (pr pe : List Int) (x i d phi ord : Int) : Prop :=
  Zlength pr = Zlength pe ∧
  (0 ≤ i ∧ i ≤ Zlength pr) ∧
  PrefixSelected pr pe i d ∧
  0 < d ∧ 0 < phi ∧ 0 < ord ∧
  phi = EulerPhi d ∧ ord = Ord x d ∧ Z.gcd x d = 1

def PrimePowerTransition
    (x d phi ord p e pk ph o g next_d next_phi next_ord : Int) : Prop :=
  0 < d ∧ 1 < p ∧ 1 ≤ e ∧
  pk = Z.pow p e ∧
  ph = EulerPhi pk ∧
  o = Ord (x mod pk) pk ∧
  g = Z.gcd ord o ∧
  next_d = d * pk ∧
  next_phi = phi * ph ∧
  next_ord = ord /ᶻ g * o ∧
  Z.gcd d pk = 1 ∧
  EulerPhi next_d = EulerPhi d * EulerPhi pk ∧
  Ord x next_d = next_ord ∧
  0 < next_d ∧ 0 < next_phi ∧ 0 < next_ord

def CycleAnswer (m x total : Int) : Prop :=
  (0 ≤ total ∧ total ≤ m) ∧ Spec m x (total + 1)

def DivisorCycleSum (m x total : Int) : Prop :=
  min_value_of_subset (fun (a b : Int) => a ≤ b)
    (fun v => ∃ traps, CatchesAll m x traps ∧ v = Zlength traps)
    (fun z => z) (total + 1)

def OrderCore
    (x modulus phi ord excess : Int) : Prop :=
  OrderInput x modulus phi ∧
  0 < ord ∧ ord ≤ phi ∧ (ord ∣ᶻ phi) ∧
  0 < excess ∧
  ord = Ord x modulus * excess ∧
  Z.pow x ord mod modulus = 1

def PrimeSupport (excess remainder : Int) : Prop :=
  ∀ p, IsPrime p → (p ∣ᶻ excess) → (p ∣ᶻ remainder)

def PrimeSupportExcept (excess active remainder : Int) : Prop :=
  ∀ p, IsPrime p → (p ∣ᶻ excess) → p = active ∨ (p ∣ᶻ remainder)

def NoPrimeBelow (candidate remainder : Int) : Prop :=
  ∀ p, IsPrime p → p < candidate → remainder mod p ≠ 0

def OrderTrialStateEx
    (x modulus phi candidate remainder ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  0 < remainder ∧ remainder ≤ phi ∧ (remainder ∣ᶻ phi) ∧
  NoPrimeBelow candidate remainder ∧
  ∃ excess,
    OrderCore x modulus phi ord excess ∧
    PrimeSupport excess remainder

def OrderFactorStateEx
    (x modulus phi active remainder ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  IsPrime active ∧
  0 < remainder ∧ remainder ≤ phi ∧ (remainder ∣ᶻ phi) ∧
  NoPrimeBelow active remainder ∧
  ∃ excess,
    OrderCore x modulus phi ord excess ∧
    PrimeSupportExcept excess active remainder

def OrderStripStateEx
    (x modulus phi active remainder ord : Int) : Prop :=
  OrderFactorStateEx x modulus phi active remainder ord ∧
  remainder mod active ≠ 0

def OrderFinalStateEx
    (x modulus phi active ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  IsPrime active ∧
  ∃ excess,
    OrderCore x modulus phi ord excess ∧
    (∀ p, IsPrime p → (p ∣ᶻ excess) → p = active)

def OrderPowerLaw (x modulus : Int) : Prop :=
  ∀ k, 0 ≤ k →
    (Z.pow x k mod modulus = 1 ↔ (Ord x modulus ∣ᶻ k))

namespace P090_OrderExcess

namespace P090_OrderExcess

def OrderCore
    (x modulus phi ord excess : Int) : Prop :=
  OrderInput x modulus phi ∧
  0 < ord ∧ ord ≤ phi ∧ (ord ∣ᶻ phi) ∧
  0 < excess ∧
  ord = Ord x modulus * excess ∧
  Z.pow x ord mod modulus = 1

def PrimeSupport (excess remainder : Int) : Prop :=
  ∀ p, IsPrime p → (p ∣ᶻ excess) → (p ∣ᶻ remainder)

def PrimeSupportExcept (excess active remainder : Int) : Prop :=
  ∀ p, IsPrime p → (p ∣ᶻ excess) → p = active ∨ (p ∣ᶻ remainder)

def NoPrimeBelow (candidate remainder : Int) : Prop :=
  ∀ p, IsPrime p → p < candidate → remainder mod p ≠ 0

def OrderTrialStateEx
    (x modulus phi candidate remainder ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  0 < remainder ∧ remainder ≤ phi ∧ (remainder ∣ᶻ phi) ∧
  NoPrimeBelow candidate remainder ∧
  ∃ excess,
    OrderCore x modulus phi ord excess ∧
    PrimeSupport excess remainder

def OrderFactorStateEx
    (x modulus phi active remainder ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  IsPrime active ∧
  0 < remainder ∧ remainder ≤ phi ∧ (remainder ∣ᶻ phi) ∧
  NoPrimeBelow active remainder ∧
  ∃ excess,
    OrderCore x modulus phi ord excess ∧
    PrimeSupportExcept excess active remainder

def OrderStripStateEx
    (x modulus phi active remainder ord : Int) : Prop :=
  OrderFactorStateEx x modulus phi active remainder ord ∧
  remainder mod active ≠ 0

def OrderFinalStateEx
    (x modulus phi active ord : Int) : Prop :=
  OrderInput x modulus phi ∧
  IsPrime active ∧
  ∃ excess,
    OrderCore x modulus phi ord excess ∧
    (∀ p, IsPrime p → (p ∣ᶻ excess) → p = active)

def OrderPowerLaw (x modulus : Int) : Prop :=
  ∀ k, 0 ≤ k →
    (Z.pow x k mod modulus = 1 ↔ (Ord x modulus ∣ᶻ k))

def PrimeFactorExistsLaw : Prop :=
  ∀ n, 1 < n → ∃ p, IsPrime p ∧ (p ∣ᶻ n)

def PrimeDivisorProductLaw : Prop :=
  ∀ p a b, IsPrime p → (p ∣ᶻ a * b) → (p ∣ᶻ a) ∨ (p ∣ᶻ b)

def PrimeDivisorOfPrimeLaw : Prop :=
  ∀ p q, IsPrime p → IsPrime q → (p ∣ᶻ q) → p = q

def SmallestRemainingDivisorPrimeLaw : Prop :=
  ∀ candidate remainder,
    2 ≤ candidate →
    0 < remainder →
    NoPrimeBelow candidate remainder →
    remainder mod candidate = 0 →
    IsPrime candidate

def ResidualRemainderPrimeLaw : Prop :=
  ∀ candidate remainder,
    2 ≤ candidate →
    1 < remainder →
    candidate * candidate > remainder →
    NoPrimeBelow candidate remainder →
    IsPrime remainder

end P090_OrderExcess

end P090_OrderExcess

-- Coq exports P090_OrderExcess; its proof declarations are migrated separately.

namespace P090_OrderFoundations

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess

namespace P090_OrderFoundations

end P090_OrderFoundations

end P090_OrderFoundations

-- Coq exports P090_OrderFoundations; its proof declarations are migrated separately.

namespace P090_OrderExact

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess

namespace P090_OrderExact

end P090_OrderExact

end P090_OrderExact

-- Coq exports P090_OrderExact; its proof declarations are migrated separately.

namespace P090_FactorTable

def StrictPrimePrefix (pr : List Int) : Prop :=
  ∀ j k,
    0 ≤ j ∧ j < k ∧ k < Zlength pr →
    Znth j pr 0 < Znth k pr 0

def StrictFactorPrefix
    (m candidate remainder : Int) (pr pe : List Int) : Prop :=
  FactorPrefix m candidate remainder pr pe ∧ StrictPrimePrefix pr

end P090_FactorTable

export P090_FactorTable (StrictPrimePrefix StrictFactorPrefix)

namespace P090_FactorFoundations

def FactorEntriesAtLeastTwo (pr pe : List Int) : Prop :=
  ∀ k, (0 ≤ k ∧ k < Zlength pr) →
    2 ≤ Znth k pr 0 ∧ 1 ≤ Znth k pe 0

end P090_FactorFoundations

export P090_FactorFoundations (FactorEntriesAtLeastTwo)

namespace P090_WalkFoundations

namespace ETI
-- Coq module alias: euler_theorem_inverse_lib.
export SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib (EulerTotientValue EulerPhi EulerTheoremInverse EulerPhiResidual EulerPrime NoPrimeDivisorBelow EulerPhiProgress EulerPhiFactorCompletion EulerPhiFactorCompletion_divide EulerPhiRemovalProgress EulerPhiRemovalProgress_complete EulerModularPowerProgress euler_prime_from_prime__euler_phi_final_results euler_prime_divisor_exists__euler_phi_final_results euler_residue_bounds__inverse_final_result euler_factor_prime__euler_phi_setup_removal euler_prime_power_relprime_iff__euler_phi_setup_removal euler_prime_power_multiple_count__euler_phi_setup_removal euler_totient_prime_power__euler_phi_setup_removal euler_relprime_product_divide__euler_phi_setup_removal euler_list_prod_nodup__euler_phi_setup_removal euler_residue_mod_member__euler_phi_setup_removal euler_crt_solution_mod_left__euler_phi_setup_removal euler_crt_solution_mod_right__euler_phi_setup_removal euler_crt_residue_pair_injective__euler_phi_setup_removal euler_totient_multiplicative__euler_phi_setup_removal euler_totient_coprime_prime_power__euler_phi_setup_removal euler_phi_removal_start__euler_phi_setup_removal euler_prime_two__euler_phi_factor_completion euler_exact_positive_quotient_bounds__euler_phi_factor_completion euler_progress_advance_nondivisor__euler_phi_factor_completion euler_completed_progress__euler_phi_factor_completion euler_active_frontier_bound__euler_phi_factor_completion euler_prime_to_prime__euler_phi_final_results euler_remaining_prime__euler_phi_final_results euler_filter_all_true__euler_phi_final_results euler_totient_of_prime__euler_phi_final_results euler_progress_terminal_prime__euler_phi_final_results euler_progress_terminal_one__euler_phi_final_results euler_modular_progress_odd_step__modular_power_loop euler_modular_progress_even_step__modular_power_loop bounded_residue_product_int__modular_power_loop euler_modular_progress_zero_finish__modular_power_final euler_coprime_residue_member__inverse_final_result euler_residue_map_member__inverse_final_result euler_residue_map_injective__inverse_final_result euler_residue_map_nodup__inverse_final_result euler_residue_map_permutation__inverse_final_result euler_product_permutation__inverse_final_result euler_mapped_product_mod__inverse_final_result euler_residue_product_coprime__inverse_final_result euler_power_totient_mod__inverse_final_result euler_totient_inverse_theorem__inverse_final_result)
end ETI

def ExactOrderCriterion (x modulus candidate : Int) : Prop :=
  0 < candidate ∧
  ∀ exponent,
    0 ≤ exponent →
    ((x ^ᶻ exponent) mod modulus = 1 ↔ (candidate ∣ᶻ exponent))

end P090_WalkFoundations

export P090_WalkFoundations (ExactOrderCriterion)

namespace P090_OrbitOptimality

end P090_OrbitOptimality

-- Coq exports P090_OrbitOptimality; its proof declarations are migrated separately.

namespace P090_WalkBridge

def WalkCompleted
    (pr pe : List Int) (x total : Int) : Prop :=
  total = WalkSuffix pr pe x 0 1

def OrbitCoverUpperBound
    (m x cycle_count : Int) : Prop :=
  ∃ traps,
    CatchesAll m x traps ∧
    Zlength traps = cycle_count + 1

def OrbitCoverLowerBound
    (m x cycle_count : Int) : Prop :=
  ∀ traps,
    CatchesAll m x traps →
    cycle_count + 1 ≤ Zlength traps

end P090_WalkBridge

export P090_WalkBridge (WalkCompleted OrbitCoverUpperBound OrbitCoverLowerBound)

namespace P090_TableBudget

inductive OrderedPrimeTable : List Int → List Int → Prop where
| ordered_prime_table_nil : OrderedPrimeTable [] []
| ordered_prime_table_cons : ∀ p exponent pr pe,
    IsPrime p →
    1 ≤ exponent →
    Forall (fun q => p < q) pr →
    OrderedPrimeTable pr pe →
    OrderedPrimeTable (p :: pr) (exponent :: pe)
export OrderedPrimeTable (ordered_prime_table_nil ordered_prime_table_cons)

def enumerated_phi_sum (pr pe : List Int) (d : Int) : Int :=
  match pr, pe with
  | p :: pr', exponent :: pe' =>
      sum_nat_range 0 (Nat.succ (Int.toNat exponent))
        (fun k => enumerated_phi_sum pr' pe'
          (d * p ^ᶻ Int.ofNat k))
  | _, _ => EulerPhi d

def CoprimeToTable (d : Int) (pr : List Int) : Prop :=
  Forall (fun p => Z.gcd d p = 1) pr

end P090_TableBudget

export P090_TableBudget (OrderedPrimeTable ordered_prime_table_nil ordered_prime_table_cons enumerated_phi_sum CoprimeToTable)

namespace P090_DivisorEnumeration

inductive ExponentTrace : List Int → List Int → List Int → Int → Prop where
| exponent_trace_nil :
    ExponentTrace [] [] [] 1
| exponent_trace_cons : ∀ p pr maximum pe exponent exponents product,
    (0 ≤ exponent ∧ exponent ≤ maximum) →
    ExponentTrace pr pe exponents product →
    ExponentTrace (p :: pr) (maximum :: pe) (exponent :: exponents)
      (Z.pow p exponent * product)
export ExponentTrace (exponent_trace_nil exponent_trace_cons)

def enumerated_products (pr pe : List Int) : List Int :=
  match pr, pe with
  | p :: pr', maximum :: pe' =>
      List.flatten
        (List.map
           (fun n =>
              List.map (fun product => Z.pow p (Int.ofNat n) * product)
                (enumerated_products pr' pe'))
           (List.range' 0 (Nat.succ (Int.toNat maximum))))
  | _, _ => [1]

def enumerated_walk_terms
    (pr pe : List Int) (x d : Int) : List Int :=
  match pr, pe with
  | p :: pr', maximum :: pe' =>
      List.flatten
        (List.map
           (fun n =>
              enumerated_walk_terms pr' pe' x
                (d * Z.pow p (Int.ofNat n)))
           (List.range' 0 (Nat.succ (Int.toNat maximum))))
  | _, _ => [CycleTerm x d]

def NonUnitDivisorCycleSum
    (pr pe : List Int) (x : Int) : Int :=
  List.foldr Int.add 0
    (List.map (CycleTerm x)
      (List.filter (fun d => Bool.not ((· == ·) d 1))
        (enumerated_products pr pe)))

inductive PrefixSelectedTrace (pr pe : List Int) :
    Int → List Int → Int → Prop where
| prefix_selected_trace_zero :
    PrefixSelectedTrace pr pe 0 [] 1
| prefix_selected_trace_step : ∀ i exponents d exponent,
    PrefixSelectedTrace pr pe i exponents d →
    (0 ≤ i ∧ i < Zlength pr) →
    (0 ≤ exponent ∧ exponent ≤ Znth i pe 0) →
    PrefixSelectedTrace pr pe (i + 1) (exponents ++ [exponent])
      (d * Z.pow (Znth i pr 0) exponent)
export PrefixSelectedTrace (prefix_selected_trace_zero prefix_selected_trace_step)

end P090_DivisorEnumeration

export P090_DivisorEnumeration (ExponentTrace exponent_trace_nil exponent_trace_cons enumerated_products enumerated_walk_terms NonUnitDivisorCycleSum PrefixSelectedTrace prefix_selected_trace_zero prefix_selected_trace_step)

namespace P090_DivisorCompleteness

inductive CanonicalFactorTable : List Int → List Int → Prop where
| canonical_factor_table_nil :
    CanonicalFactorTable [] []
| canonical_factor_table_cons : ∀ p pr exponent pe,
    prime p →
    1 ≤ exponent →
    CanonicalFactorTable pr pe →
    ¬ (p ∣ᶻ factor_product pr pe) →
    CanonicalFactorTable (p :: pr) (exponent :: pe)
export CanonicalFactorTable (canonical_factor_table_nil canonical_factor_table_cons)

def enumerated_exponent_vectors (pe : List Int) : List (List Int) :=
  match pe with
  | [] => [[]]
  | maximum :: pe' =>
      List.flatten
        (List.map
          (fun n => List.map (List.cons (Int.ofNat n))
            (enumerated_exponent_vectors pe'))
          (List.range' 0 (Nat.succ (Int.toNat maximum))))

def exponent_vector_product (pr exponents : List Int) : Int :=
  match pr, exponents with
  | p :: pr', exponent :: exponents' =>
      Z.pow p exponent * exponent_vector_product pr' exponents'
  | _, _ => 1

end P090_DivisorCompleteness

export P090_DivisorCompleteness (CanonicalFactorTable canonical_factor_table_nil canonical_factor_table_cons enumerated_exponent_vectors exponent_vector_product)

namespace P090_OrderInputBridge

namespace ETI
-- Coq module alias: euler_theorem_inverse_lib.
export SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib (EulerTotientValue EulerPhi EulerTheoremInverse EulerPhiResidual EulerPrime NoPrimeDivisorBelow EulerPhiProgress EulerPhiFactorCompletion EulerPhiFactorCompletion_divide EulerPhiRemovalProgress EulerPhiRemovalProgress_complete EulerModularPowerProgress euler_prime_from_prime__euler_phi_final_results euler_prime_divisor_exists__euler_phi_final_results euler_residue_bounds__inverse_final_result euler_factor_prime__euler_phi_setup_removal euler_prime_power_relprime_iff__euler_phi_setup_removal euler_prime_power_multiple_count__euler_phi_setup_removal euler_totient_prime_power__euler_phi_setup_removal euler_relprime_product_divide__euler_phi_setup_removal euler_list_prod_nodup__euler_phi_setup_removal euler_residue_mod_member__euler_phi_setup_removal euler_crt_solution_mod_left__euler_phi_setup_removal euler_crt_solution_mod_right__euler_phi_setup_removal euler_crt_residue_pair_injective__euler_phi_setup_removal euler_totient_multiplicative__euler_phi_setup_removal euler_totient_coprime_prime_power__euler_phi_setup_removal euler_phi_removal_start__euler_phi_setup_removal euler_prime_two__euler_phi_factor_completion euler_exact_positive_quotient_bounds__euler_phi_factor_completion euler_progress_advance_nondivisor__euler_phi_factor_completion euler_completed_progress__euler_phi_factor_completion euler_active_frontier_bound__euler_phi_factor_completion euler_prime_to_prime__euler_phi_final_results euler_remaining_prime__euler_phi_final_results euler_filter_all_true__euler_phi_final_results euler_totient_of_prime__euler_phi_final_results euler_progress_terminal_prime__euler_phi_final_results euler_progress_terminal_one__euler_phi_final_results euler_modular_progress_odd_step__modular_power_loop euler_modular_progress_even_step__modular_power_loop bounded_residue_product_int__modular_power_loop euler_modular_progress_zero_finish__modular_power_final euler_coprime_residue_member__inverse_final_result euler_residue_map_member__inverse_final_result euler_residue_map_injective__inverse_final_result euler_residue_map_nodup__inverse_final_result euler_residue_map_permutation__inverse_final_result euler_product_permutation__inverse_final_result euler_mapped_product_mod__inverse_final_result euler_residue_product_coprime__inverse_final_result euler_power_totient_mod__inverse_final_result euler_totient_inverse_theorem__inverse_final_result)
end ETI

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess

end P090_OrderInputBridge

-- Coq exports P090_OrderInputBridge; its proof declarations are migrated separately.

namespace P090_FactorConsumer

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess

def StrictTrialState
    (m candidate remainder : Int) (pr pe : List Int) : Prop :=
  StrictFactorPrefix m candidate remainder pr pe

def StrictFactorAtPrime
    (m candidate original_remainder remainder exponent : Int)
    (pr pe : List Int) : Prop :=
  StrictFactorPrefix m candidate original_remainder pr pe ∧
  IsPrime candidate ∧
  original_remainder mod candidate = 0 ∧
  0 ≤ exponent ∧
  original_remainder = Z.pow candidate exponent * remainder ∧
  (0 < remainder ∧ remainder ≤ original_remainder)

end P090_FactorConsumer

export P090_FactorConsumer (StrictTrialState StrictFactorAtPrime)

namespace P090_FactorMachineBounds

def FactorInputLimit : Int := 100000000000000

def FactorCandidateGuardLimit : Int := 10000000

def FactorCandidateStateLimit : Int := 10000001

def Signed64Max : Int := 9223372036854775807

def FactorMachineTrialState
    (m candidate remainder : Int) (pr pe : List Int) : Prop :=
  StrictTrialState m candidate remainder pr pe ∧
  m ≤ FactorInputLimit ∧
  candidate ≤ FactorCandidateStateLimit

def FactorMachineAtPrime
    (m candidate original remainder exponent : Int)
    (pr pe : List Int) : Prop :=
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ∧
  m ≤ FactorInputLimit ∧
  candidate ≤ FactorCandidateGuardLimit

end P090_FactorMachineBounds

export P090_FactorMachineBounds (FactorInputLimit FactorCandidateGuardLimit FactorCandidateStateLimit Signed64Max FactorMachineTrialState FactorMachineAtPrime)

namespace P090_OrderConsumer

open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrderExcess.P090_OrderExcess

end P090_OrderConsumer

-- Coq exports P090_OrderConsumer; its proof declarations are migrated separately.

namespace P090_WalkConsumer

end P090_WalkConsumer

-- Coq exports P090_WalkConsumer; its proof declarations are migrated separately.

namespace P090_WalkCallBudget

end P090_WalkCallBudget

-- Coq exports P090_WalkCallBudget; its proof declarations are migrated separately.

namespace P090_PrimePowerConsumer

end P090_PrimePowerConsumer

-- Coq exports P090_PrimePowerConsumer; its proof declarations are migrated separately.

namespace P090_WalkExponentConsumer

def WalkExponentPhiUpdate
    (p exponent ph : Int) : Int :=
  if (· == ·) exponent 1 then p - 1 else ph * p

end P090_WalkExponentConsumer

export P090_WalkExponentConsumer (WalkExponentPhiUpdate)

namespace P090_OrbitQuotient

namespace OrderExact
-- Coq module alias: P090_OrderExact.P090_OrderExact.
end OrderExact

def OrbitHit (m x start room : Int) : Prop :=
  ∃ time, 0 ≤ time ∧
    room = (start * x ^ᶻ time) mod m

def OrbitSeparated
    (m x : Int) (representatives : List Int) : Prop :=
  ∀ left right room,
    (left ∈ representatives) →
    (right ∈ representatives) →
    OrbitHit m x left room →
    OrbitHit m x right room →
    left = right

def OrbitCoversRange
    (m x : Int) (representatives : List Int) : Prop :=
  ∀ start,
    (0 ≤ start ∧ start < m) →
    ∃ representative,
      (representative ∈ representatives) ∧
      OrbitHit m x start representative

def OrbitRepresentativeSystem
    (m x : Int) (representatives : List Int) : Prop :=
  NoDup representatives ∧
  Forall (fun room => (0 ≤ room ∧ room < m)) representatives ∧
  OrbitCoversRange m x representatives ∧
  OrbitSeparated m x representatives

def StratumCovers
    (m x gcd_value : Int) (representatives : List Int) : Prop :=
  ∀ start,
    (0 ≤ start ∧ start < m) →
    Z.gcd start m = gcd_value →
    ∃ representative,
      (representative ∈ representatives) ∧
      OrbitHit m x start representative

def StratumRepresentativeSystem
    (m x gcd_value : Int) (representatives : List Int) : Prop :=
  NoDup representatives ∧
  Forall
    (fun room => (0 ≤ room ∧ room < m) ∧ Z.gcd room m = gcd_value)
    representatives ∧
  StratumCovers m x gcd_value representatives ∧
  OrbitSeparated m x representatives

def UnitOrbitList
    (modulus x unit : Int) : List Int :=
  List.map
    (fun index : Nat =>
       (unit * x ^ᶻ Int.ofNat index) mod modulus)
    (List.range' 0 (Int.toNat (Ord x modulus)))

def EquivalenceLaws (relation : Int → Int → Prop) : Prop :=
  (∀ item, relation item item) ∧
  (∀ left right, relation left right → relation right left) ∧
  (∀ left middle right,
      relation left middle → relation middle right → relation left right)

def CanonicalKey
    (relatedb : Int → Int → Bool) («universe» : List Int) (item : Int) : Int :=
  match List.find? (relatedb item) «universe» with
  | some representative => representative
  | none => 0

def FiniteQuotient
    (relatedb : Int → Int → Bool) («universe» : List Int) : List Int :=
  List.dedup (List.map (CanonicalKey relatedb «universe») «universe»)

def UnitOrbitRelatedb
    (modulus x left right : Int) : Bool :=
  coq_existsb ((· == ·) right) (UnitOrbitList modulus x left)

end P090_OrbitQuotient

export P090_OrbitQuotient (OrbitHit OrbitSeparated OrbitCoversRange OrbitRepresentativeSystem StratumCovers StratumRepresentativeSystem UnitOrbitList EquivalenceLaws CanonicalKey FiniteQuotient UnitOrbitRelatedb)

namespace P090_UnitOrbitPartition

namespace ETI
-- Coq module alias: euler_theorem_inverse_lib.
export SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib (EulerTotientValue EulerPhi EulerTheoremInverse EulerPhiResidual EulerPrime NoPrimeDivisorBelow EulerPhiProgress EulerPhiFactorCompletion EulerPhiFactorCompletion_divide EulerPhiRemovalProgress EulerPhiRemovalProgress_complete EulerModularPowerProgress euler_prime_from_prime__euler_phi_final_results euler_prime_divisor_exists__euler_phi_final_results euler_residue_bounds__inverse_final_result euler_factor_prime__euler_phi_setup_removal euler_prime_power_relprime_iff__euler_phi_setup_removal euler_prime_power_multiple_count__euler_phi_setup_removal euler_totient_prime_power__euler_phi_setup_removal euler_relprime_product_divide__euler_phi_setup_removal euler_list_prod_nodup__euler_phi_setup_removal euler_residue_mod_member__euler_phi_setup_removal euler_crt_solution_mod_left__euler_phi_setup_removal euler_crt_solution_mod_right__euler_phi_setup_removal euler_crt_residue_pair_injective__euler_phi_setup_removal euler_totient_multiplicative__euler_phi_setup_removal euler_totient_coprime_prime_power__euler_phi_setup_removal euler_phi_removal_start__euler_phi_setup_removal euler_prime_two__euler_phi_factor_completion euler_exact_positive_quotient_bounds__euler_phi_factor_completion euler_progress_advance_nondivisor__euler_phi_factor_completion euler_completed_progress__euler_phi_factor_completion euler_active_frontier_bound__euler_phi_factor_completion euler_prime_to_prime__euler_phi_final_results euler_remaining_prime__euler_phi_final_results euler_filter_all_true__euler_phi_final_results euler_totient_of_prime__euler_phi_final_results euler_progress_terminal_prime__euler_phi_final_results euler_progress_terminal_one__euler_phi_final_results euler_modular_progress_odd_step__modular_power_loop euler_modular_progress_even_step__modular_power_loop bounded_residue_product_int__modular_power_loop euler_modular_progress_zero_finish__modular_power_final euler_coprime_residue_member__inverse_final_result euler_residue_map_member__inverse_final_result euler_residue_map_injective__inverse_final_result euler_residue_map_nodup__inverse_final_result euler_residue_map_permutation__inverse_final_result euler_product_permutation__inverse_final_result euler_mapped_product_mod__inverse_final_result euler_residue_product_coprime__inverse_final_result euler_power_totient_mod__inverse_final_result euler_totient_inverse_theorem__inverse_final_result)
end ETI

def UnitResidue (modulus unit : Int) : Prop :=
  (0 ≤ unit ∧ unit < modulus) ∧ Z.gcd unit modulus = 1

def UnitResidueb (modulus unit : Int) : Bool :=
  (decide (0 ≤ unit)) && (decide (unit < modulus)) &&
  (· == ·) (Z.gcd unit modulus) 1

def UnitResidues (modulus : Int) : List Int :=
  List.map Int.ofNat
    (List.filter
      (fun k : Nat => (· == ·) (Z.gcd (Int.ofNat k) modulus) 1)
      (List.range' 1 (Int.toNat modulus)))

def UnitOrbitEquiv
    (modulus x left right : Int) : Prop :=
  if UnitResidueb modulus left
  then UnitResidue modulus right ∧ OrbitHit modulus x left right
  else left = right

def UnitOrbitEquivb
    (modulus x left right : Int) : Bool :=
  if UnitResidueb modulus left
  then UnitResidueb modulus right && UnitOrbitRelatedb modulus x left right
  else (· == ·) left right

def UnitRepresentatives (modulus x : Int) : List Int :=
  FiniteQuotient
    (UnitOrbitEquivb modulus x)
    (UnitResidues modulus)

def UnitOrbitBlocks (modulus x : Int) : List Int :=
  List.flatten
    (List.map (UnitOrbitList modulus x)
      (UnitRepresentatives modulus x))

def UnitOrbitRepresentativeSystem
    (modulus x : Int) (representatives : List Int) : Prop :=
  StratumRepresentativeSystem modulus x 1 representatives

end P090_UnitOrbitPartition

export P090_UnitOrbitPartition (UnitResidue UnitResidueb UnitResidues UnitOrbitEquiv UnitOrbitEquivb UnitRepresentatives UnitOrbitBlocks UnitOrbitRepresentativeSystem)

namespace P090_GcdStratumTransport

namespace OQ
-- Coq module alias: P090_OrbitQuotient.
export SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.P090_OrbitQuotient (OrbitHit OrbitSeparated OrbitCoversRange OrbitRepresentativeSystem StratumCovers StratumRepresentativeSystem UnitOrbitList EquivalenceLaws CanonicalKey FiniteQuotient UnitOrbitRelatedb)
end OQ

namespace OE
-- Coq module alias: P090_OrderExact.P090_OrderExact.
end OE

def StratumLift (m d unit : Int) : Int :=
  (m /ᶻ d) * unit

def StratumProject (m d room : Int) : Int :=
  room /ᶻ (m /ᶻ d)

def LiftedRepresentatives
    (m d : Int) (representatives : List Int) : List Int :=
  List.map (StratumLift m d) representatives

end P090_GcdStratumTransport

export P090_GcdStratumTransport (StratumLift StratumProject LiftedRepresentatives)

namespace P090_DivisorCycleBridge

def positive_divisor_list (m : Int) : List Int :=
  List.filter
    (fun d => (· == ·) (m mod d) 0)
    (List.map Int.ofNat (List.range' 1 (Int.toNat m)))

def ConcreteNonUnitDivisorCycleSum (m x : Int) : Int :=
  List.foldr Int.add 0
    (List.map (CycleTerm x)
      (List.filter (fun d => Bool.not ((· == ·) d 1))
        (positive_divisor_list m)))

def RoomZeroCycleTotal (m x : Int) : Int :=
  1 + ConcreteNonUnitDivisorCycleSum m x

end P090_DivisorCycleBridge

export P090_DivisorCycleBridge (positive_divisor_list ConcreteNonUnitDivisorCycleSum RoomZeroCycleTotal)

namespace P090_GlobalOrbitBridge

def AlignedStratumSystems
    (m x : Int) (gcd_values : List Int) (blocks : List (List Int)) : Prop :=
  Forall2
    (fun gcd_value representatives =>
       StratumRepresentativeSystem m x gcd_value representatives)
    gcd_values blocks

def ExactNonUnitDivisorSystems
    (m x : Int) (divisors : List Int) (blocks : List (List Int)) : Prop :=
  Forall2
    (fun divisor representatives =>
       1 < divisor ∧
       (divisor ∣ᶻ m) ∧
       StratumRepresentativeSystem
         m x (m /ᶻ divisor) representatives ∧
       Zlength representatives = CycleTerm x divisor)
    divisors blocks

def ExactZeroStratumSystem
    (m x : Int) (zero_block : List Int) : Prop :=
  StratumRepresentativeSystem m x m zero_block ∧
  Zlength zero_block = 1

def DivisorStrataClassify
    (m : Int) (divisors : List Int) : Prop :=
  ∀ start,
    (0 ≤ start ∧ start < m) →
    Z.gcd start m = m ∨
    ∃ divisor,
      (divisor ∈ divisors) ∧
      Z.gcd start m = m /ᶻ divisor

def DistinctGlobalStratumKeys
    (m : Int) (divisors : List Int) : Prop :=
  NoDup (m :: List.map (fun divisor => m /ᶻ divisor) divisors)

end P090_GlobalOrbitBridge

export P090_GlobalOrbitBridge (AlignedStratumSystems ExactNonUnitDivisorSystems ExactZeroStratumSystem DivisorStrataClassify DistinctGlobalStratumKeys)

namespace P090_DivisorStrataKeys

def concrete_nonunit_divisors (m : Int) : List Int :=
  List.filter (fun divisor => Bool.not ((· == ·) divisor 1))
    (positive_divisor_list m)

end P090_DivisorStrataKeys

export P090_DivisorStrataKeys (concrete_nonunit_divisors)

namespace P090_FinalOrbitInstantiation

def ConcreteZeroBlock (m : Int) : List Int :=
  LiftedRepresentatives m 1 [0]

def ConcreteNonUnitBlock
    (m x divisor : Int) : List Int :=
  LiftedRepresentatives m divisor
    (UnitRepresentatives divisor (x mod divisor))

def ConcreteNonUnitBlocks
    (m x : Int) : List (List Int) :=
  List.map (ConcreteNonUnitBlock m x)
    (concrete_nonunit_divisors m)

end P090_FinalOrbitInstantiation

export P090_FinalOrbitInstantiation (ConcreteZeroBlock ConcreteNonUnitBlock ConcreteNonUnitBlocks)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
