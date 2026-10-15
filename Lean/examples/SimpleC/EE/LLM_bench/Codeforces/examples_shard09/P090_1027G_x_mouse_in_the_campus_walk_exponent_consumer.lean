import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_prime_power_consumer
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_WalkExponentConsumer

theorem walk_exponent_init_from_table (m p : Int) (pr pe : List Int) (i : Int) :
    2 ≤ m → ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    WalkExponentState m p 1 (Znth i pe 0) 1 1 := by
  intro hm hv hi hp
  have hentry := valid_factor_table_entry m pr pe i hv hi
  have hpd := valid_table_power_at_divides_m m pr pe i 1 hv hi ⟨by omega,hentry.2⟩
  rw [← hp] at hpd hentry
  have hp1 : Z.pow p 1 = p := by simp [Z.pow]
  rw [hp1] at hpd
  have hple := Int.le_of_dvd (by omega : 0 < m) ((Z.divide_iff_dvd _ _).mp hpd)
  exact ⟨⟨by have := hentry.1.1; omega,hple⟩,by omega,by omega,by omega,rfl,rfl⟩

theorem walk_exponent_pk_step (p exponent pk : Int) :
    1 ≤ exponent → pk = Z.pow p (exponent-1) → pk*p = Z.pow p exponent := by
  intro he hp
  rw [hp]
  have h := coq_pow_add p (exponent-1) 1 (by omega) (by omega)
  simpa [Z.pow,show exponent-1+1=exponent by omega] using h.symm

theorem walk_exponent_phi_step (p exponent pk ph : Int) :
    IsPrime p → 1 ≤ exponent → pk = Z.pow p (exponent-1) → ph = EulerPhi pk →
    WalkExponentPhiUpdate p exponent ph = EulerPhi (pk*p) := by
  intro hp he hpk hph
  have hp1 : Z.pow p 1 = p := by simp [Z.pow]
  by_cases he1 : exponent = 1
  · subst exponent
    have hpk1 : pk = 1 := by simpa [Z.pow] using hpk
    rw [hpk1]
    have hphi := euler_phi_prime_power p 1 hp (by omega)
    simpa [WalkExponentPhiUpdate,Z.pow] using hphi.symm
  · have hfalse : (exponent == 1) = false := by simp [he1]
    have hstep := walk_exponent_pk_step p exponent pk he hpk
    unfold WalkExponentPhiUpdate
    dsimp only
    rw [hfalse]
    simp only [Bool.false_eq_true,↓reduceIte]
    rw [hph,hstep,hpk,euler_phi_prime_power p (exponent-1) hp (by omega),euler_phi_prime_power p exponent hp he]
    have hpower := coq_pow_add p (exponent-2) 1 (by omega) (by omega)
    rw [hp1] at hpower
    have heq : exponent-2+1 = exponent-1 := by omega
    rw [heq] at hpower
    rw [hpower]
    have heq2 : exponent-1-1 = exponent-2 := by omega
    rw [heq2]
    ring

theorem positive_prime_power_divisor_bound (m p exponent : Int) :
    0 < m → 1 < p → 0 ≤ exponent → Z.pow p exponent ∣ᶻ m →
    1 ≤ Z.pow p exponent ∧ Z.pow p exponent ≤ m := by
  intro hm hp he hd
  have hpos := coq_pow_pos p exponent (by omega) he
  exact ⟨by omega,Int.le_of_dvd hm ((Z.divide_iff_dvd _ _).mp hd)⟩

theorem walk_exponent_step_from_table (m p exponent maximum pk ph : Int) (pr pe : List Int) (i : Int) :
    m ≤ 100000000000000 → ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    maximum = Znth i pe 0 → exponent ≤ maximum → WalkExponentState m p exponent maximum pk ph →
    WalkExponentState m p (exponent+1) maximum (pk*p) (WalkExponentPhiUpdate p exponent ph) ∧
    pk*p = Z.pow p exponent ∧ WalkExponentPhiUpdate p exponent ph = EulerPhi (pk*p) ∧
    (0 ≤ pk*p ∧ pk*p ≤ 18446744073709551615) ∧
    (0 ≤ WalkExponentPhiUpdate p exponent ph ∧ WalkExponentPhiUpdate p exponent ph ≤ 18446744073709551615) := by
  intro hm hv hi hp hmax hguard hs
  obtain ⟨hpb,heb,hpkb,hphb,hpk,hph⟩ := hs
  have hprime : IsPrime p := by rw [hp]; exact (valid_factor_table_entry m pr pe i hv hi).1
  have hpd : Z.pow p exponent ∣ᶻ m := by
    rw [hp]
    exact valid_table_power_at_divides_m m pr pe i exponent hv hi ⟨by omega,by omega⟩
  have hpowb := positive_prime_power_divisor_bound m p exponent (by omega) hprime.1 (by omega) hpd
  have hpkstep := walk_exponent_pk_step p exponent pk heb.1 hpk
  have hphstep := walk_exponent_phi_step p exponent pk ph hprime heb.1 hpk hph
  have hpos : 0 < pk*p := by omega
  have hphib := euler_phi_positive_bounded (pk*p) (by omega)
  have hpknew : pk*p = Z.pow p (exponent+1-1) := by simpa using hpkstep
  refine ⟨⟨hpb,by omega,by omega,?_,hpknew,hphstep⟩,hpkstep,hphstep,by omega,?_⟩
  · rw [hphstep]; omega
  · rw [hphstep]; omega

theorem walk_exponent_step_first_from_table (m p maximum pk ph : Int) (pr pe : List Int) (i : Int) :
    m ≤ 100000000000000 → ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    maximum = Znth i pe 0 → WalkExponentState m p 1 maximum pk ph →
    WalkExponentState m p 2 maximum (pk*p) (p-1) ∧ pk*p = Z.pow p 1 ∧ p-1 = EulerPhi (pk*p) ∧
    (0 ≤ pk*p ∧ pk*p ≤ 18446744073709551615) ∧ (0 ≤ p-1 ∧ p-1 ≤ 18446744073709551615) := by
  intro hm hv hi hp hmax hs
  have hmaxpos := (valid_factor_table_entry m pr pe i hv hi).2
  simpa [WalkExponentPhiUpdate] using walk_exponent_step_from_table m p 1 maximum pk ph pr pe i hm hv hi hp hmax (by omega) hs

theorem walk_exponent_step_later_from_table (m p exponent maximum pk ph : Int) (pr pe : List Int) (i : Int) :
    m ≤ 100000000000000 → ValidFactorTable m pr pe → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    maximum = Znth i pe 0 → 1 < exponent → exponent ≤ maximum → WalkExponentState m p exponent maximum pk ph →
    WalkExponentState m p (exponent+1) maximum (pk*p) (ph*p) ∧ pk*p = Z.pow p exponent ∧ ph*p = EulerPhi (pk*p) ∧
    (0 ≤ pk*p ∧ pk*p ≤ 18446744073709551615) ∧ (0 ≤ ph*p ∧ ph*p ≤ 18446744073709551615) := by
  intro hm hv hi hp hmax he hg hs
  have hn : exponent ≠ 1 := by omega
  simpa [WalkExponentPhiUpdate,hn] using walk_exponent_step_from_table m p exponent maximum pk ph pr pe i hm hv hi hp hmax hg hs

theorem walk_exponent_ready_for_transition (m p exponent maximum pk ph : Int) :
    (1 ≤ exponent ∧ exponent ≤ maximum) → WalkExponentState m p (exponent+1) maximum pk ph →
    pk = Z.pow p exponent ∧ ph = EulerPhi pk ∧ (1 ≤ pk ∧ pk ≤ m) ∧ (1 ≤ ph ∧ ph ≤ m) := by
  rintro he ⟨hp,hidx,hpkb,hphb,hpk,hph⟩
  exact ⟨by simpa using hpk,hph,hpkb,hphb⟩

theorem walk_exponent_state_consumer_transition (m x p exponent pk ph o g d phi ord : Int) (pr pe : List Int) (i : Int) :
    ValidFactorTable m pr pe → PrefixChoice pr pe x i d phi ord → (0 ≤ i ∧ i < Zlength pr) → p = Znth i pr 0 →
    (1 ≤ exponent ∧ exponent ≤ Znth i pe 0) → WalkGlobalBounds m x →
    WalkExponentState m p (exponent+1) (Znth i pe 0) pk ph → o = Ord (x mod pk) pk → g = Z.gcd ord o →
    OrderInput (x mod pk) pk ph ∧ PrimePowerTransition x d phi ord p exponent pk ph o g (d*pk) (phi*ph) (ord /ᶻ g*o) ∧
    PrefixChoice pr pe x (i+1) (d*pk) (phi*ph) (ord /ᶻ g*o) ∧ WalkMachineBounds m (d*pk) (phi*ph) (ord /ᶻ g*o) := by
  intro hv hc hi hp he hg hs ho hgg
  obtain ⟨hpk,hph,_⟩ := walk_exponent_ready_for_transition m p exponent (Znth i pe 0) pk ph he hs
  exact prime_power_consumer_transition m x p exponent pk ph o g d phi ord pr pe i hv hc hi hp he hg hpk hph ho hgg

theorem walk_exponent_exit (m p exponent maximum pk ph : Int) :
    WalkExponentState m p exponent maximum pk ph → maximum < exponent →
    exponent = maximum+1 ∧ pk = Z.pow p maximum ∧ ph = EulerPhi pk ∧
    (1 ≤ pk ∧ pk ≤ m) ∧ (1 ≤ ph ∧ ph ≤ m) := by
  rintro ⟨hp,he,hpkb,hphb,hpk,hph⟩ hg
  have heq : exponent = maximum+1 := by omega
  exact ⟨heq,by simpa [heq] using hpk,hph,hpkb,hphb⟩

theorem walk_exponent_pending_exit (pr pe : List Int) (m x i d before current p exponent pk ph : Int) :
    WalkExponentState m p exponent (Znth i pe 0) pk ph → Znth i pe 0 < exponent →
    WalkPendingState pr pe m x i d before current exponent →
    current = before+WalkSuffix pr pe x i d ∧ (0 ≤ current ∧ current ≤ m) := by
  intro hs he hp
  have heq := (walk_exponent_exit m p exponent (Znth i pe 0) pk ph hs he).1
  rw [heq] at hp
  exact walk_pending_finish pr pe m x i d before current hp
end P090_WalkExponentConsumer
export P090_WalkExponentConsumer (walk_exponent_init_from_table walk_exponent_pk_step walk_exponent_phi_step
  positive_prime_power_divisor_bound walk_exponent_step_from_table walk_exponent_step_first_from_table
  walk_exponent_step_later_from_table walk_exponent_ready_for_transition walk_exponent_state_consumer_transition
  walk_exponent_exit walk_exponent_pending_exit)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
