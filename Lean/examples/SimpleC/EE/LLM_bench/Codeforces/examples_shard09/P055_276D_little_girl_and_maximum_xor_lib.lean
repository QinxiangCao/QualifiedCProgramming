import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.Int.Bitwise
import Mathlib.Tactic.Lift

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib
open AUXLib


open MaxMinLib

def Pre (l r : Int) : Prop := True
def Spec (l r out : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun v => ∃ a b, (l ≤ a ∧ a ≤ b) ∧ b ≤ r ∧ v = Z.lxor a b) (fun x => x) out

def HighestBitScan (l r x b : Int) : Prop :=
  x = Z.lxor l r ∧ ∀ k, (b < k ∧ k ≤ 63) → Z.land (Z.shiftr x k) 1 = 0

private theorem xor_native (a b : Int) : Z.lxor a b=Int.xor a b := by cases a <;> cases b <;> rfl

theorem xor_self (a : Int) : Z.lxor a a=0 := by
  cases a with
  | ofNat a => exact congrArg Int.ofNat (Nat.xor_self a)
  | negSucc a => exact congrArg Int.ofNat (Nat.xor_self a)

theorem xor_zero_iff (a b : Int) : Z.lxor a b=0 ↔ a=b := by
  constructor
  · intro he
    apply Z.bits_inj'
    intro n hn
    have h := congrArg (fun v => Z.testbit v n) he
    have hz : Z.testbit 0 n=false := by cases n <;> simp only [Z.testbit,Nat.zero_testBit]
    change Z.testbit (Z.lxor a b) n=Z.testbit 0 n at h
    rw [Z.lxor_spec,hz] at h
    cases ha : Z.testbit a n <;> cases hb : Z.testbit b n <;> rw [ha,hb] at h
    all_goals first | rfl | cases h
  · intro he
    subst b
    exact xor_self a

theorem xor_nonneg (a b : Int) (ha : 0≤a) (hb : 0≤b) : 0≤Z.lxor a b := by
  cases a <;> cases b <;> simp_all [Z.lxor]

private theorem pow_nat (a : Int) (n : Nat) : Z.pow a (Int.ofNat n)=a^n := rfl

private theorem shiftr_nat (a : Int) (n : Nat) : Z.shiftr a (Int.ofNat n)=a >>> n := by
  cases n with
  | zero => change a <<< (0:Nat)=a >>> (0:Nat); simp only [Int.shiftLeft_zero,Int.shiftRight_zero]
  | succ n => rfl

private theorem and_one_mod (a : Int) : Z.land a 1=a%2 := by
  change Z.land a (Z.ones 1)=a%2
  rw [Z.land_ones a 1 (by omega)]
  exact Int.fmod_eq_emod_of_nonneg _ (by decide)

private theorem bit_div (a : Int) (n : Nat) : Z.land (Z.shiftr a (Int.ofNat n)) 1=(a/(2:Int)^n)%2 := by
  rw [and_one_mod,shiftr_nat,Int.shiftRight_eq_div_pow,Int.natCast_pow]
  norm_num only [Nat.cast_ofNat]

private theorem testbit_div (a : Int) (n : Nat) :
    (if Z.testbit a (Int.ofNat n) then (1:Int) else 0)=(a/(2:Int)^n)%2 := by
  have hp : (2:Int)^n=Int.ofNat (2^n) := (Int.natCast_pow 2 n).symm
  cases a with
  | ofNat a =>
    simp only [Z.testbit,Nat.testBit_eq_decide_div_mod_eq]
    have hr := Nat.mod_lt (a/2^n) (by decide : 0<2)
    rw [hp]
    change (if decide (a/2^n%2=1) then (1:Int) else 0)=Int.ofNat (a/2^n%2)
    simp only [Int.ofNat_eq_coe]
    split <;> simp_all <;> omega
  | negSucc a =>
    simp only [Z.testbit,Nat.testBit_eq_decide_div_mod_eq]
    have hr := Nat.mod_lt (a/2^n) (by decide : 0<2)
    rw [Int.negSucc_ediv _ (by positivity),hp]
    change (if !decide (a/2^n%2=1) then (1:Int) else 0)=(-(Int.ofNat (a/2^n)+1))%2
    have hc : (Int.ofNat (a/2^n))%2=Int.ofNat (a/2^n%2) := rfl
    simp only [Int.ofNat_eq_coe] at *
    by_cases hh : a/2^n%2=1
    · simp only [hh,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
      omega
    · have hz : a/2^n%2=0 := by omega
      simp only [hh,decide_false,Bool.not_false,↓reduceIte]
      omega

theorem lxor_u64_bound__bit_scan_transitions (x y : Int) :
    (0≤x ∧ x<Z.pow 2 64) → (0≤y ∧ y<Z.pow 2 64) → Z.lxor x y≤Z.pow 2 64-1 := by
  intro hx hy
  lift x to Nat using hx.1
  lift y to Nat using hy.1
  have hxb : x<2^64 := by have h := hx.2; change (x:Int)<18446744073709551616 at h; omega
  have hyb : y<2^64 := by have h := hy.2; change (y:Int)<18446744073709551616 at h; omega
  have h := Nat.xor_lt_two_pow hxb hyb
  change ((x ^^^ y : Nat):Int)≤18446744073709551615
  omega

theorem land_shiftr_one_bit__interval_maximum (x b : Int) : 0≤b →
    Z.land (Z.shiftr x b) 1=(if Z.testbit x b then 1 else 0) := by
  intro hb
  lift b to Nat using hb
  exact (bit_div x b).trans (testbit_div x b).symm

private theorem xor_bit (a b : Int) (u v : Bool) :
    Z.lxor (2*a+(if u then 1 else 0)) (2*b+(if v then 1 else 0)) =
    2*Z.lxor a b+(if Bool.xor u v then 1 else 0) := by
  simp only [xor_native]
  have he := Int.lxor_bit u a v b
  cases u <;> cases v <;> simpa only [Int.bit_val] using he

private theorem boundary_nat (c : Int) (b : Nat) :
    Z.lxor (c*(2:Int)^(b+1)+(2:Int)^b-1) (c*(2:Int)^(b+1)+(2:Int)^b)=(2:Int)^(b+1)-1 := by
  induction b with
  | zero =>
    have he := xor_bit c c false true
    simpa [xor_self,pow_succ,mul_comm] using he
  | succ b ih =>
    have he := xor_bit (c*(2:Int)^(b+1)+(2:Int)^b-1) (c*(2:Int)^(b+1)+(2:Int)^b) true false
    change Z.lxor (2*(c*(2:Int)^(b+1)+(2:Int)^b-1)+1) (2*(c*(2:Int)^(b+1)+(2:Int)^b)+0) =
      2*Z.lxor (c*(2:Int)^(b+1)+(2:Int)^b-1) (c*(2:Int)^(b+1)+(2:Int)^b)+1 at he
    rw [ih] at he
    calc
      _ = Z.lxor (2*(c*(2:Int)^(b+1)+(2:Int)^b-1)+1) (2*(c*(2:Int)^(b+1)+(2:Int)^b)+0) := by congr 1 <;> ring
      _ = 2*((2:Int)^(b+1)-1)+1 := he
      _ = _ := by ring

theorem boundary_xor__interval_maximum (c b : Int) : 0≤b →
    Z.lxor (c*Z.pow 2 (b+1)+Z.pow 2 b-1) (c*Z.pow 2 (b+1)+Z.pow 2 b)=Z.pow 2 (b+1)-1 := by
  intro hb
  lift b to Nat using hb
  exact boundary_nat c b

private theorem pow_two_pos (n : Nat) : 0<(2:Int)^n := pow_pos (by omega) _

private theorem div_halving (x : Int) (n : Nat) :
    x/(2:Int)^n=2*(x/(2:Int)^(n+1))+(x/(2:Int)^n)%2 := by
  have h := Int.emod_add_mul_ediv (x/(2:Int)^n) 2
  rw [Int.ediv_ediv (by positivity),←pow_succ] at h
  omega

private theorem descending_div_zero (x : Int) (start count : Nat) :
    x/(2:Int)^(start+count)=0 →
    (∀ k, start≤k → k<start+count → (x/(2:Int)^k)%2=0) → x/(2:Int)^start=0 := by
  induction count with
  | zero => intro hz _; simpa only [Nat.add_zero] using hz
  | succ count ih =>
    intro hz hb
    have htop := div_halving x (start+count)
    have hbit := hb (start+count) (by omega) (by omega)
    have hz' : x/(2:Int)^(start+count)=0 := by rw [show start+count+1=start+(count+1) by omega,hz,hbit] at htop; omega
    exact ih hz' (fun k hlo hhi => hb k hlo (by omega))

private theorem scan_div_zero (l r x b : Int) (hb : 0≤b ∧ b≤63)
    (hx : 0≤x ∧ x≤18446744073709551615) (hs : HighestBitScan l r x b) :
    x/(2:Int)^(b.toNat+1)=0 := by
  have hbi : Int.ofNat b.toNat=b := Int.toNat_of_nonneg hb.1
  have hn : b.toNat+1≤64 := by omega
  have hz : x/(2:Int)^64=0 := Int.ediv_eq_zero_of_lt hx.1 (by change x<18446744073709551616; omega)
  apply descending_div_zero x (b.toNat+1) (64-(b.toNat+1))
  · simpa only [Nat.add_sub_of_le hn] using hz
  · intro k hk hk64
    have hkn : k≤63 := by omega
    have hki : b<Int.ofNat k ∧ Int.ofNat k≤63 := by
      simp only [Int.ofNat_eq_coe] at *
      omega
    have hh := hs.2 (Int.ofNat k) hki
    rwa [bit_div] at hh

theorem highest_bit_scan_zero_step__bit_scan_transitions (l r x b : Int) :
    (0<x ∧ x<Z.pow 2 64) → (0≤b ∧ b≤63) → HighestBitScan l r x b →
    Z.land (Z.shiftr x b) 1=0 → 0<b ∧ HighestBitScan l r x (b-1) := by
  intro hx hb hs hbit
  have hp : 0<b := by
    by_contra h
    have hbe : b=0 := by omega
    have hzero := scan_div_zero l r x b hb ⟨by omega,by have h := hx.2; change x<18446744073709551616 at h; omega⟩ hs
    rw [hbe] at hzero hbit
    have hh := div_halving x 0
    have hzbit := bit_div x 0
    change Z.land (Z.shiftr x 0) 1=x/(2:Int)^0%2 at hzbit
    simp only [pow_zero,Int.ediv_one] at hzbit
    change x/2=0 at hzero
    rw [hbit] at hzbit
    norm_num only [pow_zero,pow_one,Int.ediv_one] at hh hzbit
    omega
  refine ⟨hp,hs.1,?_⟩
  intro k hk
  by_cases he : k=b
  · simpa only [he] using hbit
  · exact hs.2 k ⟨by omega,hk.2⟩

private theorem xor_div_pow (a b : Int) (ha : 0≤a) (hb : 0≤b) (n : Nat) :
    Z.lxor a b/(2:Int)^n=Z.lxor (a/(2:Int)^n) (b/(2:Int)^n) := by
  lift a to Nat using ha
  lift b to Nat using hb
  have hp : (2:Int)^n=Int.ofNat (2^n) := (Int.natCast_pow 2 n).symm
  rw [hp]
  change Int.ofNat ((a ^^^ b)/2^n)=Int.ofNat (a/2^n ^^^ b/2^n)
  exact congrArg Int.ofNat Nat.xor_div_two_pow

theorem interval_max_xor_from_scan__interval_maximum (l r x b : Int) :
    (0≤l ∧ l≤r) → (0≤x ∧ x≤18446744073709551615) → (0≤b ∧ b≤63) →
    HighestBitScan l r x b → Z.land (Z.shiftr x b) 1≠0 → Spec l r (Z.pow 2 (b+1)-1) := by
  intro hlr hx hb hs hbit
  let n := b.toNat
  have hnb : Int.ofNat n=b := Int.toNat_of_nonneg hb.1
  let p : Int := 2^n
  let q : Int := 2^(n+1)
  let c : Int := l/q
  have hp : 0<p := pow_two_pos n
  have hq : 0<q := pow_two_pos (n+1)
  have hqp : q=2*p := by dsimp [q,p]; ring
  have hpow : Z.pow 2 (b+1)=q := by rw [←hnb]; rfl
  have hxdiv : x/q=0 := scan_div_zero l r x b hb hx hs
  have hrc : r/q=c := by
    rw [hs.1,xor_div_pow l r hlr.1 (by omega) (n+1)] at hxdiv
    exact ((xor_zero_iff (l/q) (r/q)).mp hxdiv).symm
  have hxb : Z.testbit x (Int.ofNat n)=true := by
    rw [land_shiftr_one_bit__interval_maximum x b hb.1] at hbit
    rw [←hnb] at hbit
    cases he : Z.testbit x (Int.ofNat n) <;> simp only [he,↓reduceIte] at hbit ⊢
    exact False.elim (hbit rfl)
  have hbits : Bool.xor (Z.testbit l (Int.ofNat n)) (Z.testbit r (Int.ofNat n))=true := by
    rw [hs.1,Z.lxor_spec] at hxb
    exact hxb
  have hld : l/p=2*c+(if Z.testbit l (Int.ofNat n) then 1 else 0) := by
    have hh := div_halving l n
    rw [←testbit_div] at hh
    exact hh
  have hrd : r/p=2*c+(if Z.testbit r (Int.ofNat n) then 1 else 0) := by
    have hh := div_halving r n
    rw [←testbit_div] at hh
    change r/p=2*(r/q)+(if Z.testbit r (Int.ofNat n) then 1 else 0) at hh
    rwa [hrc] at hh
  have hmono := Int.ediv_le_ediv hp hlr.2
  have hdivs : l/p=2*c ∧ r/p=2*c+1 := by
    cases he1 : Z.testbit l (Int.ofNat n) <;> cases he2 : Z.testbit r (Int.ofNat n)
    all_goals rw [he1,he2] at hbits
    all_goals try cases hbits
    all_goals simp only [he1,he2,Bool.false_eq_true,↓reduceIte] at hld hrd
    all_goals omega
  let a0 := c*q+p-1
  let b0 := c*q+p
  have hlbound : l≤a0 := by
    have hh := Int.emod_add_mul_ediv l p
    have hrm := Int.emod_lt_of_pos l hp
    rw [hdivs.1] at hh
    dsimp [a0]
    rw [hqp]
    nlinarith
  have hrbound : b0≤r := by
    have hh := Int.emod_add_mul_ediv r p
    have hrm := Int.emod_nonneg r (by omega : p≠0)
    rw [hdivs.2] at hh
    dsimp [b0]
    rw [hqp]
    nlinarith
  have hab : a0≤b0 := by dsimp [a0,b0]; omega
  have hxor : Z.lxor a0 b0=q-1 := boundary_nat c n
  have hbound : ∀ a d, (l≤a ∧ a≤d) → d≤r → Z.lxor a d≤q-1 := by
    intro a d had hdr
    have hac : a/q=c := by
      have hh1 := Int.ediv_le_ediv hq had.1
      have hh2 := Int.ediv_le_ediv hq (show a≤r by omega)
      rw [hrc] at hh2
      change c≤a/q at hh1
      omega
    have hdc : d/q=c := by
      have hh1 := Int.ediv_le_ediv hq (show l≤d by omega)
      have hh2 := Int.ediv_le_ediv hq hdr
      rw [hrc] at hh2
      change c≤d/q at hh1
      omega
    have hd0 : Z.lxor a d/q=0 := by
      rw [xor_div_pow a d (by omega) (by omega) (n+1),hac,hdc,xor_self]
    have hrem := Int.emod_add_mul_ediv (Z.lxor a d) q
    have hlt := Int.emod_lt_of_pos (Z.lxor a d) hq
    rw [hd0] at hrem
    omega
  rw [hpow]
  unfold Spec max_value_of_subset max_object_of_subset
  refine ⟨q-1,⟨⟨a0,b0,⟨hlbound,hab⟩,hrbound,hxor.symm⟩,?_⟩,rfl⟩
  rintro v ⟨a,d,had,hdr,rfl⟩
  exact hbound a d had hdr

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P055_276D_little_girl_and_maximum_xor_lib
