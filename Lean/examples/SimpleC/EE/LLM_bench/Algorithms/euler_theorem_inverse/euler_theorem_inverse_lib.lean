import AUXLib.Prime
import SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib
import AUXLib.RelPrime
import SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib
open AUXLib AUXLib.Prime
export SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib (ModularPower)

private abbrev residues (n : Int) : List Nat :=
  (List.range' 1 n.toNat).filter (fun k : Nat => Z.gcd (Int.ofNat k) n == 1)

private theorem zpow_nat (a e : Int) (he : 0≤e) : Z.pow a e=a^e.toNat := by
  cases e <;> simp_all [Z.pow]

private theorem zpow_succ (a e : Int) (he : 0≤e) : Z.pow a (e+1)=Z.pow a e*a := by
  cases e with
  | ofNat e => exact Int.pow_succ a e
  | negSucc e => omega

private theorem zpow_pos (a e : Int) (ha : 0<a) (he : 0≤e) : 0<Z.pow a e := by
  rw [zpow_nat a e he]
  exact Int.pow_pos ha

private theorem zpow_split (a e : Int) (he : 1≤e) : Z.pow a e=a*Z.pow a (e-1) := by
  have h := zpow_succ a (e-1) (by omega)
  simpa [Int.mul_comm] using h

private theorem gcd_fmod (a n : Int) : Int.gcd (a.fmod n) n=Int.gcd a n := by
  have h := Int.fmod_add_mul_fdiv a n
  calc
    _ = Int.gcd (a.fmod n+n*a.fdiv n) n := (Int.gcd_add_mul_left_left n (a.fmod n) (a.fdiv n)).symm
    _ = Int.gcd a n := by rw [h]

private theorem gcd1_mod_nonzero (x n : Int) (hn : 2≤n) (hg : Int.gcd x n=1) : x.fmod n≠0 := by
  intro h0
  have h := gcd_fmod x n
  rw [h0,Int.zero_gcd,hg] at h
  have habs : (n.natAbs : Int)=n := (Int.eq_natAbs_of_nonneg (by omega)).symm
  omega

private theorem gcd1_of_dvd_right (x n d : Int) (hg : Int.gcd x n=1) (hd : d∣n) : Int.gcd x d=1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hcx hcd
  exact Int.gcd_eq_one_iff.mp hg c hcx (Int.dvd_trans hcd hd)

private theorem gcd1_prime (p x : Int) (hp : prime p) (hn : ¬p∣x) : Int.gcd x p=1 := by
  have hp2 := prime_ge_2 p hp
  have hdiv := Int.gcd_dvd_right x p
  have hdx := Int.gcd_dvd_left x p
  have hgpos := Int.gcd_pos_of_ne_zero_right x (by omega : p≠0)
  rcases prime_divisors p hp (Int.gcd x p) ((Z.divide_iff_dvd _ _).2 hdiv) with h | h | h | h
  · omega
  · omega
  · exact False.elim (hn (h ▸ hdx))
  · omega

private theorem mem_residues (n : Int) (k : Nat) :
    k∈residues n ↔ (1≤k ∧ k<1+n.toNat) ∧ Z.gcd (k:Int) n=1 := by
  simp only [residues,List.mem_filter,List.mem_range',Int.ofNat_eq_coe,beq_iff_eq]
  constructor
  · rintro ⟨⟨i,hi,hki⟩,hg⟩
    exact ⟨by omega,hg⟩
  · rintro ⟨hk,hg⟩
    exact ⟨⟨k-1,by omega,by omega⟩,hg⟩

private theorem residue_member (n x : Int) (hn : 2≤n) (hx : 0<x ∧ x<n) (hg : Z.gcd x n=1) :
    x.toNat∈residues n := by
  apply (mem_residues n x.toNat).2
  refine ⟨by omega,?_⟩
  have he : (x.toNat : Int)=x := by omega
  rw [he]
  exact hg

private theorem nodup_map_on {A B : Type} (f : A→B) (l : List A) (hl : l.Nodup)
    (hinj : ∀ x, x∈l → ∀ y,y∈l → f x=f y → x=y) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    have ha := List.nodup_cons.mp hl
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_map.mp hm with ⟨x,hx,hxa⟩
      exact ha.1 (hinj x (by simp [hx]) a (by simp) hxa ▸ hx)
    · exact ih ha.2 (by intro x hx y hy he; exact hinj x (by simp [hx]) y (by simp [hy]) he)

private theorem nodup_perm {A : Type} [DecidableEq A] (l1 l2 : List A)
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hm : ∀ x,x∈l1 ↔ x∈l2) : l1.Perm l2 := by
  apply List.perm_iff_count.mpr
  intro x
  simp only [h1.count,h2.count,hm x]

private theorem perm_of_nodup_subset_length {A : Type} [DecidableEq A] (l1 l2 : List A)
    (hnd : l1.Nodup) (hlen : l1.length=l2.length) (hsub : ∀ x,x∈l1 → x∈l2) : l1.Perm l2 := by
  induction l1 generalizing l2 with
  | nil => have he : l2=[] := List.length_eq_zero_iff.mp hlen.symm; subst l2; exact List.Perm.refl []
  | cons a l ih =>
    have ha := List.nodup_cons.mp hnd
    have ham := hsub a (by simp)
    apply List.cons_perm_iff_perm_erase.mpr
    refine ⟨ham,ih (l2.erase a) ha.2 ?_ ?_⟩
    · rw [List.length_erase_of_mem ham]
      simp only [List.length_cons] at hlen
      omega
    · intro x hx
      have hxa : x≠a := by intro he; subst x; exact ha.1 hx
      exact (List.mem_erase_of_ne hxa).mpr (hsub x (by simp [hx]))

private theorem mod_eq_of_dvd_sub (x y n : Int) (hd : n∣x-y) : x.fmod n=y.fmod n :=
  Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mpr (Int.fmod_eq_zero_of_dvd hd)

private theorem eq_of_dvd_sub_bounds (x y n : Int) (hx : 0≤x ∧ x<n) (hy : 0≤y ∧ y<n)
    (hd : n∣x-y) : x=y := by
  have h := mod_eq_of_dvd_sub x y n hd
  rw [Int.fmod_eq_of_lt hx.1 hx.2,Int.fmod_eq_of_lt hy.1 hy.2] at h
  exact h

private theorem dvd_sub_of_mod_eq (x y n : Int) (he : x.fmod n=y.fmod n) : n∣x-y :=
  Int.dvd_of_fmod_eq_zero (Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mp he)

private theorem coprime_cancel_dvd (n a x : Int) (hg : Int.gcd n a=1) (hd : n∣a*x) : n∣x := by
  have ht := (Int.dvd_gcd_mul_iff_dvd_mul (k:=n) (n:=a) (m:=x)).2 hd
  simpa [hg] using ht

def EulerTotientValue (n : Int) : Int := Int.ofNat (residues n).length

def EulerPhi (n result : Int) : Prop := result = EulerTotientValue n

def EulerTheoremInverse (value modulus inverse : Int) : Prop :=
  ∃ phi : Int, EulerPhi modulus phi ∧ ModularPower value (phi-1) modulus inverse ∧
    Z.modulo (value*inverse) modulus = 1

def EulerPhiResidual (original remaining result : Int) : Prop :=
  Z.divide remaining result ∧ ∀ original_phi remaining_phi : Int,
    EulerPhi original original_phi → EulerPhi remaining remaining_phi →
    original_phi*remaining = result*remaining_phi

def EulerPrime (p : Int) : Prop :=
  1<p ∧ ∀ d : Int, 0<d → Z.divide d p → d=1 ∨ d=p

def NoPrimeDivisorBelow (frontier remaining : Int) : Prop :=
  ∀ p : Int, EulerPrime p → p<frontier → ¬Z.divide p remaining

def EulerPhiProgress (original frontier remaining result : Int) : Prop :=
  EulerPhiResidual original remaining result ∧ NoPrimeDivisorBelow frontier remaining

def EulerPhiFactorCompletion (original factor current result : Int) : Prop :=
  ∀ terminal removed : Int, 0≤removed → current=terminal*Z.pow factor removed →
    Z.modulo terminal factor ≠ 0 → EulerPhiResidual original terminal (Z.div result factor*(factor-1))

theorem EulerPhiFactorCompletion_divide (original factor current result : Int) :
    factor≠0 → Z.modulo current factor=0 → EulerPhiFactorCompletion original factor current result →
    EulerPhiFactorCompletion original factor (Z.div current factor) result := by
  intro hf hm hcomp terminal removed hr he hfree
  apply hcomp terminal (removed+1) (by omega) _ hfree
  rw [zpow_succ factor removed hr]
  have hdiv := Int.fmod_add_mul_fdiv current factor
  change current.fmod factor=0 at hm
  rw [hm] at hdiv
  change current=terminal*(Z.pow factor removed*factor)
  change current.fdiv factor=terminal*Z.pow factor removed at he
  grind

def EulerPhiRemovalProgress (original factor current result : Int) : Prop :=
  ∃ before removed : Int, 0≤removed ∧ before=current*Z.pow factor removed ∧
    Z.divide factor before ∧ Z.divide factor result ∧
    EulerPhiProgress original factor before result ∧ EulerPhiFactorCompletion original factor current result

theorem EulerPhiRemovalProgress_complete (original factor current result : Int) :
    EulerPhiRemovalProgress original factor current result → Z.modulo current factor ≠ 0 →
    EulerPhiResidual original current (Z.div result factor*(factor-1)) := by
  rintro ⟨before,removed,_,_,_,_,_,hcompletion⟩ hfree
  exact hcompletion current 0 (by omega) (by simp [Z.pow]) hfree

def EulerModularPowerProgress (original_base original_exponent modulus current_base remaining_exponent accumulator : Int) : Prop :=
  Z.modulo (accumulator*Z.pow current_base remaining_exponent) modulus = Z.modulo (Z.pow original_base original_exponent) modulus

theorem euler_prime_from_prime__euler_phi_final_results (p : Int) : prime p → EulerPrime p := by
  intro hp
  have hgt := prime_ge_2 p hp
  refine ⟨by omega,?_⟩
  intro d hd hdiv
  rcases prime_divisors p hp d hdiv with h | h | h | h <;> omega

theorem euler_prime_divisor_exists__euler_phi_final_results (k : Int) : 1<k → ∃ q : Int, prime q ∧ Z.divide q k := by
  intro hk
  have aux : ∀ n : Nat, 1<(n:Int) → ∃ q : Int,prime q ∧ Z.divide q (n:Int) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hp : prime (n:Int)
      · exact ⟨n,hp,⟨1,by simp⟩⟩
      · rcases not_prime_divide (n:Int) hn hp with ⟨d,hd,hdiv⟩
        have hdcast : (d.toNat : Int)=d := by omega
        rcases ih d.toNat (by omega) (by omega) with ⟨q,hq,hdq⟩
        rw [hdcast] at hdq
        exact ⟨q,hq,(Z.divide_iff_dvd _ _).2 (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hdq) ((Z.divide_iff_dvd _ _).1 hdiv))⟩
  have he : (k.toNat : Int)=k := by omega
  simpa [he] using aux k.toNat (by omega)

theorem euler_residue_bounds__inverse_final_result (n : Int) (k : Nat) :
    2≤n → k ∈ residues n → (1≤(k:Int) ∧ (k:Int)<n) ∧ Z.gcd (k:Int) n=1 := by
  intro hn hk
  have h := (mem_residues n k).1 hk
  have he : (k:Int)≠n := by
    intro he
    have hg := h.2
    rw [he] at hg
    have hnat := Int.ofNat_inj.mp hg
    rw [Int.gcd_self] at hnat
    have ha : (n.natAbs : Int)=n := (Int.eq_natAbs_of_nonneg (by omega)).symm
    simp only [hnat] at ha
    omega
  exact ⟨by omega,h.2⟩

theorem euler_factor_prime__euler_phi_setup_removal (factor value : Int) :
    2≤factor → Z.divide factor value → NoPrimeDivisorBelow factor value → prime factor := by
  intro hf hfv hbelow
  apply Classical.byContradiction
  intro hn
  rcases not_prime_divide factor (by omega) hn with ⟨d,hd,hdf⟩
  rcases euler_prime_divisor_exists__euler_phi_final_results d hd.1 with ⟨q,hq,hqd⟩
  have hqle := Int.le_of_dvd (by omega : 0<d) ((Z.divide_iff_dvd _ _).1 hqd)
  apply hbelow q (euler_prime_from_prime__euler_phi_final_results q hq) (by omega)
  exact (Z.divide_iff_dvd _ _).2 (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hqd)
    (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hdf) ((Z.divide_iff_dvd _ _).1 hfv)))

theorem euler_prime_power_relprime_iff__euler_phi_setup_removal (p exponent x : Int) :
    prime p → 1≤exponent → (Z.gcd x (Z.pow p exponent)=1 ↔ Z.modulo x p≠0) := by
  intro hp he
  have hp2 := prime_ge_2 p hp
  constructor
  · intro hg hmod
    have hpd : p∣Z.pow p exponent := by
      rw [zpow_split p exponent he]
      exact Int.dvd_mul_right p _
    have hx := gcd1_of_dvd_right x (Z.pow p exponent) p (Int.ofNat_inj.mp hg) hpd
    exact gcd1_mod_nonzero x p hp2 hx hmod
  · intro hn
    have hnd : ¬p∣x := by intro hd; exact hn (Int.fmod_eq_zero_of_dvd hd)
    have hg := gcd1_prime p x hp hnd
    rw [zpow_nat p exponent (by omega)]
    exact congrArg Int.ofNat (Int.gcd_pow_right_of_gcd_eq_one (k:=exponent.toNat) hg)

theorem euler_prime_power_multiple_count__euler_phi_setup_removal (p exponent : Int) :
    prime p → 1≤exponent →
    ((List.range' 1 (Z.pow p exponent).toNat).filter (fun j : Nat => Z.modulo (j:Int) p == 0)).length =
      (Z.pow p (exponent-1)).toNat := by
  intro hp he
  have hp2 := prime_ge_2 p hp
  have htail := zpow_pos p (exponent-1) (by omega) (by omega)
  have hpower := zpow_pos p exponent (by omega) (by omega)
  have hsplit := zpow_split p exponent he
  let source := (List.range' 1 (Z.pow p exponent).toNat).filter (fun j : Nat => Z.modulo (j:Int) p == 0)
  let target := (List.range' 1 (Z.pow p (exponent-1)).toNat).map (fun j : Nat => (p*(j:Int)).toNat)
  have hnd1 : source.Nodup := List.Pairwise.filter _ (List.nodup_range' _)
  have hnd2 : target.Nodup := by
    apply nodup_map_on _ _ (List.nodup_range' _)
    intro x hx y hy heq
    have hx0 := Int.mul_nonneg (by omega : 0≤p) (Int.natCast_nonneg x)
    have hy0 := Int.mul_nonneg (by omega : 0≤p) (Int.natCast_nonneg y)
    have hz : p*(x:Int)=p*(y:Int) := by omega
    have hxy := Int.eq_of_mul_eq_mul_left (by omega : p≠0) hz
    omega
  have hperm := nodup_perm source target hnd1 hnd2 (by
    intro x
    constructor
    · intro hx
      have hh := List.mem_filter.mp hx
      rcases List.mem_range'.mp hh.1 with ⟨i,hi,hxi⟩
      have hxm : (x:Int).fmod p=0 := by simpa only [Z.modulo,beq_iff_eq] using hh.2
      have hdivision := Int.fmod_add_mul_fdiv (x:Int) p
      rw [hxm] at hdivision
      have hxpos : 0<(x:Int) := by omega
      have hqpos : 0<(x:Int).fdiv p := Int.pos_of_mul_pos_right (by omega : 0<p*(x:Int).fdiv p) (by omega)
      have hqle : (x:Int).fdiv p≤Z.pow p (exponent-1) := by
        apply (Int.mul_le_mul_left (by omega : 0<p)).mp
        omega
      apply List.mem_map.mpr
      refine ⟨((x:Int).fdiv p).toNat,?_,?_⟩
      · apply List.mem_range'.mpr
        exact ⟨((x:Int).fdiv p).toNat-1,by omega,by omega⟩
      · have heq : ((((x:Int).fdiv p).toNat : Nat) : Int)=(x:Int).fdiv p := by omega
        rw [heq]
        omega
    · intro hx
      rcases List.mem_map.mp hx with ⟨y,hy,hyx⟩
      rcases List.mem_range'.mp hy with ⟨i,hi,hyi⟩
      have hylo : 1≤(y:Int) := by omega
      have hyhi : (y:Int)≤Z.pow p (exponent-1) := by omega
      have hprodlo := Int.mul_le_mul_of_nonneg_left hylo (by omega : 0≤p)
      have hprodhi := Int.mul_le_mul_of_nonneg_left hyhi (by omega : 0≤p)
      have hcast : (x:Int)=p*(y:Int) := by omega
      apply List.mem_filter.mpr
      constructor
      · apply List.mem_range'.mpr
        exact ⟨x-1,by omega,by omega⟩
      · change (Z.modulo (x:Int) p == 0)=true
        rw [hcast]
        simp [Z.modulo,Int.mul_fmod_right])
  have hlen := hperm.length_eq
  simpa only [target,List.length_map,List.length_range'] using hlen

theorem euler_totient_prime_power__euler_phi_setup_removal (p exponent : Int) :
    prime p → 1≤exponent → EulerTotientValue (Z.pow p exponent)=Z.pow p (exponent-1)*(p-1) := by
  intro hp he
  have hpower := zpow_pos p exponent (by have := prime_ge_2 p hp; omega) (by omega)
  have htail := zpow_pos p (exponent-1) (by have := prime_ge_2 p hp; omega) (by omega)
  have hsplit := zpow_split p exponent he
  let l := List.range' 1 (Z.pow p exponent).toNat
  let divisible := fun j : Nat => Z.modulo (j:Int) p == 0
  have hf : l.filter (fun j : Nat => Z.gcd (j:Int) (Z.pow p exponent)==1) = l.filter (fun j => !(divisible j)) := by
    apply List.filter_congr
    intro j hj
    have hh := euler_prime_power_relprime_iff__euler_phi_setup_removal p exponent (j:Int) hp he
    by_cases hg : Z.gcd (j:Int) (Z.pow p exponent)=1
    · have hm := hh.mp hg
      simp [divisible,hg,hm]
    · have hm : Z.modulo (j:Int) p=0 := by
        apply Classical.byContradiction
        intro hn
        exact hg (hh.mpr hn)
      simp [divisible,hg,hm]
  have hpart := (List.filter_append_perm divisible l).length_eq
  simp only [List.length_append] at hpart
  have hcount := euler_prime_power_multiple_count__euler_phi_setup_removal p exponent hp he
  change (l.filter divisible).length=(Z.pow p (exponent-1)).toNat at hcount
  rw [hcount] at hpart
  have hlen : l.length=(Z.pow p exponent).toNat := List.length_range'
  unfold EulerTotientValue residues
  change Int.ofNat (l.filter (fun j : Nat => Z.gcd (j:Int) (Z.pow p exponent)==1)).length=_
  rw [hf]
  have heq : (Int.ofNat (l.filter (fun j => !(divisible j))).length)=Z.pow p exponent-Z.pow p (exponent-1) := by
    simp only [Int.ofNat_eq_coe]
    omega
  rw [heq,hsplit]
  grind

theorem euler_relprime_product_divide__euler_phi_setup_removal (a b x : Int) :
    rel_prime a b → Z.divide a x → Z.divide b x → Z.divide (a*b) x := by
  intro hr hax hbx
  have hg : Int.gcd a b=1 := Int.ofNat_inj.mp ((Zgcd_1_rel_prime a b).2 hr)
  rcases hax with ⟨q,hq⟩
  have hbq : b∣q := by
    have hm : b∣a*q := by rw [Int.mul_comm,←hq]; exact (Z.divide_iff_dvd _ _).1 hbx
    have hg' : Int.gcd b a=1 := by rw [Int.gcd_comm]; exact hg
    have ht := (Int.dvd_gcd_mul_iff_dvd_mul (k:=b) (n:=a) (m:=q)).2 hm
    simpa [hg'] using ht
  rcases (Z.divide_iff_dvd b q).2 hbq with ⟨r,hr⟩
  exact ⟨r,by grind⟩

theorem euler_list_prod_nodup__euler_phi_setup_removal (A B : Type) (l1 : List A) (l2 : List B) :
    l1.Nodup → l2.Nodup → (l1.flatMap (fun x => l2.map (fun y => (x,y)))).Nodup := by
  intro h1 h2
  induction l1 with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    have h := List.nodup_cons.mp h1
    apply List.nodup_append.mpr
    refine ⟨nodup_map_on (fun y => (a,y)) l2 h2 (by intro x _ y _ he; exact Prod.mk.inj he |>.2),ih h.2,?_⟩
    intro pair hm pair2 hprod heq
    subst pair2
    rcases List.mem_map.mp hm with ⟨y,hy,hpair⟩
    rcases List.mem_flatMap.mp hprod with ⟨x,hx,hmap⟩
    rcases List.mem_map.mp hmap with ⟨z,hz,hpair'⟩
    have he : x=a := by grind
    exact h.1 (he ▸ hx)

theorem euler_residue_mod_member__euler_phi_setup_removal (total modulus : Int) (k : Nat) :
    2≤total → 2≤modulus → Z.divide modulus total → k ∈ residues total →
    (Z.modulo (k:Int) modulus).toNat ∈ residues modulus := by
  intro ht hm hd hk
  have hg := (euler_residue_bounds__inverse_final_result total k ht hk).2
  have hgd := gcd1_of_dvd_right (k:Int) total modulus (Int.ofNat_inj.mp hg) ((Z.divide_iff_dvd _ _).1 hd)
  have hn := gcd1_mod_nonzero (k:Int) modulus hm hgd
  have hnonneg := Int.fmod_nonneg_of_pos (k:Int) (by omega : 0<modulus)
  have hlt := Int.fmod_lt_of_pos (k:Int) (by omega : 0<modulus)
  apply residue_member modulus _ hm ⟨by omega,hlt⟩
  change Int.ofNat (Int.gcd ((k:Int).fmod modulus) modulus)=1
  rw [gcd_fmod,hgd]
  rfl

theorem euler_crt_solution_mod_left__euler_phi_setup_removal (a b x y u v : Int) :
    2≤a → 2≤b → (0≤x ∧ x<a) → u*a+v*b=1 →
    Z.modulo (Z.modulo (x*(v*b)+y*(u*a)) (a*b)) a=x := by
  intro ha hb hx he
  unfold Z.modulo
  rw [Int.fmod_fmod_of_dvd _ (Int.dvd_mul_right a b)]
  have hi : x*(v*b)+y*(u*a)=x+a*(u*(y-x)) := by grind
  rw [hi,Int.add_mul_fmod_self_left]
  exact Int.fmod_eq_of_lt hx.1 hx.2

theorem euler_crt_solution_mod_right__euler_phi_setup_removal (a b x y u v : Int) :
    2≤a → 2≤b → (0≤y ∧ y<b) → u*a+v*b=1 →
    Z.modulo (Z.modulo (x*(v*b)+y*(u*a)) (a*b)) b=y := by
  intro ha hb hy he
  unfold Z.modulo
  rw [Int.fmod_fmod_of_dvd _ (Int.dvd_mul_left a b)]
  have hi : x*(v*b)+y*(u*a)=y+b*(v*(x-y)) := by grind
  rw [hi,Int.add_mul_fmod_self_left]
  exact Int.fmod_eq_of_lt hy.1 hy.2

theorem euler_crt_residue_pair_injective__euler_phi_setup_removal (a b : Int) (x y : Nat) :
    2≤a → 2≤b → rel_prime a b → x ∈ residues (a*b) → y ∈ residues (a*b) →
    ((Z.modulo (x:Int) a).toNat,(Z.modulo (x:Int) b).toNat) =
      ((Z.modulo (y:Int) a).toNat,(Z.modulo (y:Int) b).toNat) → x=y := by
  intro ha hb hab hx hy he
  have hab2 : 2≤a*b := by
    have := Int.mul_le_mul_of_nonneg_left hb (by omega : 0≤a)
    omega
  have hxr := (euler_residue_bounds__inverse_final_result (a*b) x hab2 hx).1
  have hyr := (euler_residue_bounds__inverse_final_result (a*b) y hab2 hy).1
  have hleft := congrArg Prod.fst he
  have hright := congrArg Prod.snd he
  have hma : (x:Int).fmod a=(y:Int).fmod a := by
    have := Int.fmod_nonneg_of_pos (x:Int) (by omega : 0<a)
    have := Int.fmod_nonneg_of_pos (y:Int) (by omega : 0<a)
    change ((x:Int).fmod a).toNat=((y:Int).fmod a).toNat at hleft
    omega
  have hmb : (x:Int).fmod b=(y:Int).fmod b := by
    have := Int.fmod_nonneg_of_pos (x:Int) (by omega : 0<b)
    have := Int.fmod_nonneg_of_pos (y:Int) (by omega : 0<b)
    change ((x:Int).fmod b).toNat=((y:Int).fmod b).toNat at hright
    omega
  have hd := euler_relprime_product_divide__euler_phi_setup_removal a b ((x:Int)-(y:Int)) hab
    ((Z.divide_iff_dvd _ _).2 (dvd_sub_of_mod_eq _ _ _ hma)) ((Z.divide_iff_dvd _ _).2 (dvd_sub_of_mod_eq _ _ _ hmb))
  have heq := eq_of_dvd_sub_bounds (x:Int) (y:Int) (a*b) ⟨by omega,hxr.2⟩ ⟨by omega,hyr.2⟩ ((Z.divide_iff_dvd _ _).1 hd)
  omega

theorem euler_totient_multiplicative__euler_phi_setup_removal (a b : Int) :
    2≤a → 2≤b → rel_prime a b → EulerTotientValue (a*b)=EulerTotientValue a*EulerTotientValue b := by
  intro ha hb hab
  have hg := (Zgcd_1_rel_prime a b).2 hab
  rcases AUXLib.RelPrime.gcd_eq_one_bezout a b hg with ⟨u,v,huv⟩
  have habpos : 0<a*b := Int.mul_pos (by omega) (by omega)
  have hab2 : 2≤a*b := by
    have := Int.mul_le_mul_of_nonneg_left hb (by omega : 0≤a)
    omega
  let f := fun k : Nat => ((Z.modulo (k:Int) a).toNat,(Z.modulo (k:Int) b).toNat)
  let prod := (residues a).flatMap (fun x => (residues b).map (fun y => (x,y)))
  have hmap : ((residues (a*b)).map f).Nodup :=
    nodup_map_on f _ (List.Pairwise.filter _ (List.nodup_range' _)) (by
      intro x hx y hy he
      exact euler_crt_residue_pair_injective__euler_phi_setup_removal a b x y ha hb hab hx hy he)
  have hprod : prod.Nodup := euler_list_prod_nodup__euler_phi_setup_removal Nat Nat _ _
    (List.Pairwise.filter _ (List.nodup_range' _)) (List.Pairwise.filter _ (List.nodup_range' _))
  have hperm := nodup_perm ((residues (a*b)).map f) prod hmap hprod (by
    rintro ⟨x,y⟩
    constructor
    · intro hm
      rcases List.mem_map.mp hm with ⟨k,hk,he⟩
      have hka := euler_residue_mod_member__euler_phi_setup_removal (a*b) a k hab2 ha ⟨b,by grind⟩ hk
      have hkb := euler_residue_mod_member__euler_phi_setup_removal (a*b) b k hab2 hb ⟨a,rfl⟩ hk
      have hx : (Z.modulo (k:Int) a).toNat=x := congrArg Prod.fst he
      have hy : (Z.modulo (k:Int) b).toNat=y := congrArg Prod.snd he
      rw [hx] at hka
      rw [hy] at hkb
      exact List.mem_flatMap.mpr ⟨x,hka,List.mem_map.mpr ⟨y,hkb,rfl⟩⟩
    · intro hpair
      rcases List.mem_flatMap.mp hpair with ⟨x',hx',hmap'⟩
      rcases List.mem_map.mp hmap' with ⟨y',hy',he'⟩
      rcases Prod.mk.inj he' with ⟨hexx,heyy⟩
      subst x'; subst y'
      have hxr := euler_residue_bounds__inverse_final_result a x ha hx'
      have hyr := euler_residue_bounds__inverse_final_result b y hb hy'
      let z := Z.modulo ((x:Int)*(v*b)+(y:Int)*(u*a)) (a*b)
      have hza : Z.modulo z a=(x:Int) := euler_crt_solution_mod_left__euler_phi_setup_removal a b (x:Int) (y:Int) u v ha hb ⟨by omega,hxr.1.2⟩ huv
      have hzb : Z.modulo z b=(y:Int) := euler_crt_solution_mod_right__euler_phi_setup_removal a b (x:Int) (y:Int) u v ha hb ⟨by omega,hyr.1.2⟩ huv
      have hz0 : 0≤z := Int.fmod_nonneg_of_pos _ habpos
      have hzlt : z<a*b := Int.fmod_lt_of_pos _ habpos
      have hzpos : 0<z := by
        by_cases he : z=0
        · rw [he] at hza
          simp only [Z.modulo,Int.zero_fmod] at hza
          omega
        · omega
      have hga : Int.gcd z a=1 := by
        rw [←gcd_fmod z a]
        change Int.gcd (Z.modulo z a) a=1
        rw [hza]
        exact Int.ofNat_inj.mp hxr.2
      have hgb : Int.gcd z b=1 := by
        rw [←gcd_fmod z b]
        change Int.gcd (Z.modulo z b) b=1
        rw [hzb]
        exact Int.ofNat_inj.mp hyr.2
      have hgab : Int.gcd z (a*b)=1 := by rw [Int.gcd_mul_right_right_of_gcd_eq_one hga]; exact hgb
      have hzmem := residue_member (a*b) z hab2 ⟨hzpos,hzlt⟩ (congrArg Int.ofNat hgab)
      apply List.mem_map.mpr
      refine ⟨z.toNat,hzmem,?_⟩
      dsimp only [f]
      have hzcast : (z.toNat : Int)=z := by omega
      rw [hzcast,hza,hzb]
      simp)
  have hlenprod : prod.length=(residues a).length*(residues b).length := by
    dsimp only [prod]
    generalize residues a=la
    induction la with
    | nil => simp
    | cons x la ih => simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons,ih,Nat.add_mul,Nat.one_mul]; omega
  have hlen := hperm.length_eq
  rw [List.length_map,hlenprod] at hlen
  unfold EulerTotientValue
  rw [hlen]
  exact Int.natCast_mul _ _

theorem euler_totient_coprime_prime_power__euler_phi_setup_removal (terminal factor exponent : Int) :
    1≤terminal → prime factor → 1≤exponent → ¬Z.divide factor terminal →
    EulerTotientValue (terminal*Z.pow factor exponent)=EulerTotientValue terminal*(Z.pow factor (exponent-1)*(factor-1)) := by
  intro ht hp he hn
  have hp2 := prime_ge_2 factor hp
  have htail := zpow_pos factor (exponent-1) (by omega) (by omega)
  have hsplit := zpow_split factor exponent he
  by_cases ht1 : terminal=1
  · subst terminal
    have hone : EulerTotientValue 1=1 := rfl
    rw [Int.one_mul,hone,Int.one_mul]
    exact euler_totient_prime_power__euler_phi_setup_removal factor exponent hp he
  · have hpow2 : 2≤Z.pow factor exponent := by
      have hm := Int.mul_le_mul_of_nonneg_left (by omega : 1≤Z.pow factor (exponent-1)) (by omega : 0≤factor)
      omega
    have hg := gcd1_prime factor terminal hp (by intro hd; exact hn ((Z.divide_iff_dvd _ _).2 hd))
    have hrel : rel_prime terminal (Z.pow factor exponent) := by
      apply (Zgcd_1_rel_prime _ _).1
      rw [zpow_nat factor exponent (by omega)]
      exact congrArg Int.ofNat (Int.gcd_pow_right_of_gcd_eq_one (k:=exponent.toNat) hg)
    rw [euler_totient_multiplicative__euler_phi_setup_removal terminal (Z.pow factor exponent) (by omega) hpow2 hrel,
      euler_totient_prime_power__euler_phi_setup_removal factor exponent hp he]

theorem euler_phi_removal_start__euler_phi_setup_removal (original factor current result : Int) :
    2≤original → 1≤current → 1≤result → 2≤factor → Z.modulo current factor=0 →
    EulerPhiProgress original factor current result → EulerPhiRemovalProgress original factor current result := by
  intro ho hc hr hf hm hprogress
  rcases hprogress with ⟨⟨hcr,hsem⟩,hbelow⟩
  have hfc : Z.divide factor current := (Z.divide_iff_dvd _ _).2 (Int.dvd_of_fmod_eq_zero hm)
  have hp := euler_factor_prime__euler_phi_setup_removal factor current hf hfc hbelow
  have hfr : Z.divide factor result := (Z.divide_iff_dvd _ _).2
    (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hfc) ((Z.divide_iff_dvd _ _).1 hcr))
  refine ⟨current,0,by omega,by simp [Z.pow],hfc,hfr,⟨⟨hcr,hsem⟩,hbelow⟩,?_⟩
  intro terminal removed hremoved hdec hfree
  have he : 1≤removed := by
    by_cases he0 : removed=0
    · subst removed
      simp only [Z.pow,Int.pow_zero,Int.mul_one] at hdec
      rw [←hdec] at hfree
      exact False.elim (hfree hm)
    · omega
  have htail := zpow_pos factor (removed-1) (by omega) (by omega)
  have hpower := zpow_pos factor removed (by omega) (by omega)
  have hsplit := zpow_split factor removed he
  have htpos : 0<terminal := Int.pos_of_mul_pos_left (by omega : 0<terminal*Z.pow factor removed) hpower
  have hn : ¬Z.divide factor terminal := by intro hd; exact hfree (Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 hd))
  have htot : EulerTotientValue current=EulerTotientValue terminal*(Z.pow factor (removed-1)*(factor-1)) := by
    rw [hdec]
    exact euler_totient_coprime_prime_power__euler_phi_setup_removal terminal factor removed (by omega) hp he hn
  rcases hcr with ⟨q,hq⟩
  have hquot : Z.div result factor=terminal*Z.pow factor (removed-1)*q := by
    have hrex : result=(terminal*Z.pow factor (removed-1)*q)*factor := by grind
    rw [hrex]
    exact Int.mul_fdiv_cancel _ (by omega)
  refine ⟨⟨Z.pow factor (removed-1)*q*(factor-1),by rw [hquot]; grind⟩,?_⟩
  intro origphi termphi hophi htphi
  have hs := hsem origphi (EulerTotientValue current) hophi rfl
  have hcancel : origphi=q*EulerTotientValue current := by
    apply Int.eq_of_mul_eq_mul_right (a:=current) (by omega)
    grind
  rw [hcancel,htot,hquot,htphi]
  grind

theorem euler_prime_two__euler_phi_factor_completion : EulerPrime 2 := by
  refine ⟨by omega,?_⟩
  intro d hd hdiv
  have := Int.le_of_dvd (by omega : (0:Int)<2) ((Z.divide_iff_dvd _ _).1 hdiv)
  omega

theorem euler_exact_positive_quotient_bounds__euler_phi_factor_completion (result factor : Int) :
    1≤result → 2≤factor → Z.divide factor result →
    1≤Z.quot result factor ∧ 0≤Z.quot result factor*(factor-1) ∧ Z.quot result factor*(factor-1)≤result := by
  rintro hr hf ⟨q,hq⟩
  have hqpos : 0<q := Int.pos_of_mul_pos_left (by omega : 0<q*factor) (by omega)
  rw [hq,Z.quot_mul q factor (by omega)]
  have hnonneg := Int.mul_nonneg (by omega : 0≤q) (by omega : 0≤factor-1)
  have hmul := Int.mul_le_mul_of_nonneg_left (by omega : factor-1≤factor) (by omega : 0≤q)
  exact ⟨by omega,hnonneg,hmul⟩

theorem euler_progress_advance_nondivisor__euler_phi_factor_completion (original factor remaining result : Int) :
    2≤factor → Z.rem remaining factor≠0 → EulerPhiProgress original factor remaining result →
    EulerPhiProgress original (factor+1) remaining result := by
  rintro hf hr ⟨hres,hbelow⟩
  refine ⟨hres,?_⟩
  intro p hp hlt hd
  by_cases hpf : p<factor
  · exact hbelow p hp hpf hd
  · have he : p=factor := by omega
    subst p
    exact hr ((Z.rem_divide remaining factor (by omega)).2 hd)

theorem euler_completed_progress__euler_phi_factor_completion (original factor current result : Int) :
    1≤current → 1≤result → 2≤factor → Z.rem current factor≠0 → EulerPhiRemovalProgress original factor current result →
    EulerPhiProgress original (factor+1) current (Z.quot result factor*(factor-1)) := by
  intro hc hr hf hrem hremoval
  have hmod : Z.modulo current factor≠0 := by
    rw [show Z.modulo current factor=Z.rem current factor from Int.fmod_eq_tmod_of_nonneg (by omega) (by omega)]
    exact hrem
  have hres := EulerPhiRemovalProgress_complete original factor current result hremoval hmod
  rw [show Z.div result factor=Z.quot result factor from Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)] at hres
  refine ⟨hres,?_⟩
  rcases hremoval with ⟨before,removed,hremoved,hbefore,_,_,⟨_,hbelow⟩,_⟩
  intro p hp hlt hd
  by_cases hpf : p<factor
  · apply hbelow p hp hpf
    rcases hd with ⟨q,hq⟩
    exact ⟨q*Z.pow factor removed,by grind⟩
  · have he : p=factor := by omega
    subst p
    exact hrem ((Z.rem_divide current factor (by omega)).2 hd)

theorem euler_active_frontier_bound__euler_phi_factor_completion (original factor current result : Int) :
    2≤factor → factor≤216 → EulerPhiRemovalProgress original factor current result → factor+1≤216 := by
  rintro hf hb ⟨before,removed,_,_,hd,_,⟨_,hbelow⟩,_⟩
  by_cases he : factor=216
  · subst factor
    apply False.elim
    apply hbelow 2 euler_prime_two__euler_phi_factor_completion (by omega)
    rcases hd with ⟨q,hq⟩
    exact ⟨108*q,by grind⟩
  · omega

theorem euler_prime_to_prime__euler_phi_final_results (p : Int) : EulerPrime p → prime p := by
  rintro ⟨hp,hdiv⟩
  apply (prime_alt p).1
  refine ⟨hp,?_⟩
  intro d hd hv
  rcases hdiv d (by omega) hv with h | h <;> omega

theorem euler_remaining_prime__euler_phi_final_results (frontier remaining : Int) :
    1<remaining → 2≤frontier → frontier*frontier>remaining → NoPrimeDivisorBelow frontier remaining → EulerPrime remaining := by
  intro hr hf hsq hbelow
  apply euler_prime_from_prime__euler_phi_final_results
  apply (AUXLib.Prime.prime_alt remaining).1
  apply SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib.prime_of_no_factor_before_square remaining frontier (by omega) hf hsq
  rintro ⟨d,hdlo,hdhi,hdiv⟩
  rcases euler_prime_divisor_exists__euler_phi_final_results d (by omega) with ⟨q,hq,hqd⟩
  have hqle := Int.le_of_dvd (by omega : 0<d) ((Z.divide_iff_dvd _ _).1 hqd)
  exact hbelow q (euler_prime_from_prime__euler_phi_final_results q hq) (by omega)
    ((Z.divide_iff_dvd _ _).2 (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hqd) ((Z.divide_iff_dvd _ _).1 hdiv)))

theorem euler_filter_all_true__euler_phi_final_results (A : Type) (f : A → Bool) (l : List A) :
    (∀ x, x∈l → f x=true) → l.filter f=l := by
  exact List.filter_eq_self.mpr

theorem euler_totient_of_prime__euler_phi_final_results (p : Int) : prime p → EulerTotientValue p=p-1 := by
  intro hp
  have h := euler_totient_prime_power__euler_phi_setup_removal p 1 hp (by omega)
  simpa [Z.pow,Int.pow_succ] using h

theorem euler_progress_terminal_prime__euler_phi_final_results (original frontier remaining result : Int) :
    1<remaining → 2≤frontier → frontier*frontier>remaining → EulerPhiProgress original frontier remaining result →
    EulerPhi original (Z.quot result remaining*(remaining-1)) := by
  rintro hr hf hsq ⟨⟨hd,hsem⟩,hbelow⟩
  have hep := euler_remaining_prime__euler_phi_final_results frontier remaining hr hf hsq hbelow
  have hp := euler_prime_to_prime__euler_phi_final_results remaining hep
  have hphi := euler_totient_of_prime__euler_phi_final_results remaining hp
  have hs := hsem (EulerTotientValue original) (remaining-1) rfl hphi.symm
  rcases hd with ⟨q,hq⟩
  unfold EulerPhi
  rw [hq,Z.quot_mul q remaining (by omega)]
  apply Int.eq_of_mul_eq_mul_right (a:=remaining) (by omega)
  grind

theorem euler_progress_terminal_one__euler_phi_final_results (original frontier remaining result : Int) :
    remaining=1 → EulerPhiProgress original frontier remaining result → EulerPhi original result := by
  rintro rfl ⟨⟨hd,hsem⟩,_⟩
  have h := hsem (EulerTotientValue original) 1 rfl rfl
  simpa [EulerPhi] using h.symm

theorem euler_modular_progress_odd_step__modular_power_loop (original_base original_exponent modulus base exponent accumulator : Int) :
    0<modulus → 0<exponent → Z.modulo exponent 2=1 →
    EulerModularPowerProgress original_base original_exponent modulus base exponent accumulator →
    EulerModularPowerProgress original_base original_exponent modulus (Z.modulo (base*base) modulus) (Z.div exponent 2) (Z.modulo (accumulator*base) modulus) := by
  intro hm he hodd hp
  exact SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.modular_power_progress_odd_step__loop_transitions _ _ _ _ _ _ hm (by omega) hodd hp

theorem euler_modular_progress_even_step__modular_power_loop (original_base original_exponent modulus base exponent accumulator : Int) :
    0<modulus → 0<exponent → Z.modulo exponent 2≠1 →
    EulerModularPowerProgress original_base original_exponent modulus base exponent accumulator →
    EulerModularPowerProgress original_base original_exponent modulus (Z.modulo (base*base) modulus) (Z.div exponent 2) accumulator := by
  intro hm he hn hp
  have hb := Int.fmod_nonneg_of_pos exponent (by omega : (0:Int)<2)
  have ht := Int.fmod_lt_of_pos exponent (by omega : (0:Int)<2)
  have hz : Z.modulo exponent 2=0 := by unfold Z.modulo at *; omega
  exact SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.modular_power_progress_even_step__loop_transitions _ _ _ _ _ _ hm (by omega) hz hp

theorem bounded_residue_product_int__modular_power_loop (modulus x y : Int) :
    2≤modulus → modulus≤46341 → 0≤x → x<modulus → 0≤y → y<modulus → 0≤x*y ∧ x*y≤2147483647 := by
  intro hm hmax hx hxm hy hym
  exact AUXLib.bounded_product x y modulus hmax ⟨hx,hxm⟩ ⟨hy,hym⟩

theorem euler_modular_progress_zero_finish__modular_power_final (original_base original_exponent modulus current_base accumulator : Int) :
    0≤accumulator → accumulator<modulus → EulerModularPowerProgress original_base original_exponent modulus current_base 0 accumulator →
    ModularPower original_base original_exponent modulus accumulator := by
  intro ha ham hp
  unfold EulerModularPowerProgress at hp
  simp only [Z.pow,Int.pow_zero,Int.mul_one] at hp
  change accumulator=Z.modulo (Z.pow original_base original_exponent) modulus
  rw [show Z.modulo accumulator modulus=accumulator from Int.fmod_eq_of_lt ha ham] at hp
  exact hp

theorem euler_coprime_residue_member__inverse_final_result (n x : Int) :
    2≤n → (0<x ∧ x<n) → Z.gcd x n=1 → x.toNat ∈ residues n := by
  exact residue_member n x

theorem euler_residue_map_member__inverse_final_result (n a : Int) (k : Nat) :
    2≤n → Z.gcd a n=1 → k ∈ residues n → (Z.modulo (a*(k:Int)) n).toNat ∈ residues n := by
  intro hn ha hk
  have hgk := (euler_residue_bounds__inverse_final_result n k hn hk).2
  have hga : Int.gcd a n=1 := Int.ofNat_inj.mp ha
  have hg : Int.gcd (a*(k:Int)) n=1 := by
    rw [Int.gcd_mul_right_left_of_gcd_eq_one hga]
    exact Int.ofNat_inj.mp hgk
  have hz := gcd1_mod_nonzero (a*(k:Int)) n hn hg
  have hlo := Int.fmod_nonneg_of_pos (a*(k:Int)) (by omega : 0<n)
  have hhi := Int.fmod_lt_of_pos (a*(k:Int)) (by omega : 0<n)
  apply residue_member n _ hn ⟨by omega,hhi⟩
  change Int.ofNat (Int.gcd ((a*(k:Int)).fmod n) n)=1
  rw [gcd_fmod,hg]
  rfl

theorem euler_residue_map_injective__inverse_final_result (n a : Int) (x y : Nat) :
    2≤n → Z.gcd a n=1 → x ∈ residues n → y ∈ residues n →
    (Z.modulo (a*(x:Int)) n).toNat=(Z.modulo (a*(y:Int)) n).toNat → x=y := by
  intro hn ha hx hy he
  have hxr := (euler_residue_bounds__inverse_final_result n x hn hx).1
  have hyr := (euler_residue_bounds__inverse_final_result n y hn hy).1
  have hma : (a*(x:Int)).fmod n=(a*(y:Int)).fmod n := by
    have := Int.fmod_nonneg_of_pos (a*(x:Int)) (by omega : 0<n)
    have := Int.fmod_nonneg_of_pos (a*(y:Int)) (by omega : 0<n)
    change ((a*(x:Int)).fmod n).toNat=((a*(y:Int)).fmod n).toNat at he
    omega
  have hd := dvd_sub_of_mod_eq _ _ _ hma
  have hm : n∣a*((x:Int)-(y:Int)) := by
    have heq : a*((x:Int)-(y:Int))=a*(x:Int)-a*(y:Int) := by grind
    rw [heq]
    exact hd
  have hg : Int.gcd n a=1 := by rw [Int.gcd_comm]; exact Int.ofNat_inj.mp ha
  have hdiv := coprime_cancel_dvd n a _ hg hm
  have heq := eq_of_dvd_sub_bounds (x:Int) (y:Int) n ⟨by omega,hxr.2⟩ ⟨by omega,hyr.2⟩ hdiv
  omega

theorem euler_residue_map_nodup__inverse_final_result (n a : Int) :
    2≤n → Z.gcd a n=1 → ((residues n).map (fun k : Nat => (Z.modulo (a*(k:Int)) n).toNat)).Nodup := by
  intro hn ha
  apply nodup_map_on _ _ (List.Pairwise.filter _ (List.nodup_range' _))
  intro x hx y hy he
  exact euler_residue_map_injective__inverse_final_result n a x y hn ha hx hy he

theorem euler_residue_map_permutation__inverse_final_result (n a : Int) :
    2≤n → Z.gcd a n=1 →
    ((residues n).map (fun k : Nat => (Z.modulo (a*(k:Int)) n).toNat)).Perm (residues n) := by
  intro hn ha
  apply perm_of_nodup_subset_length _ _ (euler_residue_map_nodup__inverse_final_result n a hn ha) (List.length_map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨k,hk,hkx⟩
  subst x
  exact euler_residue_map_member__inverse_final_result n a k hn ha hk

theorem euler_product_permutation__inverse_final_result (l1 l2 : List Nat) :
    l1.Perm l2 → l1.foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1=l2.foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1 := by
  intro hp
  induction hp with
  | nil => rfl
  | cons a h ih => simp only [List.foldr_cons]; rw [ih]
  | swap a b l => simp only [List.foldr_cons]; grind
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem euler_mapped_product_mod__inverse_final_result (n a : Int) (l : List Nat) :
    0<n → Z.modulo (((l.map (fun k : Nat => (Z.modulo (a*(k:Int)) n).toNat)).foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1)) n =
    Z.modulo (Z.pow a (Int.ofNat l.length)*l.foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1) n := by
  intro hn
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons,List.foldr_cons,List.length_cons]
    have hk : (((Z.modulo (a*(k:Int)) n).toNat : Nat) : Int)=Z.modulo (a*(k:Int)) n := by
      have := Int.fmod_nonneg_of_pos (a*(k:Int)) hn
      change ↑((a*↑k).fmod n).toNat=(a*↑k).fmod n
      omega
    rw [hk]
    change ((a*(k:Int)).fmod n * _).fmod n=(a^(l.length+1)*((k:Int)*_)).fmod n
    rw [Int.mul_fmod,Int.fmod_fmod]
    change _=((a^l.length*a)*((k:Int)*_)).fmod n
    simp only [Z.modulo,Z.pow] at ih
    simp only [Z.modulo]
    rw [ih,←Int.mul_fmod]
    congr 1
    grind

theorem euler_residue_product_coprime__inverse_final_result (n : Int) (l : List Nat) :
    (∀ k, k∈l → Z.gcd (k:Int) n=1) → rel_prime (l.foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1) n := by
  intro hall
  apply (Zgcd_1_rel_prime _ n).1
  have hnat : Int.gcd (l.foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1) n=1 := by
    induction l with
    | nil => exact Int.one_gcd
    | cons k l ih =>
      have hk : Int.gcd (k:Int) n=1 := Int.ofNat_inj.mp (hall k (by simp))
      simp only [List.foldr_cons,Int.gcd_mul_right_left_of_gcd_eq_one hk]
      exact ih (by intro j hj; exact hall j (by simp [hj]))
  exact congrArg Int.ofNat hnat

theorem euler_power_totient_mod__inverse_final_result (a n : Int) :
    0<a → a<n → 2≤n → Z.gcd a n=1 → Z.modulo (Z.pow a (EulerTotientValue n)) n=1 := by
  intro ha han hn hag
  let l := residues n
  let prod := l.foldr (fun (k : Nat) (acc : Int) => (k:Int)*acc) 1
  have hp := euler_residue_map_permutation__inverse_final_result n a hn hag
  have hprod := euler_product_permutation__inverse_final_result _ _ hp
  have hmod := euler_mapped_product_mod__inverse_final_result n a l (by omega)
  rw [hprod] at hmod
  have hdiv : n∣prod*(Z.pow a (Int.ofNat l.length)-1) := by
    have hd := dvd_sub_of_mod_eq _ _ n hmod.symm
    have heq : prod*(Z.pow a (Int.ofNat l.length)-1)=Z.pow a (Int.ofNat l.length)*prod-prod := by grind
    rw [heq]
    exact hd
  have hrel := euler_residue_product_coprime__inverse_final_result n l (by
    intro k hk
    exact (euler_residue_bounds__inverse_final_result n k hn hk).2)
  have hg : Int.gcd n prod=1 := by
    rw [Int.gcd_comm]
    exact Int.ofNat_inj.mp ((Zgcd_1_rel_prime prod n).2 hrel)
  have hc := coprime_cancel_dvd n prod _ hg hdiv
  have he := mod_eq_of_dvd_sub (Z.pow a (Int.ofNat l.length)) 1 n hc
  rw [Int.fmod_eq_of_lt (by omega : (0:Int)≤1) (by omega : (1:Int)<n)] at he
  exact he

theorem euler_totient_inverse_theorem__inverse_final_result (a n phi inverse : Int) :
    0<a → a<n → 2≤n → Z.gcd a n=1 → EulerPhi n phi → ModularPower a (phi-1) n inverse →
    Z.modulo (a*inverse) n=1 ∧ EulerTheoremInverse a n inverse := by
  intro ha han hn hag hphi hpower
  have hmember := euler_coprime_residue_member__inverse_final_result n a hn ⟨ha,han⟩ hag
  have hlenpos : 0<(residues n).length := List.length_pos_of_mem hmember
  have hphi1 : 1≤phi := by unfold EulerPhi EulerTotientValue at hphi; simp only [Int.ofNat_eq_coe] at hphi; omega
  have hi : Z.modulo (a*inverse) n=1 := by
    unfold ModularPower at hpower
    rw [hpower]
    change (a*(Z.pow a (phi-1)).fmod n).fmod n=1
    rw [Int.mul_fmod,Int.fmod_fmod,←Int.mul_fmod]
    rw [←zpow_split a phi hphi1,hphi]
    exact euler_power_totient_mod__inverse_final_result a n ha han hn hag
  exact ⟨hi,⟨phi,hphi,hpower,hi⟩⟩

end SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib
namespace SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse
export euler_theorem_inverse_lib (EulerTotientValue EulerPhi EulerTheoremInverse EulerPhiResidual EulerPrime NoPrimeDivisorBelow EulerPhiProgress EulerPhiFactorCompletion EulerPhiRemovalProgress EulerModularPowerProgress ModularPower)
end SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse
