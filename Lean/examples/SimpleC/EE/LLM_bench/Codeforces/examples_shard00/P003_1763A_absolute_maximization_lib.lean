import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import SetsClass.RelsDomain

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib
open AUXLib


open MaxMinLib

def SameBitsExcept (x y b : Int) : Prop :=
  ∀ k, 0 ≤ k → k ≠ b → Z.testbit x k = Z.testbit y k

def OneBitSwap (n : Int) (before after : List Int) : Prop :=
  ∃ i j b xi xj yi yj,
    (0 ≤ i ∧ i < n) ∧ (0 ≤ j ∧ j < n) ∧ 0 ≤ b ∧
    xi = Znth i before 0 ∧ xj = Znth j before 0 ∧
    yi = Znth i after 0 ∧ yj = Znth j after 0 ∧
    Zlength after = Zlength before ∧
    (∀ k, (0 ≤ k ∧ k < n) → k ≠ i → k ≠ j → Znth k after 0 = Znth k before 0) ∧
    SameBitsExcept xi yi b ∧ SameBitsExcept xj yj b ∧
    Z.testbit yi b = Z.testbit xj b ∧ Z.testbit yj b = Z.testbit xi b

def ReachableByBitSwaps (n : Int) (a out : List Int) : Prop :=
  clos_refl_trans (OneBitSwap n) a out

def ArraySpread (a : List Int) (d : Int) : Prop :=
  max_value_of_subset (· ≤ ·) (fun endpoints : Int × Int => endpoints.1 ∈ a ∧ endpoints.2 ∈ a)
    (fun endpoints => endpoints.2 - endpoints.1) d

def Pre (a : List Int) : Prop :=
  (3 ≤ Zlength a ∧ Zlength a ≤ 512) ∧ Forall (fun x => 0 ≤ x ∧ x < 1024) a

def Spec (a : List Int) (out : Int) : Prop :=
  max_value_of_subset (· ≤ ·)
    (fun candidate : List Int × Int => ReachableByBitSwaps (Zlength a) a candidate.1 ∧ ArraySpread candidate.1 candidate.2)
    Prod.snd out

def BitwiseScanState (a : List Int) (i acc_or acc_and : Int) : Prop :=
  (0 ≤ i ∧ i ≤ Zlength a) ∧
  (∀ b, 0 ≤ b → (Z.testbit acc_or b = true ↔ ∃ j, (0 ≤ j ∧ j < i) ∧ Z.testbit (Znth j a 0) b = true)) ∧
  (∀ b, 0 ≤ b → (Z.testbit acc_and b = true ↔ ∀ j, (0 ≤ j ∧ j < max 1 i) → Z.testbit (Znth j a 0) b = true))


set_option maxHeartbeats 2000000

-- Coq setbit/clearbit use the single-bit mask 2^b. Coq integer powers give
-- zero at negative b, preserving the no-op behavior there as well.
def Z.setbit (x b : Int) : Int := _root_.Z.lor x (_root_.Z.pow 2 b)
def Z.clearbit (x b : Int) : Int := _root_.Z.ldiff x (_root_.Z.pow 2 b)

private theorem mask_bit (b k : Int) (hb : 0≤b) :
    Z.testbit (Z.pow 2 b) k=decide (b=k) := by
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb
  cases k with
  | ofNat k =>
    have hp : (2 : Int)^b=Int.ofNat (2^b) := (Int.natCast_pow 2 b).symm
    change Z.testbit ((2 : Int)^b) (Int.ofNat k)=decide (Int.ofNat b=Int.ofNat k)
    rw [hp]
    simp [Z.testbit,Nat.testBit_two_pow]
  | negSucc k => simp [Z.testbit]

theorem bitwise_scan_state_zero__scan_core (a : List Int) (ha : 1≤Zlength a) :
    BitwiseScanState a 0 0 (Znth 0 a 0) := by
  refine ⟨by omega,?_,?_⟩
  · intro b hb
    have hz : Z.testbit 0 b=false := by cases b <;> simp [Z.testbit]
    rw [hz]
    constructor
    · intro h;cases h
    · rintro ⟨j,hj,_⟩;omega
  · intro b hb
    constructor
    · intro h j hj
      have he : j=0 := by change 0≤j ∧ j<1 at hj;omega
      simpa only [he] using h
    · intro h;exact h 0 (by decide)

theorem bitwise_scan_state_succ__scan_core (a : List Int) (i acc_or acc_and : Int)
    (hi : 0≤i ∧ i<Zlength a) (hs : BitwiseScanState a i acc_or acc_and) :
    BitwiseScanState a (i+1) (Z.lor acc_or (Znth i a 0)) (Z.land acc_and (Znth i a 0)) := by
  obtain ⟨hbound,hor,hand⟩ := hs
  refine ⟨by omega,?_,?_⟩
  · intro b hb
    rw [Z.lor_spec,Bool.or_eq_true,hor b hb]
    constructor
    · rintro (⟨j,hj,hbit⟩ | hbit)
      · exact ⟨j,by omega,hbit⟩
      · exact ⟨i,by omega,hbit⟩
    · rintro ⟨j,hj,hbit⟩
      by_cases he : j=i
      · exact Or.inr (he ▸ hbit)
      · exact Or.inl ⟨j,by omega,hbit⟩
  · intro b hb
    rw [Z.land_spec,Bool.and_eq_true,hand b hb]
    constructor
    · rintro ⟨hold,hbit⟩ j hj
      by_cases he : j=i
      · exact he ▸ hbit
      · apply hold j;omega
    · intro hall
      exact ⟨fun j hj => hall j (by omega),hall i (by omega)⟩

theorem bounded_mask_1024__scan_core (x : Int) (hx : 0≤x ∧ x<1024) : Z.land x 1023=x := by
  change Z.land x (Z.ones 10)=x
  rw [Z.land_ones x 10 (by omega)]
  change Int.fmod x 1024=x
  exact Int.fmod_eq_of_lt hx.1 hx.2

theorem bounded_lor_land__scan_core (x y : Int) (hx : 0≤x ∧ x<1024) (hy : 0≤y ∧ y<1024) :
    (0≤Z.lor x y ∧ Z.lor x y<1024) ∧ (0≤Z.land x y ∧ Z.land x y<1024) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hxn : x<2^10 := by omega
  have hyn : y<2^10 := by omega
  have ho := Nat.or_lt_two_pow hxn hyn
  have ha := Nat.and_lt_two_pow x hyn
  change (0≤Int.ofNat (x ||| y) ∧ Int.ofNat (x ||| y)<1024) ∧ (0≤Int.ofNat (x &&& y) ∧ Int.ofNat (x &&& y)<1024)
  simp only [Int.ofNat_eq_coe] at *
  omega

theorem bit_write_same__final_result (x b : Int) (v : Bool) (hb : 0≤b) :
    Z.testbit (if v then Z.setbit x b else Z.clearbit x b) b=v := by
  cases v <;> simp [Z.setbit,Z.clearbit,Z.lor_spec,Z.ldiff_spec,mask_bit b b hb]

theorem bit_write_other__final_result (x b : Int) (v : Bool) (k : Int) (hb : 0≤b) (hne : k≠b) :
    Z.testbit (if v then Z.setbit x b else Z.clearbit x b) k=Z.testbit x k := by
  have he : b≠k := Ne.symm hne
  cases v <;> simp [Z.setbit,Z.clearbit,Z.lor_spec,Z.ldiff_spec,mask_bit b k hb,he]

theorem Zlength_replace_Znth__final_result {A : Type} (l : List A) (n : Int) (v : A) :
    Zlength (replace_Znth n v l)=Zlength l := Zlength_replace_Znth l n v


private theorem update_pair (l : List Int) (i j vi vj : Int)
    (hi : 0≤i ∧ i<Zlength l) (hj : 0≤j ∧ j<Zlength l) (hne : i≠j) :
    Znth i (replace_Znth j vj (replace_Znth i vi l)) 0=vi ∧
    Znth j (replace_Znth j vj (replace_Znth i vi l)) 0=vj ∧
    (∀ k, 0≤k ∧ k<Zlength l → k≠i → k≠j →
      Znth k (replace_Znth j vj (replace_Znth i vi l)) 0=Znth k l 0) := by
  have hli : Zlength (replace_Znth i vi l)=Zlength l := Zlength_replace_Znth l i vi
  refine ⟨?_,?_,?_⟩
  · rw [Znth_replace_Znth_Diff 0 _ j i vj (by omega) (by omega) (Ne.symm hne),Znth_replace_Znth_Same 0 _ i vi hi]
  · exact Znth_replace_Znth_Same 0 _ j vj (by omega)
  · intro k hk hki hkj
    rw [Znth_replace_Znth_Diff 0 _ j k vj (by omega) (by omega) (Ne.symm hkj),Znth_replace_Znth_Diff 0 l i k vi hi hk (Ne.symm hki)]

theorem one_bit_swap_construct__final_result (n : Int) (l : List Int) (i j b : Int)
    (hlen : Zlength l=n) (hi : 0≤i ∧ i<n) (hj : 0≤j ∧ j<n) (hne : i≠j) (hb : 0≤b) :
    let xi := Znth i l 0
    let xj := Znth j l 0
    let yi := if Z.testbit xj b then Z.setbit xi b else Z.clearbit xi b
    let yj := if Z.testbit xi b then Z.setbit xj b else Z.clearbit xj b
    OneBitSwap n l (replace_Znth j yj (replace_Znth i yi l)) := by
  dsimp only
  let xi := Znth i l 0
  let xj := Znth j l 0
  let yi := if Z.testbit xj b then Z.setbit xi b else Z.clearbit xi b
  let yj := if Z.testbit xi b then Z.setbit xj b else Z.clearbit xj b
  have hpos := update_pair l i j yi yj (by omega) (by omega) hne
  refine ⟨i,j,b,xi,xj,yi,yj,hi,hj,hb,rfl,rfl,hpos.1.symm,hpos.2.1.symm,?_,?_,?_,?_,?_,?_⟩
  · simp only [Zlength_replace_Znth]
  · intro k hk hki hkj;exact hpos.2.2 k (by omega) hki hkj
  · intro k hk hkb;exact (bit_write_other__final_result xi b (Z.testbit xj b) k hb hkb).symm
  · intro k hk hkb;exact (bit_write_other__final_result xj b (Z.testbit xi b) k hb hkb).symm
  · exact bit_write_same__final_result xi b (Z.testbit xj b) hb
  · exact bit_write_same__final_result xj b (Z.testbit xi b) hb

private theorem swap_symm (n : Int) (before after : List Int) (hs : OneBitSwap n before after) :
    OneBitSwap n after before := by
  obtain ⟨i,j,b,xi,xj,yi,yj,hi,hj,hb,hxi,hxj,hyi,hyj,hlen,hother,hsi,hsj,hbi,hbj⟩ := hs
  refine ⟨i,j,b,yi,yj,xi,xj,hi,hj,hb,hyi,hyj,hxi,hxj,hlen.symm,?_,?_,?_,hbj.symm,hbi.symm⟩
  · intro k hk hki hkj;exact (hother k hk hki hkj).symm
  · intro k hk hkb;exact (hsi k hk hkb).symm
  · intro k hk hkb;exact (hsj k hk hkb).symm

private theorem swap_occurs (n : Int) (before after : List Int) (hs : OneBitSwap n before after)
    (hl : Zlength before=n) (b : Int) (hb : 0≤b) (v : Bool)
    (h : ∃ k, (0≤k ∧ k<Zlength before) ∧ Z.testbit (Znth k before 0) b=v) :
    ∃ k, (0≤k ∧ k<Zlength after) ∧ Z.testbit (Znth k after 0) b=v := by
  obtain ⟨i,j,sb,xi,xj,yi,yj,hi,hj,hsb,hxi,hxj,hyi,hyj,hlen,hother,hsi,hsj,hbi,hbj⟩ := hs
  obtain ⟨k,hk,hv⟩ := h
  by_cases he : b=sb
  · rw [he] at hv ⊢
    by_cases hki : k=i
    · refine ⟨j,by omega,?_⟩
      rw [← hyj,hbj,hxi,← hki];exact hv
    · by_cases hkj : k=j
      · refine ⟨i,by omega,?_⟩
        rw [← hyi,hbi,hxj,← hkj];exact hv
      · refine ⟨k,by omega,?_⟩
        rw [hother k (by omega) hki hkj];exact hv
  · refine ⟨k,by omega,?_⟩
    by_cases hki : k=i
    · rw [hki,← hyi,← hsi b hb he,hxi,← hki];exact hv
    · by_cases hkj : k=j
      · rw [hkj,← hyj,← hsj b hb he,hxj,← hkj];exact hv
      · rw [hother k (by omega) hki hkj];exact hv

theorem one_bit_swap_occurs_iff__final_result (n : Int) (before after : List Int)
    (hs : OneBitSwap n before after) (hl : Zlength before=n) :
    Zlength after=Zlength before ∧ ∀ b, 0≤b → ∀ v,
      (∃ k, (0≤k ∧ k<Zlength before) ∧ Z.testbit (Znth k before 0) b=v) ↔
      (∃ k, (0≤k ∧ k<Zlength after) ∧ Z.testbit (Znth k after 0) b=v) := by
  have hlen : Zlength after=Zlength before := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hlen,_⟩ := hs
    exact hlen
  refine ⟨hlen,?_⟩
  intro b hb v
  exact ⟨swap_occurs n before after hs hl b hb v,
    swap_occurs n after before (swap_symm n before after hs) (by omega) b hb v⟩

theorem reachable_preserves_bit_counts__final_result (n : Int) (a out : List Int)
    (hl : Zlength a=n) (hr : ReachableByBitSwaps n a out) :
    Zlength out=Zlength a ∧ ∀ b, 0≤b → ∀ v,
      (∃ k, (0≤k ∧ k<Zlength a) ∧ Z.testbit (Znth k a 0) b=v) ↔
      (∃ k, (0≤k ∧ k<Zlength out) ∧ Z.testbit (Znth k out 0) b=v) := by
  induction hr using clos_refl_trans_induction_1n with
  | hrefl a => exact ⟨rfl,fun _ _ _ => Iff.rfl⟩
  | hstep a mid out hs hr ih =>
    have hstep := one_bit_swap_occurs_iff__final_result n a mid hs hl
    have ht := ih (by omega)
    refine ⟨by omega,?_⟩
    intro b hb v
    exact (hstep.2 b hb v).trans (ht.2 b hb v)

theorem one_swap_reachable__final_result (n : Int) (a b : List Int) (hs : OneBitSwap n a b) :
    ReachableByBitSwaps n a b := ⟨1,b,hs,rfl⟩

theorem force_bit_once__final_result (n : Int) (l : List Int) (t s b : Int)
    (hlen : Zlength l=n) (ht : 0≤t ∧ t<n) (hs : 0≤s ∧ s<n) (hne : t≠s) (hb : 0≤b) :
    ∃ out, ReachableByBitSwaps n l out ∧ Zlength out=n ∧
      Z.testbit (Znth t out 0) b=Z.testbit (Znth s l 0) b ∧
      (∀ k q, (0≤k ∧ k<n) → 0≤q → q≠b → Z.testbit (Znth k out 0) q=Z.testbit (Znth k l 0) q) ∧
      (∀ k, (0≤k ∧ k<n) → k≠t → k≠s → Znth k out 0=Znth k l 0) := by
  let xt := Znth t l 0
  let xs := Znth s l 0
  let yt := if Z.testbit xs b then Z.setbit xt b else Z.clearbit xt b
  let ys := if Z.testbit xt b then Z.setbit xs b else Z.clearbit xs b
  let out := replace_Znth s ys (replace_Znth t yt l)
  have hswap : OneBitSwap n l out := one_bit_swap_construct__final_result n l t s b hlen ht hs hne hb
  have hp := update_pair l t s yt ys (by omega) (by omega) hne
  refine ⟨out,one_swap_reachable__final_result n l out hswap,?_,?_,?_,?_⟩
  · simp only [out,Zlength_replace_Znth];exact hlen
  · change Z.testbit (Znth t (replace_Znth s ys (replace_Znth t yt l)) 0) b=Z.testbit xs b
    rw [hp.1];exact bit_write_same__final_result xt b (Z.testbit xs b) hb
  · intro k q hk hq hqb
    change Z.testbit (Znth k (replace_Znth s ys (replace_Znth t yt l)) 0) q=_
    by_cases hkt : k=t
    · rw [hkt,hp.1];exact bit_write_other__final_result xt b (Z.testbit xs b) q hb hqb
    · by_cases hks : k=s
      · rw [hks,hp.2.1];exact bit_write_other__final_result xs b (Z.testbit xt b) q hb hqb
      · rw [hp.2.2 k (by omega) hkt hks]
  · intro k hk hkt hks;exact hp.2.2 k (by omega) hkt hks


private theorem reach_refl (n : Int) (l : List Int) : ReachableByBitSwaps n l l := ⟨0,rfl⟩
private theorem reach_trans (n : Int) (a b c : List Int)
    (hab : ReachableByBitSwaps n a b) (hbc : ReachableByBitSwaps n b c) : ReachableByBitSwaps n a c := by
  obtain ⟨k,hk⟩ := hab
  obtain ⟨m,hm⟩ := hbc
  exact ⟨k+m,nsteps_rel_add (List Int) (OneBitSwap n) k m hk hm⟩

theorem canonical_extrema_prefix__final_result (m : Nat) (n : Int) (a : List Int) (all_or all_and : Int)
    (hm : m≤10) (hlen : Zlength a=n) (hn : 3≤n) (hscan : BitwiseScanState a n all_or all_and) :
    ∃ out, ReachableByBitSwaps n a out ∧ Zlength out=n ∧
      (∀ b, (0≤b ∧ b<Int.ofNat m) →
        Z.testbit (Znth 0 out 0) b=Z.testbit all_or b ∧ Z.testbit (Znth 1 out 0) b=Z.testbit all_and b) := by
  classical
  induction m with
  | zero => exact ⟨a,reach_refl n a,hlen,fun b hb => by change 0≤b ∧ b<0 at hb;omega⟩
  | succ m ih =>
    obtain ⟨cur,hreach,hclen,hprefix⟩ := ih (by omega)
    obtain ⟨_,hor,hand⟩ := hscan
    let b : Int := m
    have hb : 0≤b := Int.ofNat_zero_le m
    have hprofile := (reachable_preserves_bit_counts__final_result n a cur hlen hreach).2
    have hphase1 : ∃ cur1, ReachableByBitSwaps n cur cur1 ∧ Zlength cur1=n ∧
        Z.testbit (Znth 0 cur1 0) b=Z.testbit all_or b ∧
        (∀ k q, (0≤k ∧ k<n) → 0≤q → q≠b → Z.testbit (Znth k cur1 0) q=Z.testbit (Znth k cur 0) q) := by
      cases hc : Z.testbit (Znth 0 cur 0) b with
      | false => cases ho : Z.testbit all_or b with
        | false => exact ⟨cur,reach_refl n cur,hclen,hc,fun _ _ _ _ _ => rfl⟩
        | true =>
          obtain ⟨j,hj,hjbit⟩ := (hor b hb).mp ho
          obtain ⟨s,hs,hsbit⟩ := (hprofile b hb true).mp ⟨j,by omega,hjbit⟩
          have hs0 : 0≠s := by intro he;rw [← he,hc] at hsbit;cases hsbit
          obtain ⟨cur1,hr1,hl1,hbit1,hcols1,_⟩ := force_bit_once__final_result n cur 0 s b hclen (by omega) (by omega) hs0 hb
          exact ⟨cur1,hr1,hl1,by rw [hbit1,hsbit],hcols1⟩
      | true => cases ho : Z.testbit all_or b with
        | false =>
          obtain ⟨j,hj,hjbit⟩ := (hprofile b hb true).mpr ⟨0,by omega,hc⟩
          have hh := (hor b hb).mpr ⟨j,by omega,hjbit⟩
          rw [ho] at hh;cases hh
        | true => exact ⟨cur,reach_refl n cur,hclen,hc,fun _ _ _ _ _ => rfl⟩
    obtain ⟨cur1,hr1,hl1,hcur1or,hcols1⟩ := hphase1
    have hreach1 := reach_trans n a cur cur1 hreach hr1
    have hprofile1 := (reachable_preserves_bit_counts__final_result n a cur1 hlen hreach1).2
    have hphase2 : ∃ cur2, ReachableByBitSwaps n cur1 cur2 ∧ Zlength cur2=n ∧
        Z.testbit (Znth 0 cur2 0) b=Z.testbit all_or b ∧
        Z.testbit (Znth 1 cur2 0) b=Z.testbit all_and b ∧
        (∀ k q, (0≤k ∧ k<n) → 0≤q → q≠b → Z.testbit (Znth k cur2 0) q=Z.testbit (Znth k cur1 0) q) := by
      cases hc : Z.testbit (Znth 1 cur1 0) b with
      | false => cases ha : Z.testbit all_and b with
        | false => exact ⟨cur1,reach_refl n cur1,hl1,hcur1or,hc,fun _ _ _ _ _ => rfl⟩
        | true =>
          obtain ⟨j,hj,hjbit⟩ := (hprofile1 b hb false).mpr ⟨1,by omega,hc⟩
          have hh := (hand b hb).mp ha j (by omega)
          rw [hjbit] at hh;cases hh
      | true => cases ha : Z.testbit all_and b with
        | true => exact ⟨cur1,reach_refl n cur1,hl1,hcur1or,hc,fun _ _ _ _ _ => rfl⟩
        | false =>
          have hnot : ¬ (∀ j, (0≤j ∧ j<max 1 n) → Z.testbit (Znth j a 0) b=true) := by
            intro hh;have hh' := (hand b hb).mpr hh;rw [ha] at hh';cases hh'
          push_neg at hnot
          obtain ⟨j,hj,hjnot⟩ := hnot
          have hjbit : Z.testbit (Znth j a 0) b=false := by
            cases hh : Z.testbit (Znth j a 0) b with
            | false => rfl
            | true => exact False.elim (hjnot hh)
          obtain ⟨s,hs,hsbit⟩ := (hprofile1 b hb false).mp ⟨j,by omega,hjbit⟩
          have hs1 : 1≠s := by intro he;rw [← he,hc] at hsbit;cases hsbit
          have hot : Z.testbit all_or b=true := by
            obtain ⟨j,hj,hjbit⟩ := (hprofile1 b hb true).mpr ⟨1,by omega,hc⟩
            exact (hor b hb).mpr ⟨j,by omega,hjbit⟩
          have hs0 : 0≠s := by intro he;rw [← he,hcur1or,hot] at hsbit;cases hsbit
          obtain ⟨cur2,hr2,hl2,hbit2,hcols2,hpos2⟩ := force_bit_once__final_result n cur1 1 s b hl1 (by omega) (by omega) hs1 hb
          refine ⟨cur2,hr2,hl2,?_,?_,hcols2⟩
          · rw [hpos2 0 (by omega) (by omega) hs0];exact hcur1or
          · rw [hbit2,hsbit]
    obtain ⟨cur2,hr2,hl2,hcur2or,hcur2and,hcols2⟩ := hphase2
    refine ⟨cur2,reach_trans n a cur1 cur2 hreach1 hr2,hl2,?_⟩
    intro q hq
    by_cases he : q=b
    · simpa only [he] using And.intro hcur2or hcur2and
    · have hqm : 0≤q ∧ q<Int.ofNat m := by dsimp only [b] at he; simp only [Int.ofNat_eq_coe] at *;omega
      obtain ⟨hpo,hpa⟩ := hprefix q hqm
      constructor
      · rw [hcols2 0 q (by omega) hq.1 he,hcols1 0 q (by omega) hq.1 he];exact hpo
      · rw [hcols2 1 q (by omega) hq.1 he,hcols1 1 q (by omega) hq.1 he];exact hpa


theorem bounded_testbit_high_false__final_result (x b : Int) (hx : 0≤x ∧ x<1024) (hb : 10≤b) :
    Z.testbit x b=false := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0≤b)
  have hxb : x<2^b := by
    have hm : (2:Nat)^10≤2^b := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  exact Nat.testBit_lt_two_pow hxb

theorem canonical_extrema_reachable__final_result (n : Int) (a : List Int) (all_or all_and : Int)
    (hlen : Zlength a=n) (hn : 3≤n)
    (hab : ∀ k, (0≤k ∧ k<n) → 0≤Znth k a 0 ∧ Znth k a 0<1024)
    (horb : 0≤all_or ∧ all_or<1024) (handb : 0≤all_and ∧ all_and<1024)
    (hscan : BitwiseScanState a n all_or all_and) :
    ∃ out, ReachableByBitSwaps n a out ∧ Zlength out=n ∧ Znth 0 out 0=all_or ∧ Znth 1 out 0=all_and := by
  obtain ⟨out,hr,hl,hbits⟩ := canonical_extrema_prefix__final_result 10 n a all_or all_and (by omega) hlen hn hscan
  have hprofile := (reachable_preserves_bit_counts__final_result n a out hlen hr).2
  refine ⟨out,hr,hl,?_,?_⟩
  · apply Z.bits_inj'
    intro b hb
    by_cases hbl : b<10
    · exact (hbits b (by change 0≤b ∧ b<10;omega)).1
    · obtain ⟨k,hk,hkbit⟩ := (hprofile b hb (Z.testbit (Znth 0 out 0) b)).mpr ⟨0,by omega,rfl⟩
      rw [← hkbit,bounded_testbit_high_false__final_result _ b (hab k (by omega)) (by omega),bounded_testbit_high_false__final_result all_or b horb (by omega)]
  · apply Z.bits_inj'
    intro b hb
    by_cases hbl : b<10
    · exact (hbits b (by change 0≤b ∧ b<10;omega)).2
    · obtain ⟨k,hk,hkbit⟩ := (hprofile b hb (Z.testbit (Znth 1 out 0) b)).mpr ⟨1,by omega,rfl⟩
      rw [← hkbit,bounded_testbit_high_false__final_result _ b (hab k (by omega)) (by omega),bounded_testbit_high_false__final_result all_and b handb (by omega)]

theorem land_le_nonnegative__final_result (x y : Int) (hx : 0≤x) (hy : 0≤y) :
    Z.land x y≤x ∧ Z.land x y≤y := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy
  have hl : x &&& y≤x := Nat.and_le_left
  have hr : x &&& y≤y := Nat.and_le_right
  change Int.ofNat (x &&& y)≤Int.ofNat x ∧ Int.ofNat (x &&& y)≤Int.ofNat y
  exact ⟨Int.ofNat_le.mpr hl,Int.ofNat_le.mpr hr⟩

theorem In_Znth_index__final_result (l : List Int) (x : Int) (hin : x∈l) :
    ∃ k, (0≤k ∧ k<Zlength l) ∧ Znth k l 0=x := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hin
  refine ⟨k,by simp only [Zlength,Int.ofNat_eq_coe];omega,?_⟩
  simp only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]

private theorem land_nonneg_right (x y : Int) (hy : 0≤y) : 0≤Z.land x y := by
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy
  cases x <;> exact Int.ofNat_zero_le _

private theorem Znth_mem (l : List Int) (k : Int) (hk : 0≤k ∧ k<Zlength l) : Znth k l 0∈l := by
  have hb : k.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hk;omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,Option.getD_some]
  exact List.getElem_mem hb

theorem reachable_elements_bounded_by_scan_extrema__final_result (n : Int) (a out : List Int) (all_or all_and : Int)
    (hlen : Zlength a=n) (hab : ∀ k, (0≤k ∧ k<n) → 0≤Znth k a 0 ∧ Znth k a 0<1024)
    (horb : 0≤all_or ∧ all_or<1024) (handb : 0≤all_and ∧ all_and<1024)
    (hscan : BitwiseScanState a n all_or all_and) (hr : ReachableByBitSwaps n a out)
    (x : Int) (hin : x∈out) : all_and≤x ∧ x≤all_or := by
  obtain ⟨hscanbounds,hor,hand⟩ := hscan
  obtain ⟨hl,hprofile⟩ := reachable_preserves_bit_counts__final_result n a out hlen hr
  obtain ⟨k,hk,hkx⟩ := In_Znth_index__final_result out x hin
  have hx_or : Z.land x all_or=x := by
    apply Z.bits_inj'
    intro b hb
    rw [Z.land_spec]
    cases hxbit : Z.testbit x b with
    | false => simp
    | true =>
      have hout : ∃ j, (0≤j ∧ j<Zlength out) ∧ Z.testbit (Znth j out 0) b=true := ⟨k,hk,by rw [hkx];exact hxbit⟩
      obtain ⟨j,hj,hjbit⟩ := (hprofile b hb true).mpr hout
      have hh := (hor b hb).mpr ⟨j,by omega,hjbit⟩
      simp only [hh,Bool.and_self]
  have hx0 : 0≤x := by rw [← hx_or];exact land_nonneg_right x all_or horb.1
  have hxle : x≤all_or := by
    have hh := (land_le_nonnegative__final_result x all_or hx0 horb.1).2
    rwa [hx_or] at hh
  have hand_x : Z.land all_and x=all_and := by
    apply Z.bits_inj'
    intro b hb
    rw [Z.land_spec]
    cases hab : Z.testbit all_and b with
    | false => simp
    | true =>
      have hall := (hand b hb).mp hab
      cases hxbit : Z.testbit x b with
      | true => rfl
      | false =>
        have hout : ∃ j, (0≤j ∧ j<Zlength out) ∧ Z.testbit (Znth j out 0) b=false := ⟨k,hk,by rw [hkx];exact hxbit⟩
        obtain ⟨j,hj,hjbit⟩ := (hprofile b hb false).mpr hout
        have hh := hall j (by omega)
        rw [hjbit] at hh;cases hh
  have hle : all_and≤x := by
    have hh := (land_le_nonnegative__final_result all_and x handb.1 hx0).2
    rwa [hand_x] at hh
  exact ⟨hle,hxle⟩

theorem array_spread_from_extrema_bounds__final_result (out : List Int) (all_and all_or : Int)
    (hia : all_and∈out) (hio : all_or∈out)
    (hb : ∀ x, x∈out → all_and≤x ∧ x≤all_or) : ArraySpread out (all_or-all_and) := by
  refine ⟨(all_and,all_or),⟨⟨hia,hio⟩,?_⟩,rfl⟩
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  have hxb := hb x hx
  have hyb := hb y hy
  dsimp only
  omega

theorem bitwise_scan_final_implies_spec__final_result (n : Int) (a : List Int) (all_or all_and : Int)
    (hlen : Zlength a=n) (hn : 3≤n)
    (hab : ∀ k, (0≤k ∧ k<n) → 0≤Znth k a 0 ∧ Znth k a 0<1024)
    (horb : 0≤all_or ∧ all_or<1024) (handb : 0≤all_and ∧ all_and<1024)
    (hscan : BitwiseScanState a n all_or all_and) : Spec a (all_or-all_and) := by
  obtain ⟨best,hr,hl,hbo,hba⟩ := canonical_extrema_reachable__final_result n a all_or all_and hlen hn hab horb handb hscan
  have hio : all_or∈best := hbo ▸ Znth_mem best 0 (by omega)
  have hia : all_and∈best := hba ▸ Znth_mem best 1 (by omega)
  have hbb := reachable_elements_bounded_by_scan_extrema__final_result n a best all_or all_and hlen hab horb handb hscan hr
  have hspread := array_spread_from_extrema_bounds__final_result best all_and all_or hia hio hbb
  refine ⟨(best,all_or-all_and),⟨⟨?_,hspread⟩,?_⟩,rfl⟩
  · change ReachableByBitSwaps (Zlength a) a best
    rw [hlen];exact hr
  · rintro ⟨other,d⟩ ⟨hreach,hsp⟩
    change ReachableByBitSwaps (Zlength a) a other at hreach
    rw [hlen] at hreach
    obtain ⟨⟨x,y⟩,⟨⟨hx,hy⟩,hmax⟩,hd⟩ := hsp
    have hxb := reachable_elements_bounded_by_scan_extrema__final_result n a other all_or all_and hlen hab horb handb hscan hreach x hx
    have hyb := reachable_elements_bounded_by_scan_extrema__final_result n a other all_or all_and hlen hab horb handb hscan hreach y hy
    change y-x=d at hd
    change d≤all_or-all_and
    omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib
