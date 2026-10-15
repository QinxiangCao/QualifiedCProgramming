import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Length
import Mathlib.Data.List.Induction

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib
open AUXLib


open MaxMinLib

def DecimalDigitsOf (x : Int) (digits : List Int) : Prop :=
  0 < Zlength digits ∧ Forall (fun d => 0 ≤ d ∧ d ≤ 9) digits ∧ Znth 0 digits 0 ≠ 0 ∧
    x = digits.foldl (fun value digit => 10 * value + digit) 0

def DigitRecurrenceStep (x y : Int) : Prop :=
  ∃ digits lo hi, DecimalDigitsOf x digits ∧
    min_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) lo ∧
    max_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) hi ∧ y = x + lo * hi

def Pre (a1 k : Int) : Prop :=
  (1 ≤ a1 ∧ a1 ≤ 1000000000000000000) ∧ (1 ≤ k ∧ k ≤ 10000000000000000)

def Spec (a1 k out : Int) : Prop :=
  ∃ values, Zlength values = k ∧ Znth 0 values 0 = a1 ∧ Znth (k - 1) values 0 = out ∧
    ∀ i, (0 ≤ i ∧ i < k - 1) → DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0)

def DigitExtrema (digits : List Int) (lo hi : Int) : Prop :=
  min_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) lo ∧
    max_value_of_subset (· ≤ ·) (fun d : Int => d ∈ digits) (fun d => d) hi

def DigitScanState (original remaining mn mx : Int) : Prop :=
  ∃ pending processed, DecimalDigitsOf original (pending ++ processed) ∧
    remaining = pending.foldl (fun value digit => 10 * value + digit) 0 ∧
    ((processed = [] ∧ mn = 9 ∧ mx = 0) ∨ (processed ≠ [] ∧ DigitExtrema processed mn mx))

def SequencePrefix (a1 count current : Int) : Prop :=
  ∃ values, Zlength values = count ∧ Znth 0 values 0 = a1 ∧ Znth (count - 1) values 0 = current ∧
    ∀ i, (0 ≤ i ∧ i < count - 1) → DigitRecurrenceStep (Znth i values 0) (Znth (i + 1) values 0)



set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem Spec_SequencePrefix (a1 k out : Int) : Spec a1 k out ↔ SequencePrefix a1 k out := Iff.rfl

private theorem forall_app (P : Int→Prop) (a b : List Int) : Forall P (a++b) ↔ Forall P a ∧ Forall P b := by
  simp only [Forall.iff_forall_mem,List.mem_append]
  constructor
  · intro h;exact ⟨fun x hx=>h x (Or.inl hx),fun x hx=>h x (Or.inr hx)⟩
  · rintro ⟨ha,hb⟩ x (hx | hx)
    · exact ha x hx
    · exact hb x hx

private theorem decimal_exists_nat (n : Nat) (hn : 1≤n) : ∃ digits, DecimalDigitsOf n digits := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n<10
    · refine ⟨[(n:Int)],⟨by simp [Zlength],Forall.cons (by omega) Forall.nil,?_,?_⟩⟩
      · change (n:Int)≠0;omega
      · simp only [List.foldl_cons,List.foldl_nil,Int.mul_zero,Int.zero_add]
    · have hqpos : 1≤n/10 := by omega
      have hqlt : n/10<n := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨digits,hl,hb,hh,hv⟩:=ih (n/10) hqlt hqpos
      refine ⟨digits++[(n%10:Int)],?_,?_,?_,?_⟩
      · simp only [Zlength_app,Zlength_cons,Zlength_nil];omega
      · exact (forall_app _ _ _).mpr ⟨hb,Forall.cons (by omega) Forall.nil⟩
      · have he : Znth 0 (digits++[(n%10:Int)]) 0=Znth 0 digits 0 := ListLib.app_Znth1 _ _ _ _ (by change 0≤(0:Int) ∧ 0<Zlength digits;omega)
        rwa [he]
      · rw [List.foldl_append,List.foldl_cons,List.foldl_nil,←hv]
        omega

theorem digit_scan_state_initial__step_initialization (x : Int) (hx : 1≤x) : DigitScanState x x 9 0 := by
  obtain ⟨digits,hd⟩:=decimal_exists_nat x.toNat (by omega)
  have he : (x.toNat:Int)=x := Int.toNat_of_nonneg (by omega)
  rw [he] at hd
  refine ⟨digits,[],?_,hd.2.2.2,Or.inl ⟨rfl,rfl,rfl⟩⟩
  simpa only [List.append_nil] using hd

theorem signed_decimal_remainder_bounds__step_transitions (x : Int) (hx : 0≤x) :
    0≤Z.rem x 10 ∧ Z.rem x 10≤9 := by
  change 0≤Int.tmod x 10 ∧ Int.tmod x 10≤9
  rw [Int.tmod_eq_emod_of_nonneg hx]
  omega

theorem digit_extrema_singleton__step_transitions (d : Int) : DigitExtrema [d] d d := by
  constructor
  · refine ⟨d,⟨by simp,?_⟩,rfl⟩
    intro b hb;have he : b=d := by simpa using hb
    change d≤b;omega
  · refine ⟨d,⟨by simp,?_⟩,rfl⟩
    intro b hb;have he : b=d := by simpa using hb
    change b≤d;omega

theorem digit_extrema_cons__step_transitions (digits : List Int) (mn mx d : Int)
    (he : DigitExtrema digits mn mx) : DigitExtrema (d::digits) (min mn d) (max mx d) := by
  obtain ⟨⟨a,⟨ha,hmin⟩,hea⟩,⟨b,⟨hb,hmax⟩,heb⟩⟩:=he
  change a=mn at hea
  change b=mx at heb
  rw [hea] at ha hmin
  rw [heb] at hb hmax
  constructor
  · refine ⟨min mn d,⟨?_,?_⟩,rfl⟩
    · by_cases h : mn≤d
      · rw [min_eq_left h];exact List.mem_cons_of_mem _ ha
      · rw [min_eq_right (by omega : d≤mn)];exact List.mem_cons_self
    · intro c hc
      change min mn d≤c
      obtain hh | hh := List.mem_cons.mp hc
      · rw [hh];exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (hmin c hh)
  · refine ⟨max mx d,⟨?_,?_⟩,rfl⟩
    · by_cases h : d≤mx
      · rw [max_eq_left h];exact List.mem_cons_of_mem _ hb
      · rw [max_eq_right (by omega : mx≤d)];exact List.mem_cons_self
    · intro c hc
      change c≤max mx d
      obtain hh | hh := List.mem_cons.mp hc
      · rw [hh];exact le_max_right _ _
      · exact le_trans (hmax c hh) (le_max_left _ _)

theorem digit_scan_state_advance__step_transitions (original remaining mn mx : Int)
    (hs : DigitScanState original remaining mn mx) (hr : 0≤remaining) (hrn : remaining≠0) :
    DigitScanState original (Z.quot remaining 10) (min mn (Z.rem remaining 10)) (max mx (Z.rem remaining 10)) := by
  obtain ⟨pending,processed,hd,hrem,hproc⟩:=hs
  have hpne : pending≠[] := by intro he;rw [he] at hrem;exact hrn hrem
  have hex : ∃ pref d, pending=pref++[d] := by
    induction pending using List.reverseRecOn with
    | nil => exact False.elim (hpne rfl)
    | append_singleton pref d ih => exact ⟨pref,d,rfl⟩
  obtain ⟨pref,d,hpending⟩:=hex
  rw [hpending] at hd hrem
  have hforall := (forall_app _ _ _).mp hd.2.1
  have hfd := (forall_app _ _ _).mp hforall.1
  have hdb : 0≤d ∧ d≤9 := hfd.2.mem (by simp)
  rw [List.foldl_append,List.foldl_cons,List.foldl_nil] at hrem
  have hdiv : Z.quot remaining 10=pref.foldl (fun value digit=>10*value+digit) 0 := by
    change Int.tdiv remaining 10= _
    rw [Int.tdiv_eq_ediv_of_nonneg hr]
    omega
  have hmod : Z.rem remaining 10=d := by
    change Int.tmod remaining 10= _
    rw [Int.tmod_eq_emod_of_nonneg hr]
    omega
  rw [hmod]
  refine ⟨pref,d::processed,?_,hdiv,Or.inr ⟨List.cons_ne_nil _ _,?_⟩⟩
  · simpa only [List.append_assoc,List.singleton_append] using hd
  · obtain ⟨hp,hmn,hmx⟩ | ⟨hp,he⟩:=hproc
    · rw [hp,hmn,hmx,min_eq_right (by omega : d≤9),max_eq_right (by omega : (0:Int)≤d)]
      exact digit_extrema_singleton__step_transitions d
    · exact digit_extrema_cons__step_transitions processed mn mx d he

theorem fold_decimal_positive__step_finalization (digits : List Int) (acc : Int)
    (hd : Forall (fun d=>0≤d) digits) (ha : 0<acc) :
    0<digits.foldl (fun value digit=>10*value+digit) acc := by
  induction hd generalizing acc with
  | nil => exact ha
  | @cons d digits hd ht ih => exact ih (10*acc+d) (by omega)

theorem digit_scan_state_complete__step_finalization (x_pre mn mx : Int)
    (hs : DigitScanState x_pre 0 mn mx) : DigitRecurrenceStep x_pre (x_pre+mn*mx) := by
  obtain ⟨pending,processed,hd,hr,hstate⟩:=hs
  cases pending with
  | nil =>
    change DecimalDigitsOf x_pre processed at hd
    obtain ⟨hp,_⟩ | ⟨hp,he⟩:=hstate
    · rw [hp] at hd;have hh:=hd.1;change 0<(0:Int) at hh;omega
    · exact ⟨processed,mn,mx,hd,he.1,he.2,rfl⟩
  | cons digit pending =>
    have hdigit : 0≤digit := (hd.2.1.mem (by simp)).1
    have hne : digit≠0 := hd.2.2.1
    have hpend : Forall (fun d=>0≤d) pending := by
      apply Forall.iff_forall_mem.mpr
      intro d hh
      exact (hd.2.1.mem (by simp only [List.cons_append,List.mem_cons,List.mem_append];exact Or.inr (Or.inl hh))).1
    have hp:=fold_decimal_positive__step_finalization pending digit hpend (by omega)
    change 0=pending.foldl (fun value digit=>10*value+digit) (10*0+digit) at hr
    simp only [Int.mul_zero,Int.zero_add] at hr
    omega

theorem Znth_app_left__solver_prefix (l1 l2 : List Int) (d i : Int) (hi : 0≤i ∧ i<Zlength l1) :
    Znth i (l1++l2) d=Znth i l1 d := ListLib.app_Znth1 d l1 l2 i hi

theorem Znth_app_last__solver_prefix (l : List Int) (d x : Int) : Znth (Zlength l) (l++[x]) d=x := by
  rw [app_Znth2 d l [x] (Zlength l) (by omega),Int.sub_self,Znth0_cons]

theorem sequence_prefix_base__solver_prefix (a : Int) : SequencePrefix a 1 a := by
  refine ⟨[a],rfl,rfl,rfl,?_⟩
  intro i hi;omega

theorem sequence_prefix_extend__solver_prefix (a1 i a b : Int) (hi : 1≤i)
    (hp : SequencePrefix a1 i a) (hs : DigitRecurrenceStep a b) : SequencePrefix a1 (i+1) b := by
  obtain ⟨values,hlen,hfirst,hlast,hedges⟩:=hp
  refine ⟨values++[b],?_,?_,?_,?_⟩
  · simp only [Zlength_app,Zlength_cons,Zlength_nil];omega
  · rw [Znth_app_left__solver_prefix values [b] 0 0 (by omega)];exact hfirst
  · rw [show i+1-1=Zlength values by omega,Znth_app_last__solver_prefix]
  · intro j hj
    by_cases hold : j<i-1
    · rw [Znth_app_left__solver_prefix values [b] 0 j (by omega),Znth_app_left__solver_prefix values [b] 0 (j+1) (by omega)]
      exact hedges j (by omega)
    · have he : j=i-1 := by omega
      rw [he,Znth_app_left__solver_prefix values [b] 0 (i-1) (by omega),hlast,show i-1+1=Zlength values by omega,Znth_app_last__solver_prefix]
      exact hs

theorem sequence_prefix_index_spec__solver_results (a1 k out : Int) (hp : SequencePrefix a1 k out) : Spec a1 k out := hp

theorem sequence_fixed_point_spec__solver_results (a1 i k a : Int) (hi : 1≤i) (hik : i≤k)
    (hp : SequencePrefix a1 i a) (hs : DigitRecurrenceStep a a) : Spec a1 k a := by
  have hnat : ∀ n : Nat, SequencePrefix a1 (i+(n:Int)) a := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero,Int.add_zero] using hp
    | succ n ih =>
      have hh:=sequence_prefix_extend__solver_prefix a1 (i+(n:Int)) a a (by omega) ih hs
      simpa only [Nat.cast_succ,Int.add_assoc] using hh
  have hh:=hnat (k-i).toNat
  have he : i+((k-i).toNat:Int)=k := by omega
  rw [he] at hh
  exact hh
end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib
