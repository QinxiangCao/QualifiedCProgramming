import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib
open AUXLib

abbrev Some {A : Type u} (a : A) : Option A := some a
abbrev None {A : Type u} : Option A := none

def DecimalValue (digits : List Int) : Int := digits.foldl (fun value digit => 10 * value + digit) 0

def BadUglyDigits (n : Int) (digits : List Int) : Prop :=
  Zlength digits = n ∧ Forall (fun d => 1 ≤ d ∧ d ≤ 9) digits ∧
  DecimalValue digits > 0 ∧ Forall (fun d => ¬ Z.divide d (DecimalValue digits)) digits

def Pre (n : Int) : Prop := 1 ≤ n ∧ n ≤ 100000

def Spec (n : Int) (out : Option (List Int)) : Prop :=
  (∃ digits, out = some digits ∧ BadUglyDigits n digits) ∨
  (out = none ∧ ∀ digits, ¬ BadUglyDigits n digits)


private theorem forall_cons_iff (P : Int→Prop) (a : Int) (l : List Int) : Forall P (a::l) ↔ P a ∧ Forall P l := by
  constructor
  · intro h; cases h with | cons ha ht => exact ⟨ha,ht⟩
  · rintro ⟨ha,ht⟩;exact Forall.cons ha ht

private theorem getD_eq (l : List Int) (d : Int) (i : Nat) (h : i<l.length) : l.getD i d=l[i] := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  rfl

-- Coq's last uses its default only on []; List.getLastD has the same behavior.
theorem decimal_value_acc_last_digit_mod_2__spec_results (digits : List Int) (acc : Int)
    (hn : digits ≠ []) : Z.modulo (digits.foldl (fun value digit => 10*value+digit) acc) 2 = Z.modulo (digits.getLastD 0) 2 := by
  induction digits generalizing acc with
  | nil => exact False.elim (hn rfl)
  | cons d tail ih =>
    cases tail with
    | nil =>
      simp only [List.foldl_cons,List.foldl_nil,List.getLastD_cons,List.getLastD_nil,Z.modulo,Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤2)]
      omega
    | cons e tail =>
      simpa only [List.foldl_cons,List.getLastD_cons] using ih (10*acc+d) (by simp)

theorem decimal_value_last_digit_mod_2__spec_results (digits : List Int) (hn : digits ≠ []) :
    Z.modulo (DecimalValue digits) 2=Z.modulo (digits.getLastD 0) 2 :=
  decimal_value_acc_last_digit_mod_2__spec_results digits 0 hn

theorem decimal_value_acc_digit_sum_mod_3__spec_results (digits : List Int) (acc : Int) :
    Z.modulo (digits.foldl (fun value digit => 10*value+digit) acc) 3 = Z.modulo (acc+digits.foldr (·+·) 0) 3 := by
  induction digits generalizing acc with
  | nil => simp only [List.foldl_nil,List.foldr_nil,Int.add_zero]
  | cons d tail ih =>
    rw [List.foldl_cons,ih]
    simp only [List.foldr_cons,Z.modulo,Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤3)]
    omega

theorem decimal_value_digit_sum_mod_3__spec_results (digits : List Int) :
    Z.modulo (DecimalValue digits) 3=Z.modulo (digits.foldr (·+·) 0) 3 := by
  simpa only [Int.zero_add] using decimal_value_acc_digit_sum_mod_3__spec_results digits 0

theorem all_Znth_eq_Forall__spec_results (l : List Int) (d v : Int)
    (h : ∀ k, 0≤k ∧ k<Zlength l → Znth k l d=v) : Forall (fun x => x=v) l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hx
  have hi := h k (by simp only [Zlength,Int.ofNat_eq_coe];omega)
  simpa only [Znth,Int.toNat_natCast,getD_eq _ _ _ hk] using hi

theorem fold_right_add_of_Forall_eq__spec_results (l : List Int) (v : Int)
    (h : Forall (fun x => x=v) l) : l.foldr (·+·) 0=v*Zlength l := by
  induction l with
  | nil => simp [Zlength]
  | cons a l ih =>
    obtain ⟨rfl,ht⟩ := (forall_cons_iff _ _ _).mp h
    rw [List.foldr_cons,ih ht,Zlength_cons]
    ring

theorem decimal_fold_positive__spec_results (digits : List Int) (acc : Int)
    (ha : 0<acc) (h : Forall (fun d => 0≤d) digits) :
    0<digits.foldl (fun value digit => 10*value+digit) acc := by
  induction digits generalizing acc with
  | nil => exact ha
  | cons d tail ih =>
    obtain ⟨hd,ht⟩ := (forall_cons_iff _ _ _).mp h
    exact ih (10*acc+d) (by omega) ht

theorem last_of_Forall_eq__spec_results (l : List Int) (v d : Int) (hn : l≠[])
    (h : Forall (fun x => x=v) l) : l.getLastD d=v := by
  induction l with
  | nil => exact False.elim (hn rfl)
  | cons a l ih =>
    obtain ⟨rfl,ht⟩ := (forall_cons_iff _ _ _).mp h
    cases l with
    | nil => rfl
    | cons b l => simpa only [List.getLastD_cons] using ih (by simp) ht

theorem last_cons_nonempty__spec_results (a : Int) (l : List Int) (d : Int) (hn : l≠[]) :
    (a::l).getLastD d=l.getLastD d := by
  cases l with
  | nil => exact False.elim (hn rfl)
  | cons b l => rfl

theorem two_then_threes_bad_ugly__spec_results (n : Int) (digits : List Int)
    (hn : 2≤n) (hlen : Zlength digits=n) (hfirst : Znth 0 digits 0=2)
    (hlater : ∀ k, 1≤k ∧ k<n → Znth k digits 0=3) : BadUglyDigits n digits := by
  cases digits with
  | nil => change 0=n at hlen; omega
  | cons d tail =>
    change d=2 at hfirst
    subst d
    have htl : Zlength tail=n-1 := by rw [Zlength_cons] at hlen; omega
    have ht : Forall (fun x => x=3) tail := by
      apply all_Znth_eq_Forall__spec_results tail 0 3
      intro k hk
      have hh := hlater (k+1) (by omega)
      rw [Znth_cons 0 (k+1) 2 tail (by omega)] at hh
      simpa only [Int.add_sub_cancel] using hh
    have htne : tail≠[] := by intro he; rw [he,Zlength_nil] at htl; omega
    have hm2 := decimal_value_last_digit_mod_2__spec_results (2::tail) (by simp)
    rw [last_cons_nonempty__spec_results 2 tail 0 htne,last_of_Forall_eq__spec_results tail 3 0 htne ht] at hm2
    have hm3 := decimal_value_digit_sum_mod_3__spec_results (2::tail)
    rw [List.foldr_cons,fold_right_add_of_Forall_eq__spec_results tail 3 ht] at hm3
    have hr3 : Z.modulo (2+3*Zlength tail) 3=2 := by
      simp only [Z.modulo,Int.fmod_eq_emod_of_nonneg _ (by omega : (0:Int)≤3)]
      omega
    rw [hr3] at hm3
    refine ⟨hlen,Forall.cons (by omega) ?_,?_,Forall.cons ?_ ?_⟩
    · exact Forall.iff_forall_mem.mpr (fun x hx => by have he := ht.mem hx;omega)
    · apply decimal_fold_positive__spec_results tail 2 (by omega)
      exact Forall.iff_forall_mem.mpr (fun x hx => by have he := ht.mem hx;omega)
    · intro hd
      have hz := Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).mp hd)
      change Z.modulo (DecimalValue (2::tail)) 2=0 at hz
      change Z.modulo (DecimalValue (2::tail)) 2=1 at hm2
      omega
    · apply Forall.iff_forall_mem.mpr
      intro x hx hd
      have he := ht.mem hx
      subst x
      have hz := Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).mp hd)
      change Z.modulo (DecimalValue (2::tail)) 3=0 at hz
      omega

theorem no_bad_ugly_length_one__spec_results (digits : List Int) : ¬ BadUglyDigits 1 digits := by
  rintro ⟨hlen,_,_,hnot⟩
  cases digits with
  | nil => change 0=1 at hlen;omega
  | cons d tail => cases tail with
    | nil =>
      have hn := hnot.mem (List.mem_cons_self)
      exact hn ⟨1,by simp [DecimalValue]⟩
    | cons e tail =>
      simp only [Zlength_cons] at hlen
      have hz := Zlength_nonneg tail
      omega

theorem Znth_map_inbounds_Z__spec_results (f : Int→Int) (l : List Int) (i da db : Int)
    (hi : 0≤i ∧ i<Zlength l) : Znth i (l.map f) db=f (Znth i l da) := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi;omega
  simp only [Znth,getD_eq _ _ _ hn,getD_eq _ _ _ (by simpa using hn : i.toNat<(l.map f).length),List.getElem_map]

theorem Zlength_map_Z__spec_results (f : Int→Int) (l : List Int) : Zlength (l.map f)=Zlength l := by simp [Zlength]

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P012_1326A_bad_ugly_numbers_lib
