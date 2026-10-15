import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
namespace SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_lib
open AUXLib

def count (m : Int) : List Int → Int
  | [] => 0
  | x :: xs => (if x = m then 1 else 0) + count m xs

def IsMajorityElement (m : Int) (l : List Int) : Prop :=
  2 * count m l > (l.length : Int)

def repeated (candidate vote : Int) : List Int := List.replicate vote.toNat candidate

def MajorityOnReduced (major candidate vote : Int) (rest : List Int) : Prop :=
  0 ≤ vote ∧ IsMajorityElement major (repeated candidate vote ++ rest)

theorem count_app (m : Int) (l1 l2 : List Int) :
    count m (l1 ++ l2) = count m l1 + count m l2 := by
  induction l1 with
  | nil => simp [count]
  | cons a l ih => simp only [List.cons_append, count, ih]; omega

theorem count_repeat_nat (m candidate : Int) (n : Nat) :
    count m (List.replicate n candidate) = if m = candidate then (n : Int) else 0 := by
  induction n with
  | zero => by_cases h : m = candidate <;> simp [count, h]
  | succ n ih =>
    by_cases h : m = candidate
    · subst m; simp [List.replicate_succ, count, ih]; omega
    · simp [List.replicate_succ, count, ih, h, Ne.symm h]

theorem repeated_nil (candidate : Int) : repeated candidate 0 = [] := rfl

theorem repeat_snoc (A : Type) (x : A) (n : Nat) :
    List.replicate (n + 1) x = List.replicate n x ++ [x] := by
  exact List.replicate_append_replicate.symm

theorem repeated_succ (candidate vote : Int) (h : 0 ≤ vote) :
    repeated candidate (vote + 1) = repeated candidate vote ++ [candidate] := by
  unfold repeated
  rw [show (vote + 1).toNat = vote.toNat + 1 by omega]
  exact repeat_snoc Int candidate vote.toNat

theorem repeated_pred (candidate vote : Int) (h : 0 < vote) :
    repeated candidate vote = repeated candidate (vote - 1) ++ [candidate] := by
  have := repeated_succ candidate (vote - 1) (by omega)
  simpa using this

theorem majority_on_reduced_init (major candidate : Int) (rest : List Int)
    (h : IsMajorityElement major rest) : MajorityOnReduced major candidate 0 rest := by
  exact ⟨by omega, h⟩

theorem majority_on_reduced_reset (major candidate a : Int) (rest : List Int)
    (h : IsMajorityElement major (repeated candidate 0 ++ a :: rest)) :
    MajorityOnReduced major a 1 rest := by
  exact ⟨by omega, h⟩

theorem majority_on_reduced_same (major candidate vote : Int) (rest : List Int)
    (hv : 0 ≤ vote)
    (h : IsMajorityElement major (repeated candidate vote ++ candidate :: rest)) :
    MajorityOnReduced major candidate (vote + 1) rest := by
  refine ⟨by omega, ?_⟩
  simpa only [repeated_succ candidate vote hv, List.append_assoc, List.singleton_append] using h

theorem majority_on_reduced_cancel (major candidate a vote : Int) (rest : List Int)
    (hv : 0 < vote) (hne : a ≠ candidate)
    (h : IsMajorityElement major (repeated candidate vote ++ a :: rest)) :
    MajorityOnReduced major candidate (vote - 1) rest := by
  refine ⟨by omega, ?_⟩
  unfold IsMajorityElement repeated at *
  simp only [count_app, count_repeat_nat, count, List.length_append,
    List.length_replicate, List.length_cons, Int.natCast_add, Int.natCast_one] at *
  split at h <;> split at h <;> split <;> omega

theorem majority_of_repeated_eq (major candidate vote : Int) (hv : 0 ≤ vote)
    (h : IsMajorityElement major (repeated candidate vote)) : major = candidate := by
  unfold IsMajorityElement repeated at h
  rw [count_repeat_nat, List.length_replicate] at h
  split at h
  · assumption
  · omega

theorem app_Znth_suffix_cons (l1 l2 : List Int) (i d : Int)
    (hi : i = Zlength l1) (hlt : i < Zlength (l1 ++ l2)) :
    ∃ h t, l2 = h :: t ∧ Znth i (l1 ++ l2) d = h := by
  cases l2 with
  | nil => simp only [List.append_nil] at hlt; omega
  | cons h t =>
    refine ⟨h, t, rfl, ?_⟩
    rw [app_Znth2 d l1 (h :: t) i (by omega), hi]
    simp [Znth]

end SimpleC.EE.LLM_bench.Algorithms.majority_element.majority_element_lib
namespace SimpleC.EE.LLM_bench.Algorithms.majority_element
export majority_element_lib (count IsMajorityElement repeated MajorityOnReduced)
end SimpleC.EE.LLM_bench.Algorithms.majority_element
