import SimpleC.EE.QCP_demos_LLM.sll_lib
import AUXLib.ListLib
import Lean.Elab.Tactic.Omega

namespace SimpleC.EE.QCP_demos_LLM.sll_insert_sort_lib

open AUXLib

def increasing_aux : List Int -> Int -> Prop
  | [], _ => True
  | y :: l0, x => x <= y /\ increasing_aux l0 y

def increasing : List Int -> Prop
  | [] => True
  | x :: l0 => increasing_aux l0 x

def strict_upperbound (x : Int) : List Int -> Prop
  | [] => True
  | y :: l' => y < x /\ strict_upperbound x l'

def insert (x : Int) : List Int -> List Int
  | [] => [x]
  | y :: l' => if x > y then y :: insert x l' else x :: y :: l'

theorem upperbound_insert_nil (x : Int) (l : List Int)
    (hbound : strict_upperbound x l) :
    insert x l = l ++ [x] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : a < x := hbound.1
      have htail : strict_upperbound x l := hbound.2
      have hxa : x > a := ha
      simp [insert, hxa]
      rw [ih htail]

theorem upperbound_insert_cons (x : Int) (l1 l2 : List Int) (y : Int)
    (hbound : strict_upperbound x l1) (hxy : x <= y) :
    insert x (l1 ++ y :: l2) = l1 ++ x :: y :: l2 := by
  induction l1 with
  | nil =>
      have hxy' : ¬ x > y := by
        intro h
        omega
      simp [insert, hxy']
  | cons a l1 ih =>
      have ha : a < x := hbound.1
      have htail : strict_upperbound x l1 := hbound.2
      have hxa : x > a := ha
      simp [insert, hxa]
      rw [ih htail]

theorem upperbound_app (x : Int) (l : List Int) (v : Int)
    (hbound : strict_upperbound x l) (hv : v < x) :
    strict_upperbound x (l ++ [v]) := by
  induction l with
  | nil => exact ⟨hv, trivial⟩
  | cons a l ih =>
      exact ⟨hbound.1, ih hbound.2⟩

theorem increasing_aux_insert (x : Int) (l : List Int) (a : Int)
    (hinc : increasing_aux l a) (hax : a <= x) :
    increasing_aux (insert x l) a := by
  induction l generalizing a with
  | nil => exact ⟨hax, trivial⟩
  | cons y l ih =>
      by_cases hxy : x > y
      · simp only [insert, if_pos hxy, increasing_aux]
        exact ⟨hinc.1, ih y hinc.2 (by omega)⟩
      · simp only [insert, if_neg hxy, increasing_aux]
        exact ⟨hax, by omega, hinc.2⟩

theorem increasing_insert (x : Int) (l : List Int)
    (hinc : increasing l) : increasing (insert x l) := by
  cases l with
  | nil => simp only [insert, increasing, increasing_aux]
  | cons y l =>
      by_cases hxy : x > y
      · simp only [insert, if_pos hxy, increasing]
        exact increasing_aux_insert x l y hinc (by omega)
      · simp only [insert, if_neg hxy, increasing, increasing_aux]
        exact ⟨by omega, hinc⟩

theorem perm_insert (x : Int) (l : List Int) :
    Permutation (l ++ [x]) (insert x l) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
      by_cases hxa : x > a
      · simpa only [List.cons_append, insert, if_pos hxa] using ih.cons a
      · simp only [List.cons_append, insert, if_neg hxa]
        change Permutation ([a] ++ (l ++ [x])) ([x] ++ (a :: l))
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := a :: l) (l₂ := [x]))

end SimpleC.EE.QCP_demos_LLM.sll_insert_sort_lib

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.sll_insert_sort_lib (increasing strict_upperbound insert)

end SimpleC.EE.QCP_demos_LLM
