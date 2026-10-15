import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib
open AUXLib

inductive Answer where
  | NoSolution : Answer
  | Trees (x3 y3 x4 y4 : Int) : Answer
export Answer (NoSolution Trees)

def SquareCorners (x1 y1 x2 y2 x3 y3 x4 y4 : Int) : Prop :=
  ∃ xl xh yl yh : Int, xl < xh ∧ yl < yh ∧ xh - xl = yh - yl ∧
    Permutation [(x1,y1),(x2,y2),(x3,y3),(x4,y4)] [(xl,yl),(xl,yh),(xh,yl),(xh,yh)]

def Printable (x3 y3 x4 y4 : Int) : Prop :=
  Forall (fun v => -1000 ≤ v ∧ v ≤ 1000) [x3,y3,x4,y4]

def Pre (x1 y1 x2 y2 : Int) : Prop := ¬ (x1 = x2 ∧ y1 = y2)

def CompletesSquare (x1 y1 x2 y2 x3 y3 x4 y4 : Int) : Prop :=
  Printable x3 y3 x4 y4 ∧ SquareCorners x1 y1 x2 y2 x3 y3 x4 y4

def NoCompletion (x1 y1 x2 y2 : Int) : Prop :=
  ¬ ∃ x3 y3 x4 y4 : Int, CompletesSquare x1 y1 x2 y2 x3 y3 x4 y4

def Spec (x1 y1 x2 y2 : Int) (out : Answer) : Prop :=
  match out with
  | Trees x3 y3 x4 y4 => CompletesSquare x1 y1 x2 y2 x3 y3 x4 y4
  | NoSolution => NoCompletion x1 y1 x2 y2

theorem perm4_acdb__final_results {A : Type} (a b c d : A) : List.Perm [a,b,c,d] [a,c,d,b] :=
  ((List.Perm.swap c b [d]).cons a).trans (((List.Perm.swap d b []).cons c).cons a)

theorem perm4_cabd__final_results {A : Type} (a b c d : A) : List.Perm [a,b,c,d] [c,a,b,d] :=
  ((List.Perm.swap c b [d]).cons a).trans (List.Perm.swap c a [b,d])

theorem perm4_dbac__final_results {A : Type} (a b c d : A) : List.Perm [a,b,c,d] [d,b,a,c] :=
  (((List.Perm.swap d c []).cons b).cons a).trans (((List.Perm.swap d b [c]).cons a).trans
    ((List.Perm.swap d a [b,c]).trans ((List.Perm.swap b a [c]).cons d)))

theorem perm4_bdca__final_results {A : Type} (a b c d : A) : List.Perm [a,b,c,d] [b,d,c,a] :=
  (List.Perm.swap b a [c,d]).trans ((((List.Perm.swap d c []).cons a).cons b).trans
    (((List.Perm.swap d a [c]).cons b).trans (((List.Perm.swap c a []).cons d).cons b)))

theorem perm4_bdac__final_results {A : Type} (a b c d : A) : List.Perm [a,b,c,d] [b,d,a,c] :=
  (List.Perm.swap b a [c,d]).trans ((((List.Perm.swap d c []).cons a).cons b).trans ((List.Perm.swap d a [c]).cons b))

theorem perm4_badc__final_results {A : Type} (a b c d : A) : List.Perm [a,b,c,d] [b,a,d,c] :=
  (List.Perm.swap b a [c,d]).trans (((List.Perm.swap d c []).cons a).cons b)

theorem abs_diff (a b : Int) : Z.abs (a-b)=if a<b then b-a else a-b := by
  simp only [Z.abs,Int.ofNat_eq_coe,Int.natCast_natAbs]
  split
  · rw [abs_of_nonpos (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]

theorem diagonal_abs_equal_of_corners__final_results (xl xh yl yh x1 y1 x2 y2 : Int) :
    xl<xh → yl<yh → xh-xl=yh-yl →
    (x1,y1)∈[(xl,yl),(xl,yh),(xh,yl),(xh,yh)] →
    (x2,y2)∈[(xl,yl),(xl,yh),(xh,yl),(xh,yh)] →
    x1≠x2 → y1≠y2 → Z.abs (x1-x2)=Z.abs (y1-y2) := by
  intro hx hy hs h1 h2 hnx hny
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h1 h2
  rcases h1 with h1|h1|h1|h1
  all_goals rcases h2 with h2|h2|h2|h2
  all_goals rw [abs_diff,abs_diff]
  all_goals (repeat' split) <;> omega

theorem no_completion_of_nonaxis_unequal_abs_diffs__final_results (x1 y1 x2 y2 : Int) :
    x1≠x2 → y1≠y2 → Z.abs (x1-x2)≠Z.abs (y1-y2) → NoCompletion x1 y1 x2 y2 := by
  rintro hnx hny hne ⟨x3,y3,x4,y4,_,xl,xh,yl,yh,hx,hy,hs,hperm⟩
  apply hne
  exact diagonal_abs_equal_of_corners__final_results xl xh yl yh x1 y1 x2 y2 hx hy hs
    (hperm.mem_iff.mp (by simp)) (hperm.mem_iff.mp (by simp)) hnx hny

theorem completes_square_diagonal__final_results (x1 y1 x2 y2 : Int) :
    (-100≤x1 ∧ x1≤100) → (-100≤y1 ∧ y1≤100) → (-100≤x2 ∧ x2≤100) → (-100≤y2 ∧ y2≤100) →
    Pre x1 y1 x2 y2 → x1≠x2 → y1≠y2 → Z.abs (x1-x2)=Z.abs (y1-y2) →
    CompletesSquare x1 y1 x2 y2 x1 y2 x2 y1 := by
  intro hx1 hy1 hx2 hy2 hp hnx hny he
  constructor
  · exact Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ Forall.nil)))
  · rw [abs_diff,abs_diff] at he
    by_cases hx : x1<x2 <;> by_cases hy : y1<y2
    · simp only [hx,hy,↓reduceIte] at he
      exact ⟨x1,x2,y1,y2,hx,hy,by omega,perm4_acdb__final_results _ _ _ _⟩
    · simp only [hx,hy,↓reduceIte] at he
      exact ⟨x1,x2,y2,y1,hx,by omega,by omega,perm4_cabd__final_results _ _ _ _⟩
    · simp only [hx,hy,↓reduceIte] at he
      exact ⟨x2,x1,y1,y2,by omega,hy,by omega,perm4_dbac__final_results _ _ _ _⟩
    · simp only [hx,hy,↓reduceIte] at he
      exact ⟨x2,x1,y2,y1,by omega,by omega,by omega,perm4_bdca__final_results _ _ _ _⟩

theorem completes_square_horizontal__final_results (x1 y1 x2 y2 d : Int) :
    (-100≤x1 ∧ x1≤100) → (-100≤y1 ∧ y1≤100) → (-100≤x2 ∧ x2≤100) → (-100≤y2 ∧ y2≤100) →
    Pre x1 y1 x2 y2 → y1=y2 → x1≠x2 → d=Z.abs (x1-x2) →
    CompletesSquare x1 y1 x2 y2 x1 (y1+d) x2 (y2+d) := by
  rintro hx1 hy1 hx2 hy2 hp rfl hnx rfl
  rw [abs_diff]
  split
  · constructor
    · exact Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ Forall.nil)))
    · refine ⟨x1,x2,y1,y1+(x2-x1),by omega,by omega,by omega,?_⟩
      exact (List.Perm.swap (x1,y1+(x2-x1)) (x2,y1) [(x2,y1+(x2-x1))]).cons (x1,y1)
  · constructor
    · exact Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ Forall.nil)))
    · exact ⟨x2,x1,y1,y1+(x1-x2),by omega,by omega,by omega,perm4_bdac__final_results _ _ _ _⟩

theorem completes_square_vertical__final_results (x1 y1 x2 y2 d : Int) :
    (-100≤x1 ∧ x1≤100) → (-100≤y1 ∧ y1≤100) → (-100≤x2 ∧ x2≤100) → (-100≤y2 ∧ y2≤100) →
    Pre x1 y1 x2 y2 → x1=x2 → d=Z.abs (y1-y2) →
    CompletesSquare x1 y1 x2 y2 (x1+d) y1 (x2+d) y2 := by
  rintro hx1 hy1 hx2 hy2 hp rfl rfl
  have hny : y1≠y2 := by intro he; exact hp ⟨rfl,he⟩
  rw [abs_diff]
  split
  · constructor
    · exact Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ Forall.nil)))
    · exact ⟨x1,x1+(y2-y1),y1,y2,by omega,by omega,by omega,List.Perm.refl _⟩
  · constructor
    · exact Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ (Forall.cons ⟨by omega,by omega⟩ Forall.nil)))
    · exact ⟨x1,x1+(y1-y2),y2,y1,by omega,by omega,by omega,perm4_badc__final_results _ _ _ _⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib
