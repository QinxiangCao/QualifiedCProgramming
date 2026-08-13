import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.poly_sll_lib

open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance poly_sll_libSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev data_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "list")) "data")

private noncomputable abbrev next_addr (p : Int) : addr :=
  addr_notation (LE_arrow_field (RE_const p (FET_alias "list")) "next")

def sll {A : Type} (storeA : addr -> A -> Assertion) (x : addr) :
    List A -> Assertion
  | [] => “ x = NULL ” && emp
  | a :: l0 =>
      “ x ≠ NULL ” &&
        (EX h : addr, EX y : addr,
          store_ptr naive_C_Rules (data_addr x) h **
          store_ptr naive_C_Rules (next_addr x) y **
          storeA h a ** sll storeA y l0)

def sllseg {A : Type} (storeA : addr -> A -> Assertion) (x y : addr) :
    List A -> Assertion
  | [] => “ x = y ” && emp
  | a :: l0 =>
      “ x ≠ NULL ” &&
        (EX h : addr, EX q : addr,
          store_ptr naive_C_Rules (data_addr x) h **
          store_ptr naive_C_Rules (next_addr x) q **
          storeA h a ** sllseg storeA q y l0)

def append {A : Type} (l1 l2 : List A) : List A := l1 ++ l2

attribute [irreducible] sll sllseg

theorem sll_zero {A : Type} (storeA : addr -> A -> Assertion)
    (x : addr) (l : List A) (hx : x = NULL) :
    sll storeA x l |-- “ l = [] ” && emp := by
  subst x
  cases l with
  | nil =>
      rw [sll.eq_1]
      intro state h
      exact ⟨rfl, h.2⟩
  | cons a l =>
      rw [sll.eq_2]
      intro state h
      exact (h.1 rfl).elim

theorem sll_not_zero {A : Type} (storeA : addr -> A -> Assertion)
    (x : addr) (l : List A) (hx : x ≠ NULL) :
    sll storeA x l |--
      EX h : addr, EX y : addr, EX a : A, EX l0 : List A,
        “ l = a :: l0 ” &&
        store_ptr naive_C_Rules (data_addr x) h **
        store_ptr naive_C_Rules (next_addr x) y **
        storeA h a ** sll storeA y l0 := by
  cases l with
  | nil =>
      rw [sll.eq_1]
      intro state h
      exact (hx h.1).elim
  | cons a l =>
      rw [sll.eq_2]
      intro state h
      rcases h with ⟨_, h, y, hspatial⟩
      exact ⟨h, y, a, l, rfl, hspatial⟩

theorem sllseg_sll {A : Type} (storeA : addr -> A -> Assertion)
    (x y : addr) (l1 l2 : List A) :
    sllseg storeA x y l1 ** sll storeA y l2 |--
      sll storeA x (l1 ++ l2) := by
  induction l1 generalizing x with
  | nil =>
      simp only [List.nil_append]
      rw [sllseg.eq_1]
      Intros
      subst x
      entailer!
  | cons a l1 ih =>
      simp only [List.cons_append]
      rw [sllseg.eq_2, sll.eq_2]
      Intros h q
      Exists h q
      sep_apply (ih q)
      entailer!

def sll_para {A : Type} (_storeA : addr -> A -> Assertion) : Prop := True

end SimpleC.EE.QCP_demos_LLM.poly_sll_lib

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.poly_sll_lib (sll sllseg append sll_para)

end SimpleC.EE.QCP_demos_LLM
