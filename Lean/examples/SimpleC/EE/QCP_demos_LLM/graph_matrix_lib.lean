import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.QCP_demos_LLM
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance graph_matrix_libSacContext : SacContext := ⟨naive_C_Rules⟩

namespace GraphMatrixFlat
noncomputable def store_graph (n : Int) (model : List (List Int) → Prop)
    (p : Int) (rows : List (List Int)) : Assertion :=
  “ model rows ” && naive_C_Rules.IntArray2.full p n n rows
end GraphMatrixFlat

namespace GraphMatrixPtr
theorem missing_i_rows_Zlength (p n i row : Int) (rows : List (List Int)) :
    naive_C_Rules.IntPtrArray2.missing_i p n i row rows |-- “ Zlength rows = n ” := by
  intro heap h
  rcases h with ⟨ptrs, hlength, _⟩
  exact hlength.2.1

noncomputable def store_graph (n : Int) (model : List (List Int) → Prop)
    (p : Int) (rows : List (List Int)) : Assertion :=
  “ model rows ” && naive_C_Rules.IntPtrArray2.full p n rows

noncomputable def row_rep (n : Int) (model : List (List Int) → Prop)
    (p i row : Int) (rows : List (List Int)) : Assertion :=
  “ model rows ” &&
  ((p + i * sizeof(PTR)) # PTR |-> row) **
  naive_C_Rules.IntArray.full row (Zlength (Znth i rows [])) (Znth i rows []) **
  naive_C_Rules.IntPtrArray2.missing_i p n i row rows
end GraphMatrixPtr
end SimpleC.EE.QCP_demos_LLM
