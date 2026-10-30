import SimpleC.SL.FunAssertion
import SimpleC.SL.SeparationLogic

open SimpleC.SL.FunAssertion SimpleC.SL.Mem
open SimpleC.Common.CTypes SimpleC.CoreLang.CTypes

private def intType : SimpleCtype := CT_basic (CT_int Signed I32)
private def unarySig : FuncSig := ([intType], intType)

example : SimpleC.SL.SeparationLogic.naive_C_Rules32.expr = Assertion := rfl
example : SimpleC.SL.SeparationLogic.naive_C_Rules64.expr = Assertion := rfl
example : SimpleC.SL.SeparationLogic.naiver_C_Rules32.expr =
    SimpleC.SL.SeparationLogic.naive_CSL.toSeparationLogicSig.expr := rfl

example : RetType (CT_basic CT_void) = Unit := rfl
example : ParamTuple [] = Unit := rfl
example : ParamTuple [intType] = Int := rfl
example : ParamTuple [intType, intType, intType] = (Int × (Int × Int)) := rfl

private def identitySem : FunSem unarySig := fun n =>
  { nrm := fun m r m' => r = n ∧ m' = m, err := fun _ => False }

private theorem identityHoare (st : state) (n : Int) :
    HoareExpr emp (identitySem n) (fun r => andp (coq_prop (r = n)) emp) st := by
  intro frame
  constructor
  · rintro r m m' ⟨left, right, hj, hp, hf⟩ ⟨rfl, rfl⟩
    exact ⟨left, right, hj, ⟨rfl, hp⟩, hf⟩
  · intro m hp herr
    exact herr

example (st : state) (f : Int) (hn : f ≠ 0)
    (lookup : st.st_χ unarySig f = some identitySem) :
    func_ptr_hoare f unarySig (fun _ => emp)
      (fun n r => andp (coq_prop (r = n)) emp) st := by
  exact ⟨hn, identitySem, lookup, identityHoare st⟩

example {A : Type} (P : Assertion) (c : MonadLib.program mem A)
    (Q : A → Assertion) (frame : Assertion) :
    derivable1 (HoareExpr P c Q)
      (HoareExpr (sepcon P frame) c (fun r => sepcon (Q r) frame)) :=
  frame_rule_sound c P Q frame

#print axioms frame_rule_sound
#print axioms HoareExpr_raw_frame_rule
#print axioms HoareFun_ramification
