import SimpleC.EE.QCP_demos_LLM.sll_lib

namespace SimpleC.EE.QCP_demos_LLM.functional_queue_lib

open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.SeparationLogic
open SimpleC.EE.QCP_demos_LLM
open scoped SimpleC.SL.SAC

local instance functional_queue_libSacContext : SacContext := ⟨naive_C_Rules⟩

def store_queue (x : addr) (l : List Int) : Assertion :=
  EX p1 : addr, EX p2 : addr, EX l1 : List Int, EX l2 : List Int,
    “ l = l1 ++ l2.reverse ” &&
    ((&((x # "queue") ->ₛ "l1")) # PTR |-> (p1)) ** ((&((x # "queue") ->ₛ "l2")) # PTR |-> (p2)) ** sll p1 l1 ** sll p2 l2

end SimpleC.EE.QCP_demos_LLM.functional_queue_lib

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.functional_queue_lib (store_queue)

end SimpleC.EE.QCP_demos_LLM
