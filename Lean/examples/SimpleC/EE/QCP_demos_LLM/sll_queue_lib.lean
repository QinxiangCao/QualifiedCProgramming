import SimpleC.EE.QCP_demos_LLM.sll_lib

namespace SimpleC.EE.QCP_demos_LLM.sll_queue_lib

open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.SeparationLogic
open SimpleC.EE.QCP_demos_LLM
open scoped SimpleC.SL.SAC

local instance sll_queue_libSacContext : SacContext := ⟨naive_C_Rules⟩

def store_queue (x : addr) (l : List Int) : Assertion :=
  EX h : addr, EX t : addr, EX u : Int, EX v : addr,
    “ t ≠ 0 ” &&
    ((&((x # "queue") ->ₛ "head")) # PTR |-> (h)) **
    ((&((x # "queue") ->ₛ "tail")) # PTR |-> (t)) **
    sllseg h t l **
    ((&((t # "list") ->ₛ "data")) # INT |-> (u)) **
    ((&((t # "list") ->ₛ "next")) # PTR |-> (v))

end SimpleC.EE.QCP_demos_LLM.sll_queue_lib

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.sll_queue_lib (store_queue)

end SimpleC.EE.QCP_demos_LLM
