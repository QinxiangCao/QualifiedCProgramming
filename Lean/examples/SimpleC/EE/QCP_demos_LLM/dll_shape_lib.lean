import SimpleC.EE.QCP_demos_LLM.dll_queue_lib

namespace SimpleC.EE.QCP_demos_LLM

open SimpleC.SL.CommonAssertion SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance dll_shape_libSacContext : SacContext := ⟨naive_C_Rules⟩

def dlistrep_shape (x prev : Int) : Assertion := EX l : List Int, dlistrep x prev l
def dllseg_shape (x px py y : Int) : Assertion := EX l : List Int, dllseg x y px py l

end SimpleC.EE.QCP_demos_LLM
