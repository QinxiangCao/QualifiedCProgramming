import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib
open AUXLib
end SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib
open AUXLib

def ModularInverse (a modulus inverse : Int) : Prop :=
  ∃ coefficient : Int, a * inverse + modulus * coefficient = 1

end SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib
namespace SimpleC.EE.LLM_bench.Algorithms.modular_inverse
export modular_inverse_lib (ModularInverse)
end SimpleC.EE.LLM_bench.Algorithms.modular_inverse
