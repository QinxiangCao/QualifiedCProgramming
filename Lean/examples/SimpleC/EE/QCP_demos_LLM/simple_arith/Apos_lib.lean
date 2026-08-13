import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib

def Always_pos (a b c : Int) : Int :=
  if a = 0 then 0
  else if 0 <= b * b - 4 * a * c then 0
  else if 0 < a then 1 else 0

end SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib

namespace SimpleC.EE.QCP_demos_LLM.simple_arith

export SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib (Always_pos)

end SimpleC.EE.QCP_demos_LLM.simple_arith

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.simple_arith.Apos_lib (Always_pos)

end SimpleC.EE.QCP_demos_LLM
