import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib

def Pos_Div (a b default : Int) : Int :=
  if b = 0 then default
  else
    let c := Z.quot a b
    if c < 0 then default else c

end SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib

namespace SimpleC.EE.QCP_demos_LLM.simple_arith

export SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib (Pos_Div)

end SimpleC.EE.QCP_demos_LLM.simple_arith

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.simple_arith.PDiv_lib (Pos_Div)

end SimpleC.EE.QCP_demos_LLM
