import Lake

open Lake DSL

package qcp_binary_democases where

require separationlogic from "./Lean/SeparationLogic"
require auxlibs from "./Lean/auxlibs"
require compcert from "./Lean/compcert_lib"
require unifysl from "./Lean/unifysl"
require setsclass from "./Lean/sets"
require fixedpoints from "./Lean/fixedpoints"
require monadlib from "./Lean/MonadLib"
require listlib from "./Lean/listlib"

@[default_target]
lean_lib QCPDemosLLM where
  roots := #[`SimpleC.EE.QCP_demos_LLM]
  globs := #[`SimpleC.EE.QCP_demos_LLM.*]
  srcDir := "Lean/examples"
