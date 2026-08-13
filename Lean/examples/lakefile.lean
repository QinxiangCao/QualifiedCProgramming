import Lake

open Lake DSL

package qcp_demos_llm_examples where

require separationlogic from "../SeparationLogic"
require auxlibs from "../auxlibs"
require compcert from "../compcert_lib"
require unifysl from "../unifysl"
require setsclass from "../sets"
require fixedpoints from "../fixedpoints"
require monadlib from "../MonadLib"
require listlib from "../listlib"

@[default_target]
lean_lib QCPDemosLLM where
  roots := #[`SimpleC.EE.QCP_demos_LLM]
  globs := #[`SimpleC.EE.QCP_demos_LLM.*]
