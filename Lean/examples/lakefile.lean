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
require maxminlib from "../maxminlib"

@[default_target]
lean_lib QCPDemosLLM where
  roots := #[`SimpleC.EE.QCP_demos_LLM]
  globs := #[`SimpleC.EE.QCP_demos_LLM.*]

lean_lib LLMBench where
  roots := #[`SimpleC.EE.LLM_bench]
  globs := #[`SimpleC.EE.LLM_bench.*]

lean_lib UpstreamLibraryChecks where
  roots := #[`UpstreamLibraryChecks]
