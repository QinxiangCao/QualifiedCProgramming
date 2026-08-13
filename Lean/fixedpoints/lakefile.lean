import Lake

open Lake DSL

package «fixedpoints» where

require setsclass from "../sets"

@[default_target]
lean_lib FP where

@[default_target]
lean_lib AUXLibRelations where
  roots := #[`AUXLib.Relations]

@[default_target]
lean_lib FPTests where
  roots := #[`FPTests]
