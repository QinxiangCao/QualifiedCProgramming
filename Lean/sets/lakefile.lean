import Lake

open Lake DSL

package «setsclass» where

require auxlibs from "../auxlibs"

@[default_target]
lean_lib SetsClass where

@[default_target]
lean_lib SetsClassTests where
  roots := #[`SetsClassTests]
