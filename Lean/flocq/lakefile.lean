import Lake

open Lake DSL

package «flocq» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

@[default_target]
lean_lib Flocq where

@[default_target]
lean_lib FlocqTests where
  roots := #[`FlocqTests]
