import Lake
open Lake DSL

package «unifysl» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

lean_lib Unifysl where

@[default_target]
lean_lib UnifyslTests where
  roots := #[`ForallCompatTests]
