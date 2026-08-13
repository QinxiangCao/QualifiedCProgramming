import Lake

open Lake DSL

package «compcert» where

@[default_target]
lean_lib compcert where

@[default_target]
lean_lib CompCertTests where
  roots := #[`CompCertIntegerTests]
