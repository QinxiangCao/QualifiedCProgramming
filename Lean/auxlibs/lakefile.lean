import Lake

open Lake DSL

package «auxlibs» where

require compcert from "../compcert_lib"

@[default_target]
lean_lib AUXLib where

@[default_target]
lean_lib AUXLibSetoidRewriteTests where
  roots := #[`AUXLibSetoidRewriteTests]

@[default_target]
lean_lib AUXLibListLibTests where
  roots := #[`AUXLibListLibTests]

@[default_target]
lean_lib AUXLibIntAutoTests where
  roots := #[`AUXLibIntAutoTests]

@[default_target]
lean_lib AUXLibNiaCompatTests where
  roots := #[`AUXLibNiaCompatTests]

@[default_target]
lean_lib AUXLibIdentsVMapTests where
  roots := #[`AUXLibIdentsVMapTests]

@[default_target]
lean_lib AUXLibOrdersDecFactTests where
  roots := #[`AUXLibOrdersDecFactTests]

@[default_target]
lean_lib AUXLibBinaryTreeTests where
  roots := #[`AUXLibBinaryTreeTests]
