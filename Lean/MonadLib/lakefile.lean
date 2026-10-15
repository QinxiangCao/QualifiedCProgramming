import Lake

open Lake DSL

package «monadlib» where

require fixedpoints from "../fixedpoints"
require listlib from "../listlib"

@[default_target]
lean_lib MonadLib where

@[default_target]
lean_lib MonadLibTests where
  roots := #[`MonadLibTests]

@[default_target]
lean_lib UnifiedTacticsTests where
  roots := #[`UnifiedTacticsTests]

@[default_target]
lean_lib FacadeImportTests where
  roots := #[`FacadeImportTests]

@[default_target]
lean_lib P12Tests where
  roots := #[`P12Tests]
