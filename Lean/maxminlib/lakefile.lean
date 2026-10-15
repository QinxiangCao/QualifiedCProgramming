import Lake

open Lake DSL

package «maxminlib» where

require auxlibs from "../auxlibs"
require setsclass from "../sets"

@[default_target]
lean_lib MaxMinLib where

@[default_target]
lean_lib MaxMinLibTests where
  roots := #[`MaxMinLibTests]
