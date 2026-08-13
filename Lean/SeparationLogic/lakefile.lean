import Lake

open Lake DSL

package «separationlogic» where

require auxlibs from "../auxlibs"
require compcert from "../compcert_lib"
require unifysl from "../unifysl"
require setsclass from "../sets"

@[default_target]
lean_lib SeparationLogic where
  roots := #[`SimpleC.SL]

@[default_target]
lean_lib SeparationLogicTests where
  roots := #[`SeparationLogicTests, `IntLibTests, `IntLibTacticTests,
    `CNotationApiTests, `UnifyslBridgeTests, `CommonAssertionBinderFixture,
    `CommonAssertionTests,
    `AssertionTests, `ConAssertionTests, `StoreAuxTests, `ArrayLibCoreTests,
    `ArrayLibTests, `Array2LibCoreTests, `Array2LibTests, `MapLibTests,
    `PtrArray2LibCoreTests, `PtrArray2LibTests, `StringLibTests,
    `CriticalSTSTests, `SeparationLogicApiTests, `NestedCriticalSTSTests,
    `AutomationProbe]
