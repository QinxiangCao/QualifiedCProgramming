import Lake

open Lake DSL

package «separationlogic» where

require auxlibs from "../auxlibs"
require compcert from "../compcert_lib"
require flocq from "../flocq"
require unifysl from "../unifysl"
require setsclass from "../sets"
require monadlib from "../MonadLib"

@[default_target]
lean_lib SeparationLogic where
  roots := #[`SimpleC.SL, `SimpleC.Common.CTypes, `SimpleC.CoreLang.CTypes]

@[default_target]
lean_lib SeparationLogicTests where
  roots := #[`SeparationLogicTests, `IntLibTests, `IntLibTacticTests, `FloatLibTests, `CArchTests,
    `CNotationApiTests, `CoqBoolUpdateTests, `UnifyslBridgeTests, `CommonAssertionBinderFixture,
    `CommonAssertionTests, `CommonAssertionArchTests, `FloatVCGoalTests, `FloatVCProofTests,
    `AssertionTests, `FunAssertionTests, `ConAssertionTests, `StoreAuxTests, `ArrayLibCoreTests,
    `ArrayLibTests, `ArrayTailRegressionTests, `ArrayLiteralRegressionTests, `Array2LibCoreTests, `Array2LibTests, `Array3LibCoreTests,
    `Array3LibTests, `ArrayArchitectureTests, `MapLibTests,
    `PtrArray2LibCoreTests, `PtrArray2LibTests, `StringLibTests,
    `CriticalSTSTests, `SeparationLogicApiTests, `SeparationLogicAggregateTests,
    `NestedCriticalSTSTests, `LeanPrinterApiTests,
    `AutomationProbe]
