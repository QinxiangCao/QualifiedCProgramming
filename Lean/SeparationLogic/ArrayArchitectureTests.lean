import SimpleC.SL.Array3Lib
import SimpleC.SL.Assertion
import SimpleC.SL.MapLib
import SimpleC.SL.StringLib
import SimpleC.SL.CriticalSTS
import SimpleC.SL.NestedCriticalSTS

namespace ArrayArchitectureTests

open SimpleC.SL.Array3Lib.Array3LibSig
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.Assertion
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.ConAssertion
open SimpleC.SL.CriticalSTS
open SimpleC.SL.MapLib
open SimpleC.SL.MapLib.MapLibSig
open SimpleC.SL.NestedCriticalSTS
open SimpleC.SL.StoreAux.StoreLibSig
open SimpleC.SL.StringLib.StringLibSig

noncomputable section

private abbrev D32B := DerivedPredSig.canonical Arch32 BigEndian SL
private abbrev D32L := DerivedPredSig.canonical Arch32 LittleEndian SL
private abbrev D64B := DerivedPredSig.canonical Arch64 BigEndian SL
private abbrev D64L := DerivedPredSig.canonical Arch64 LittleEndian SL

private abbrev S32B :=
  SimpleC.SL.StoreAux.StoreLibSig.canonical Arch32 BigEndian SL D32B
private abbrev S32L :=
  SimpleC.SL.StoreAux.StoreLibSig.canonical Arch32 LittleEndian SL D32L
private abbrev S64B :=
  SimpleC.SL.StoreAux.StoreLibSig.canonical Arch64 BigEndian SL D64B
private abbrev S64L :=
  SimpleC.SL.StoreAux.StoreLibSig.canonical Arch64 LittleEndian SL D64L

example : (StorePtrAsElement Arch32 BigEndian SL D32B S32B).sizeA = 4 := rfl
example : (StorePtrAsElement Arch32 LittleEndian SL D32L S32L).sizeA = 4 := rfl
example : (StorePtrAsElement Arch64 BigEndian SL D64B S64B).sizeA = 8 := rfl
example : (StorePtrAsElement Arch64 LittleEndian SL D64L S64L).sizeA = 8 := rfl

example (x lo value : Int) :
    (StorePtrAsElement Arch32 BigEndian SL D32B S32B).storeA x lo value =
      store_ptr Arch32 BigEndian SL (x + lo * 4) value := rfl

example (x lo value : Int) :
    (StorePtrAsElement Arch32 LittleEndian SL D32L S32L).storeA x lo value =
      store_ptr Arch32 LittleEndian SL (x + lo * 4) value := rfl

example (x lo value : Int) :
    (StorePtrAsElement Arch64 BigEndian SL D64B S64B).storeA x lo value =
      store_ptr Arch64 BigEndian SL (x + lo * 8) value := rfl

example (x lo value : Int) :
    (StorePtrAsElement Arch64 LittleEndian SL D64L S64L).storeA x lo value =
      store_ptr Arch64 LittleEndian SL (x + lo * 8) value := rfl

example (x lo value : Int) :
    (StoreIntAsElement Arch64 LittleEndian SL D64L S64L).storeA x lo value =
      store_int Arch64 LittleEndian SL (x + lo * 4) value := rfl

example (x n : Int) (values : List Int) :
    SL.derivable1 ((PtrArray Arch64 LittleEndian SL D64L S64L).full x n values)
      (SL.coq_prop
        (0 <= n * 8 ∧ n * 8 <= Arch64.addr_max_unsigned + 1)) := by
  exact (PtrArray Arch64 LittleEndian SL D64L S64L).full_length_range x n values

example (x m k i : Int) :
    (PtrArray3 Arch64 BigEndian SL D64B S64B).plane_addr x m k i =
      x + i * m * k * 8 := rfl

-- Every downstream canonical marker accepts each architecture/endian pair.
example : MapLibSig Arch32 BigEndian SL D32B S32B :=
  MapLibSig.canonical Arch32 BigEndian SL D32B S32B
example : MapLibSig Arch32 LittleEndian SL D32L S32L :=
  MapLibSig.canonical Arch32 LittleEndian SL D32L S32L
example : MapLibSig Arch64 BigEndian SL D64B S64B :=
  MapLibSig.canonical Arch64 BigEndian SL D64B S64B
example : MapLibSig Arch64 LittleEndian SL D64L S64L :=
  MapLibSig.canonical Arch64 LittleEndian SL D64L S64L

example (x : Int) (s : List Int) :
    store_string Arch32 BigEndian SL D32B S32B x s =
      SL.andp (SL.coq_prop (valid_string s))
        ((CharArray Arch32 BigEndian SL D32B S32B).full
          x (string_length s + 1) (c_string s)) := rfl
example (x : Int) (s : List Int) :
    store_string Arch32 LittleEndian SL D32L S32L x s =
      SL.andp (SL.coq_prop (valid_string s))
        ((CharArray Arch32 LittleEndian SL D32L S32L).full
          x (string_length s + 1) (c_string s)) := rfl
example (x : Int) (s : List Int) :
    store_string Arch64 BigEndian SL D64B S64B x s =
      SL.andp (SL.coq_prop (valid_string s))
        ((CharArray Arch64 BigEndian SL D64B S64B).full
          x (string_length s + 1) (c_string s)) := rfl
example (x : Int) (s : List Int) :
    store_string Arch64 LittleEndian SL D64L S64L x s =
      SL.andp (SL.coq_prop (valid_string s))
        ((CharArray Arch64 LittleEndian SL D64L S64L).full
          x (string_length s + 1) (c_string s)) := rfl

private abbrev SmokeCriticalSTS : critical_STS where
  critical_STS_state := Nat
  critical_STS_transition := Eq

private abbrev SmokeCriticalDef : critical_STS_def := ⟨SmokeCriticalSTS⟩
private abbrev SmokeCriticalFacade : critical_STS_to_STS_def SmokeCriticalDef :=
  critical_STS_to_STS_def.canonical SmokeCriticalDef
private def SmokeCriticalLogic : CSL SmokeCriticalFacade.toSTSDef :=
  CSL.canonical SmokeCriticalFacade.toSTSDef
private abbrev SmokeCriticalRules := SmokeCriticalLogic.toSeparationLogicSig
private abbrev CD32B :=
  DerivedPredSig.canonical Arch32 BigEndian SmokeCriticalRules
private abbrev CD32L :=
  DerivedPredSig.canonical Arch32 LittleEndian SmokeCriticalRules
private abbrev CD64B :=
  DerivedPredSig.canonical Arch64 BigEndian SmokeCriticalRules
private abbrev CD64L :=
  DerivedPredSig.canonical Arch64 LittleEndian SmokeCriticalRules

example : CriticalCSL SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch32 BigEndian CD32B :=
  CriticalCSL.canonical SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch32 BigEndian CD32B
example : CriticalCSL SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch32 LittleEndian CD32L :=
  CriticalCSL.canonical SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch32 LittleEndian CD32L
example : CriticalCSL SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch64 BigEndian CD64B :=
  CriticalCSL.canonical SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch64 BigEndian CD64B
example : CriticalCSL SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch64 LittleEndian CD64L :=
  CriticalCSL.canonical SmokeCriticalDef SmokeCriticalFacade SmokeCriticalLogic
    Arch64 LittleEndian CD64L

private abbrev SmokeNestedDef : nested_critical_STS_def := ⟨SmokeCriticalSTS⟩
private abbrev SmokeNestedFacade : nested_critical_STS_to_STS_def SmokeNestedDef :=
  nested_critical_STS_to_STS_def.canonical SmokeNestedDef
private def SmokeNestedLogic : CSL SmokeNestedFacade.toSTSDef :=
  CSL.canonical SmokeNestedFacade.toSTSDef
private abbrev SmokeNestedRules := SmokeNestedLogic.toSeparationLogicSig
private abbrev ND32B :=
  DerivedPredSig.canonical Arch32 BigEndian SmokeNestedRules
private abbrev ND32L :=
  DerivedPredSig.canonical Arch32 LittleEndian SmokeNestedRules
private abbrev ND64B :=
  DerivedPredSig.canonical Arch64 BigEndian SmokeNestedRules
private abbrev ND64L :=
  DerivedPredSig.canonical Arch64 LittleEndian SmokeNestedRules

example : NestedCriticalCSL SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch32 BigEndian ND32B :=
  NestedCriticalCSL.canonical SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch32 BigEndian ND32B
example : NestedCriticalCSL SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch32 LittleEndian ND32L :=
  NestedCriticalCSL.canonical SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch32 LittleEndian ND32L
example : NestedCriticalCSL SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch64 BigEndian ND64B :=
  NestedCriticalCSL.canonical SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch64 BigEndian ND64B
example : NestedCriticalCSL SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch64 LittleEndian ND64L :=
  NestedCriticalCSL.canonical SmokeNestedDef SmokeNestedFacade SmokeNestedLogic
    Arch64 LittleEndian ND64L

end

end ArrayArchitectureTests
