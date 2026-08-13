import SimpleC.SL.ArrayLib

namespace ArrayLibTests

open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CNotation
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig

#check ArrayLibSig
#check ArrayLibSig.canonical
#check ArrayFacade
#check StoreCharAsElement
#check StoreUCharAsElement
#check StoreShortAsElement
#check StoreUShortAsElement
#check StoreIntAsElement
#check StoreUIntAsElement
#check StoreInt64AsElement
#check StoreUInt64AsElement
#check StorePtrAsElement
#check CharArray
#check UCharArray
#check ShortArray
#check UShortArray
#check IntArray
#check UIntArray
#check Int64Array
#check UInt64Array
#check PtrArray

section

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}

example : (StoreCharAsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUCharAsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreShortAsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUShortAsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreIntAsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUIntAsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreInt64AsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StoreUInt64AsElement CRules DePredSig SLibSig).A = Int := rfl
example : (StorePtrAsElement CRules DePredSig SLibSig).A = Int := rfl

example (x lo a : Int) :
    (StoreCharAsElement CRules DePredSig SLibSig).storeA x lo a =
      store_char CRules
        (x + lo * sizeof_front_end_type FET_char) a := rfl

example (x lo a : Int) :
    (StorePtrAsElement CRules DePredSig SLibSig).storeA x lo a =
      store_ptr CRules (x + lo * 4) a := rfl

#check (CharArray CRules DePredSig SLibSig).full
#check (CharArray CRules DePredSig SLibSig).seg_split_to_seg
#check (UCharArray CRules DePredSig SLibSig).full
#check (ShortArray CRules DePredSig SLibSig).full
#check (UShortArray CRules DePredSig SLibSig).full
#check (IntArray CRules DePredSig SLibSig).full
#check (IntArray CRules DePredSig SLibSig).full_split_to_full
#check (IntArray CRules DePredSig SLibSig).full_merge_to_full
#check (IntArray CRules DePredSig SLibSig).full_length_range
#check (UIntArray CRules DePredSig SLibSig).full
#check (Int64Array CRules DePredSig SLibSig).full
#check (UInt64Array CRules DePredSig SLibSig).full
#check (PtrArray CRules DePredSig SLibSig).full

example (x n : Int) (l : List Int) :
    CRules.derivable1
      ((IntArray CRules DePredSig SLibSig).full x n l)
      ((IntArray CRules DePredSig SLibSig).seg x 0 n l) :=
  (IntArray CRules DePredSig SLibSig).full_to_seg x n l

example (x n : Int) :
    CRules.logic_equiv
      ((IntArray CRules DePredSig SLibSig).full x n [])
      (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (x lo : Int) :
    CRules.logic_equiv
      ((PtrArray CRules DePredSig SLibSig).undef_seg x lo lo)
      CRules.emp := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (n : Int) :
    CRules.logic_equiv
      (CRules.exp Int fun x =>
        (IntArray CRules DePredSig SLibSig).full x n [])
      (CRules.exp Int fun _ =>
        CRules.andp (CRules.coq_prop (n = 0)) CRules.emp) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (n : Int) :
    CRules.logic_equiv
      (CRules.exp Int fun x =>
        CRules.sepcon
          ((IntArray CRules DePredSig SLibSig).full x n [])
          ((IntArray CRules DePredSig SLibSig).full x n []))
      (CRules.exp Int fun _ =>
        CRules.sepcon
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

example (n : Int) :
    CRules.logic_equiv
      (CRules.allp Int fun x =>
        CRules.sepcon
          ((IntArray CRules DePredSig SLibSig).full x n [])
          ((IntArray CRules DePredSig SLibSig).full x n []))
      (CRules.allp Int fun _ =>
        CRules.sepcon
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)
          (CRules.andp (CRules.coq_prop (n = 0)) CRules.emp)) := by
  ArraySimplify
  exact CRules.toContext.logic_equiv_refl _

set_option maxHeartbeats 1000000 in
example (n : Int) (h : n >= 0) :
    CRules.logic_equiv
      (CRules.exp Int fun x =>
        CRules.sepcon
          ((PtrArray CRules DePredSig SLibSig).undef_full x (n + 1))
          ((PtrArray CRules DePredSig SLibSig).undef_full x (n + 1)))
      (CRules.exp Int fun x =>
        CRules.sepcon
          (CRules.sepcon
            ((PtrArray CRules DePredSig SLibSig).undefstoreA x 0)
            ((PtrArray CRules DePredSig SLibSig).undef_seg x 1 (n + 1)))
          (CRules.sepcon
            ((PtrArray CRules DePredSig SLibSig).undefstoreA x 0)
            ((PtrArray CRules DePredSig SLibSig).undef_seg x 1 (n + 1)))) := by
  ArraySimplify
  · exact CRules.toContext.logic_equiv_refl _
  · exact h
  · exact h

end

#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StoreCharAsElement
#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StoreIntAsElement
#print axioms SimpleC.SL.ArrayLib.ArrayLibSig.StorePtrAsElement

end ArrayLibTests
