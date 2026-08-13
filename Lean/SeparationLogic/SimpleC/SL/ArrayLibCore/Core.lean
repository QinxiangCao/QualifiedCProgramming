import SimpleC.SL.StoreAux

namespace SimpleC.SL.ArrayLibCore

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open Unifysl.LogicGenerator.demo932

structure ArrayLibCoreSig
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _CRules)
    (_SLibSig : StoreAux.StoreLibSig _CRules _DePredSig) : Type where

namespace ArrayLibCoreSig

def canonical (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreAux.StoreLibSig CRules DePredSig) :
    ArrayLibCoreSig CRules DePredSig SLibSig := {}

structure ELEMENT_STORE
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (_SLibSig : StoreAux.StoreLibSig CRules DePredSig) : Type 1 where
  A : Type
  sizeA : Int
  storeA : addr -> Int -> A -> CRules.expr
  undefstoreA : addr -> Int -> CRules.expr
  store_to_undefstore : forall x lo a,
    CRules.derivable1 (storeA x lo a) (undefstoreA x lo)
  storeA_shift : forall x n lo a,
    CRules.logic_equiv
      (storeA (x + n * sizeA) lo a)
      (storeA x (lo + n) a)
  undefstoreA_shift : forall x n lo,
    CRules.logic_equiv
      (undefstoreA (x + n * sizeA) lo)
      (undefstoreA x (lo + n))
  store_to_align : forall x lo a,
    CRules.derivable1 (storeA x lo a) (store_align_n CRules sizeA)
  undefstore_to_align : forall x lo,
    CRules.derivable1 (undefstoreA x lo) (store_align_n CRules sizeA)
  sizeA_valid : 0 < sizeA ∧ sizeA < Int.max_unsigned

end ArrayLibCoreSig

end SimpleC.SL.ArrayLibCore
