import SimpleC.SL.ArrayLibCore.Core

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open Unifysl.LogicGenerator.demo932

universe u

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : SimpleC.SL.StoreAux.StoreLibSig CRules DePredSig}

def mixedstoreA (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (lo : Int) (a : Option ES.A) : CRules.expr :=
  match a with
  | some v => ES.storeA x lo v
  | none => ES.undefstoreA x lo

def seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (lo hi : Int) (l : List ES.A) : CRules.expr :=
  store_array_rec CRules ES.storeA x lo hi l

def missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi : Int) (l : List ES.A) : CRules.expr :=
  store_array_missing_i_rec CRules ES.storeA x i lo hi l

def full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) (l : List ES.A) : CRules.expr :=
  store_array CRules ES.storeA x n l

def undef_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (lo hi : Int) : CRules.expr :=
  store_undef_array_rec CRules ES.undefstoreA x lo hi (hi - lo).toNat

def undef_missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi : Int) : CRules.expr :=
  store_undef_array_missing_i_rec CRules ES.undefstoreA x i lo hi (hi - lo).toNat

def undef_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) : CRules.expr :=
  store_undef_array CRules ES.undefstoreA x n

def seg_shape (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (lo hi : Int) : CRules.expr :=
  store_undef_array_rec CRules
    (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
    x lo hi (hi - lo).toNat

def missing_i_shape (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi : Int) : CRules.expr :=
  store_undef_array_missing_i_rec CRules
    (fun p j => CRules.exp ES.A fun a => ES.storeA p j a)
    x i lo hi (hi - lo).toNat

def full_shape (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) : CRules.expr :=
  store_undef_array CRules
    (fun p i => CRules.exp ES.A fun a => ES.storeA p i a)
    x n

def mixed_seg (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (lo hi : Int) (l : List (Option ES.A)) : CRules.expr :=
  store_array_rec CRules (mixedstoreA ES) x lo hi l

def mixed_missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi : Int) (l : List (Option ES.A)) : CRules.expr :=
  store_array_missing_i_rec CRules (mixedstoreA ES) x i lo hi l

def mixed_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) (l : List (Option ES.A)) : CRules.expr :=
  store_array CRules (mixedstoreA ES) x n l

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib

namespace SimpleC.SL.ArrayLibCore.ArrayLibCoreSig

open AUXLib

def repeat_Z {A : Type u} (a : A) (n : Int) : List A :=
  List.replicate n.toNat a

theorem repeat_Z_tail {A : Type u} (a : A) (n : Int) (h : n >= 0) :
    repeat_Z a (n + 1) = repeat_Z a n ++ [a] := by
  unfold repeat_Z
  have hcount : (n + 1).toNat = n.toNat + 1 := by omega
  rw [hcount]
  let m := n.toNat
  change List.replicate (m + 1) a = List.replicate m a ++ [a]
  induction m with
  | zero => simp
  | succ m ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        congrArg (List.cons a) ih

def SingleSome {A : Type u} (l : List (Option A)) (n : Int) (a : A) : Prop :=
  Znth n l none = some a ∧
    forall m, 0 <= m ∧ m < Zlength l -> m ≠ n -> Znth m l none = none

end SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
