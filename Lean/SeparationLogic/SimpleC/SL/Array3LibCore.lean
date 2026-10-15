import SimpleC.SL.Array2Lib

namespace SimpleC.SL.Array3LibCore

open AUXLib
open SimpleC.SL.Array2Lib
open SimpleC.SL.Array2LibCore.Array2LibCoreSig
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

structure Array3LibCoreSig
    (_Arch : CArchSig) (_Endian : CEndianSig)
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _Arch _Endian _CRules)
    (_SLibSig : StoreLibSig _Arch _Endian _CRules _DePredSig)
    (_ALibSig : SimpleC.SL.ArrayLib.ArrayLibSig
      _Arch _Endian _CRules _DePredSig _SLibSig)
    (_A2LibSig : SimpleC.SL.Array2Lib.Array2LibSig
      _Arch _Endian _CRules _DePredSig _SLibSig _ALibSig) : Type where

namespace Array3LibCoreSig

def canonical (Arch : CArchSig) (Endian : CEndianSig)
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig Arch Endian CRules)
    (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
    (ALibSig : SimpleC.SL.ArrayLib.ArrayLibSig
      Arch Endian CRules DePredSig SLibSig)
    (A2LibSig : SimpleC.SL.Array2Lib.Array2LibSig
      Arch Endian CRules DePredSig SLibSig ALibSig) :
    Array3LibCoreSig Arch Endian CRules DePredSig SLibSig ALibSig A2LibSig := {}

namespace Array3Lib

variable {Arch : CArchSig} {Endian : CEndianSig}
variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig Arch Endian CRules}
variable {SLibSig : StoreLibSig Arch Endian CRules DePredSig}

/-- Coq `Module PlaneArray := Array2Lib ES`, represented as a transparent
first-class view so the complete migrated `Array2Facade` API remains available. -/
abbrev PlaneArray (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig) :
    SimpleC.SL.Array2Lib.Array2LibSig.Array2Facade
      Arch Endian CRules DePredSig SLibSig :=
  ⟨ES⟩

def plane_addr (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (m k i : Int) : addr :=
  x + i * m * k * ES.sizeA

def plane_store (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (m k : Int) (x : addr) (i : Int) (plane : List (List ES.A)) : CRules.expr :=
  (PlaneArray ES).full (plane_addr ES x m k i) m k plane

def mixed_plane_store (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (m k : Int) (x : addr) (i : Int)
    (plane : List (List (Option ES.A))) : CRules.expr :=
  (PlaneArray ES).mixed_full (plane_addr ES x m k i) m k plane

def undef_plane_store (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (m k : Int) (x : addr) (i : Int) : CRules.expr :=
  (PlaneArray ES).undef_full (plane_addr ES x m k i) m k

def full (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (n m k : Int) (planes : List (List (List ES.A))) : CRules.expr :=
  store_array CRules (plane_store ES m k) x n planes

def missing_i (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (i lo hi m k : Int)
    (planes : List (List (List ES.A))) : CRules.expr :=
  store_array_missing_i_rec CRules (plane_store ES m k) x i lo hi planes

def mixed_full (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (n m k : Int)
    (planes : List (List (List (Option ES.A)))) : CRules.expr :=
  store_array CRules (mixed_plane_store ES m k) x n planes

def mixed_missing_i (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (i lo hi m k : Int)
    (planes : List (List (List (Option ES.A)))) : CRules.expr :=
  store_array_missing_i_rec CRules (mixed_plane_store ES m k) x i lo hi planes

def undef_full (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (n m k : Int) : CRules.expr :=
  store_undef_array CRules (undef_plane_store ES m k) x n

def undef_missing_i (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x : addr) (i lo hi m k : Int) : CRules.expr :=
  store_undef_array_missing_i_rec CRules (undef_plane_store ES m k)
    x i lo hi (hi - lo).toNat

theorem full_Zlength (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) (planes : List (List (List ES.A))) :
    CRules.derivable1 (full ES x n m k planes)
      (CRules.coq_prop (Zlength planes = n)) := by
  exact store_array_Zlength CRules (List (List ES.A))
    (plane_store ES m k) x n planes

theorem mixed_full_Zlength
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) (planes : List (List (List (Option ES.A)))) :
    CRules.derivable1 (mixed_full ES x n m k planes)
      (CRules.coq_prop (Zlength planes = n)) := by
  exact store_array_Zlength CRules (List (List (Option ES.A)))
    (mixed_plane_store ES m k) x n planes

theorem missing_i_Zlength
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i lo hi m k : Int) (planes : List (List (List ES.A))) :
    CRules.derivable1 (missing_i ES x i lo hi m k planes)
      (CRules.coq_prop (Zlength planes = hi - lo)) := by
  exact store_array_missing_i_rec_Zlength CRules (List (List ES.A))
    (plane_store ES m k) x i lo hi planes

theorem mixed_missing_i_Zlength
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i lo hi m k : Int) (planes : List (List (List (Option ES.A)))) :
    CRules.derivable1 (mixed_missing_i ES x i lo hi m k planes)
      (CRules.coq_prop (Zlength planes = hi - lo)) := by
  exact store_array_missing_i_rec_Zlength CRules (List (List (Option ES.A)))
    (mixed_plane_store ES m k) x i lo hi planes

theorem full_valid (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) (planes : List (List (List ES.A))) :
    CRules.derivable1 (full ES x n m k planes) (CRules.coq_prop (0 <= n)) := by
  exact store_array_valid CRules (List (List ES.A))
    (plane_store ES m k) x n planes

theorem mixed_full_valid
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) (planes : List (List (List (Option ES.A)))) :
    CRules.derivable1 (mixed_full ES x n m k planes)
      (CRules.coq_prop (0 <= n)) := by
  exact store_array_valid CRules (List (List (Option ES.A)))
    (mixed_plane_store ES m k) x n planes

theorem plane_store_to_undef_plane_store
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x m k i : Int) (plane : List (List ES.A)) :
    CRules.derivable1 (plane_store ES m k x i plane)
      (undef_plane_store ES m k x i) := by
  exact Array2Lib.full_to_undef_full ES (plane_addr ES x m k i) m k plane

theorem mixed_plane_store_to_undef_plane_store
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x m k i : Int) (plane : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_plane_store ES m k x i plane)
      (undef_plane_store ES m k x i) := by
  exact Array2Lib.mixed_full_to_undef_full ES (plane_addr ES x m k i) m k plane

theorem full_split_to_missing_i
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i n m k : Int) (planes : List (List (List ES.A)))
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (full ES x n m k planes)
      (CRules.sepcon
        (Array2Lib.full ES (plane_addr ES x m k i) m k (Znth i planes []))
        (missing_i ES x i 0 n m k planes)) := by
  exact store_array_split_to_missing_i CRules (List (List ES.A))
    (plane_store ES m k) x i n planes [] h

theorem missing_i_merge_to_full
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i n m k : Int) (planes : List (List (List ES.A)))
    (plane : List (List ES.A)) (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon
        (Array2Lib.full ES (plane_addr ES x m k i) m k plane)
        (missing_i ES x i 0 n m k planes))
      (full ES x n m k (replace_Znth i plane planes)) := by
  exact store_array_missing_i_merge_to_array CRules (List (List ES.A))
    (plane_store ES m k) x i n plane planes h

theorem mixed_full_split_to_mixed_missing_i
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i n m k : Int) (planes : List (List (List (Option ES.A))))
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (mixed_full ES x n m k planes)
      (CRules.sepcon
        (Array2Lib.mixed_full ES (plane_addr ES x m k i) m k
          (Znth i planes []))
        (mixed_missing_i ES x i 0 n m k planes)) := by
  exact store_array_split_to_missing_i CRules (List (List (Option ES.A)))
    (mixed_plane_store ES m k) x i n planes [] h

theorem mixed_missing_i_merge_to_mixed_full
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i n m k : Int) (planes : List (List (List (Option ES.A))))
    (plane : List (List (Option ES.A))) (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon
        (Array2Lib.mixed_full ES (plane_addr ES x m k i) m k plane)
        (mixed_missing_i ES x i 0 n m k planes))
      (mixed_full ES x n m k (replace_Znth i plane planes)) := by
  exact store_array_missing_i_merge_to_array CRules (List (List (Option ES.A)))
    (mixed_plane_store ES m k) x i n plane planes h

theorem undef_full_split_to_undef_missing_i
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x i n m k : Int) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (undef_full ES x n m k)
      (CRules.sepcon
        (Array2Lib.undef_full ES (plane_addr ES x m k i) m k)
        (undef_missing_i ES x i 0 n m k)) := by
  simpa only [undef_full, undef_plane_store, undef_missing_i, Int.sub_zero] using
    store_undef_array_split_to_missing_i CRules
      (undef_plane_store ES m k) x i n h

theorem full_to_undef_full
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) (planes : List (List (List ES.A))) :
    CRules.derivable1 (full ES x n m k planes) (undef_full ES x n m k) := by
  exact store_array_to_undef_array CRules (List (List ES.A))
    (plane_store ES m k) (undef_plane_store ES m k)
    (fun x i plane => plane_store_to_undef_plane_store ES x m k i plane)
    x n planes

theorem mixed_full_to_undef_full
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) (planes : List (List (List (Option ES.A)))) :
    CRules.derivable1 (mixed_full ES x n m k planes)
      (undef_full ES x n m k) := by
  exact store_array_to_undef_array CRules (List (List (Option ES.A)))
    (mixed_plane_store ES m k) (undef_plane_store ES m k)
    (fun x i plane => mixed_plane_store_to_undef_plane_store ES x m k i plane)
    x n planes

theorem undef_full_valid
    (ES : ELEMENT_STORE Arch Endian CRules DePredSig SLibSig)
    (x n m k : Int) :
    CRules.derivable1 (undef_full ES x n m k) (CRules.coq_prop (0 <= n)) := by
  intro _ hs
  change 0 <= n
  by_cases hn : 0 <= n
  · exact hn
  · have hzero : n.toNat = 0 := by omega
    simp only [undef_full, store_undef_array, hzero,
      store_undef_array_rec] at hs
    change 0 = n ∧ _ at hs
    omega

end Array3Lib

end Array3LibCoreSig

end SimpleC.SL.Array3LibCore
