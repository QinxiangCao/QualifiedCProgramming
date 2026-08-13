import SimpleC.SL.ArrayLib

namespace SimpleC.SL.StringLib

open AUXLib
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932

/-- The exact eight-bit character representation used by Coq's `ascii`. -/
abbrev CoqAscii := UInt8

/-- The byte-list representation of Coq's inductive `string`. -/
abbrev CoqString := List CoqAscii

namespace CoqString

/-- Encode a Lean Unicode string as the corresponding Coq byte string. -/
def ofString (s : String) : CoqString :=
  s.toUTF8.toList

end CoqString

namespace StringLibSig

def AsciiToZ (c : CoqAscii) : Int :=
  Int.ofNat c.toNat

def ZToAscii (z : Int) : CoqAscii :=
  UInt8.ofNat (z % 256).toNat

def string_length (s : List Int) : Int :=
  Zlength s

def c_string (s : List Int) : List Int :=
  s ++ [0]

def valid_char (z : Int) : Prop :=
  0 < z ∧ z < 256

def valid_string (s : List Int) : Prop :=
  Forall valid_char s

def StringLength (s : CoqString) : Int :=
  Int.ofNat s.length

def StringToList_nat : CoqString -> Nat -> List Int
  | _, 0 => []
  | [], n + 1 => 0 :: StringToList_nat [] n
  | c :: s, n + 1 => AsciiToZ c :: StringToList_nat s n

def StringToList (s : CoqString) (n : Int) : List Int :=
  StringToList_nat s n.toNat

def ListToString : List Int -> CoqString
  | [] => []
  | c :: s => ZToAscii c :: ListToString s

theorem ZToAscii_AsciiToZ (c : CoqAscii) :
    ZToAscii (AsciiToZ c) = c := by
  have hbound := c.toNat_lt
  have hbound' : c.toNat < 256 := by simpa using hbound
  have hlt : Int.ofNat c.toNat < 256 := Int.ofNat_lt.mpr hbound'
  have hmod : Int.ofNat c.toNat % 256 = Int.ofNat c.toNat :=
    Int.emod_eq_of_lt (Int.ofNat_zero_le _) hlt
  unfold ZToAscii AsciiToZ
  rw [hmod]
  exact UInt8.ofNat_toNat

theorem ListToString_StringToList_nat_full (s : CoqString) :
    ListToString (StringToList_nat s s.length) = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
      simp [StringToList_nat, ListToString, ZToAscii_AsciiToZ, ih]

theorem ListToString_StringToList (s : CoqString) :
    ListToString (StringToList s (StringLength s)) = s := by
  simpa [StringToList, StringLength] using
    ListToString_StringToList_nat_full s

def valid_stringLit (s : CoqString) : Prop :=
  valid_string (StringToList s (StringLength s))

noncomputable def store_string (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (x : addr) (s : List Int) : CRules.expr :=
  CRules.andp (CRules.coq_prop (valid_string s))
    ((CharArray CRules DePredSig SLibSig).full
      x (string_length s + 1) (c_string s))

noncomputable def store_stringLit (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (x : addr) (s : CoqString) : CRules.expr :=
  CRules.andp (CRules.coq_prop (valid_stringLit s))
    ((CharArray CRules DePredSig SLibSig).full
      x (StringLength s + 1) (StringToList s (StringLength s + 1)))

theorem c_string_Zlength (s : List Int) :
    Zlength (c_string s) = string_length s + 1 := by
  simp [c_string, string_length]

theorem StringToList_nat_length (s : CoqString) (n : Nat) :
    (StringToList_nat s n).length = n := by
  induction n generalizing s with
  | zero => simp [StringToList_nat]
  | succ n ih =>
      cases s <;> simp [StringToList_nat, ih]

theorem StringToList_length (s : CoqString) (n : Int) (hn : 0 <= n) :
    Zlength (StringToList s n) = n := by
  simp [StringToList, StringToList_nat_length]
  omega

theorem StringToList_c_length (s : CoqString) :
    Zlength (StringToList s (StringLength s + 1)) = StringLength s + 1 := by
  apply StringToList_length
  have h : 0 <= StringLength s := by simp [StringLength]
  omega

theorem store_string_length (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (x : addr) (s : List Int) :
    CRules.derivable1 (store_string CRules DePredSig SLibSig x s)
      (CRules.coq_prop (Zlength (c_string s) = string_length s + 1)) := by
  exact CRules.toContext.coq_prop_right _ _ (c_string_Zlength s)

theorem store_stringLit_length (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (x : addr) (s : CoqString) :
    CRules.derivable1 (store_stringLit CRules DePredSig SLibSig x s)
      (CRules.coq_prop
        (Zlength (StringToList s (StringLength s + 1)) = StringLength s + 1)) := by
  exact CRules.toContext.coq_prop_right _ _ (StringToList_c_length s)

theorem store_string_split_to_missing_i (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (x i : addr) (s : List Int) (hi : 0 <= i ∧ i < string_length s + 1) :
    CRules.derivable1 (store_string CRules DePredSig SLibSig x s)
      (CRules.sepcon
        (store_char CRules
          (x + i * SimpleC.SL.CNotation.sizeof_front_end_type
            SimpleC.SL.CNotation.FET_char)
          (Znth i (c_string s) 0))
        ((CharArray CRules DePredSig SLibSig).missing_i
          x i 0 (string_length s + 1) (c_string s))) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_andp_elim2 _ _)
    ((CharArray CRules DePredSig SLibSig).full_split_to_missing_i
      x i (string_length s + 1) (c_string s) (0 : Int) hi)

theorem store_stringLit_split_to_missing_i (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (x i : addr) (s : CoqString) (hi : 0 <= i ∧ i < StringLength s + 1) :
    CRules.derivable1 (store_stringLit CRules DePredSig SLibSig x s)
      (CRules.sepcon
        (store_char CRules
          (x + i * SimpleC.SL.CNotation.sizeof_front_end_type
            SimpleC.SL.CNotation.FET_char)
          (Znth i (StringToList s (StringLength s + 1)) 0))
        ((CharArray CRules DePredSig SLibSig).missing_i
          x i 0 (StringLength s + 1)
          (StringToList s (StringLength s + 1)))) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_andp_elim2 _ _)
    ((CharArray CRules DePredSig SLibSig).full_split_to_missing_i
      x i (StringLength s + 1) (StringToList s (StringLength s + 1))
        (0 : Int) hi)

theorem AsciiToZ_range (c : CoqAscii) :
    0 <= AsciiToZ c ∧ AsciiToZ c < 256 := by
  have h := c.toNat_lt
  simp [AsciiToZ]
  omega

end StringLibSig

/-- Source-faithful replacement for the abstract predicates and axioms in the
Coq `StringLibSig` module type. -/
structure StringLibSig
    (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (_ALibSig : ArrayLibSig CRules DePredSig SLibSig) : Type where
  GlobalStrings : (CoqString -> addr) -> CRules.expr
  GlobalStrings_missing : (CoqString -> addr) -> List CoqString -> CRules.expr
  GlobalStrings_split : forall (LitMap : CoqString -> addr) (s : CoqString),
    CRules.derivable1 (GlobalStrings LitMap)
      (CRules.sepcon (GlobalStrings_missing LitMap [s])
        (StringLibSig.store_stringLit CRules DePredSig SLibSig (LitMap s) s))
  GlobalStrings_merge : forall (LitMap : CoqString -> addr) (s : CoqString),
    CRules.derivable1
      (CRules.sepcon (GlobalStrings_missing LitMap [s])
        (StringLibSig.store_stringLit CRules DePredSig SLibSig (LitMap s) s))
      (GlobalStrings LitMap)
  GlobalStrings_missing_split :
    forall (LitMap : CoqString -> addr) (l : List CoqString) (s : CoqString),
      s ∉ l ->
      CRules.derivable1 (GlobalStrings_missing LitMap l)
        (CRules.sepcon (GlobalStrings_missing LitMap (s :: l))
          (StringLibSig.store_stringLit CRules DePredSig SLibSig (LitMap s) s))
  GlobalStrings_missing_merge :
    forall (LitMap : CoqString -> addr) (l : List CoqString) (s : CoqString),
      CRules.derivable1
        (CRules.sepcon (GlobalStrings_missing LitMap (s :: l))
          (StringLibSig.store_stringLit CRules DePredSig SLibSig (LitMap s) s))
        (GlobalStrings_missing LitMap l)
  GlobalStrings_split_existing :
    forall (LitMap : CoqString -> addr) (s : CoqString),
      CRules.derivable1
        (CRules.sepcon
          (StringLibSig.store_stringLit CRules DePredSig SLibSig (LitMap s) s)
          (GlobalStrings LitMap))
        (CRules.sepcon
          (StringLibSig.store_stringLit CRules DePredSig SLibSig (LitMap s) s)
          (GlobalStrings_missing LitMap [s]))

end SimpleC.SL.StringLib
