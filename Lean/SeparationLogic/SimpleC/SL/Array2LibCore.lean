import SimpleC.SL.ArrayLib

namespace SimpleC.SL.Array2LibCore

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

structure Array2LibCoreSig
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _CRules)
    (_SLibSig : StoreLibSig _CRules _DePredSig)
    (_ALibSig : SimpleC.SL.ArrayLib.ArrayLibSig _CRules _DePredSig _SLibSig) :
    Type where

namespace Array2LibCoreSig

def canonical (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (ALibSig : SimpleC.SL.ArrayLib.ArrayLibSig CRules DePredSig SLibSig) :
    Array2LibCoreSig CRules DePredSig SLibSig ALibSig := {}

private theorem store_array_rec_to_undef_array_rec_with_length
    (CRules : SeparationLogicSig) (B : Type)
    (storeB : addr -> Int -> B -> CRules.expr)
    (undefB : addr -> Int -> CRules.expr)
    (storeB_to_undefB : forall x lo b,
      CRules.derivable1 (storeB x lo b) (undefB x lo))
    (x lo hi : Int) (l : List B) (hlen : Zlength l = hi - lo) :
    CRules.derivable1 (store_array_rec CRules storeB x lo hi l)
      (store_undef_array_rec CRules undefB x lo hi (hi - lo).toNat) := by
  induction l generalizing lo with
  | nil =>
      have hzero : (hi - lo).toNat = 0 := by
        rw [← hlen]
        simp
      simp only [store_array_rec, hzero, store_undef_array_rec]
      intro _ hs
      exact ⟨hs.1, hs.2.2⟩
  | cons b l ih =>
      have hcount : (hi - lo).toNat = Nat.succ l.length := by
        rw [← hlen]
        simp [Zlength]
      have htail : Zlength l = hi - (lo + 1) := by
        simp only [Zlength_cons] at hlen
        omega
      have htailCount : (hi - (lo + 1)).toNat = l.length := by
        rw [← htail]
        simp [Zlength]
      have ihTail : CRules.derivable1
          (store_array_rec CRules storeB x (lo + 1) hi l)
          (store_undef_array_rec CRules undefB x (lo + 1) hi l.length) := by
        simpa only [htailCount] using ih (lo := lo + 1) htail
      simp only [store_array_rec, hcount, store_undef_array_rec]
      exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (storeB_to_undefB x lo b) ihTail

theorem store_array_rec_to_undef_array_rec
    (CRules : SeparationLogicSig) (B : Type)
    (storeB : addr -> Int -> B -> CRules.expr)
    (undefB : addr -> Int -> CRules.expr)
    (storeB_to_undefB : forall x lo b,
      CRules.derivable1 (storeB x lo b) (undefB x lo))
    (x lo hi : Int) (l : List B) :
    CRules.derivable1 (store_array_rec CRules storeB x lo hi l)
      (store_undef_array_rec CRules undefB x lo hi (hi - lo).toNat) := by
  intro state hs
  have hlen := store_array_rec_Zlength CRules B storeB x lo hi l state hs
  change Zlength l = hi - lo at hlen
  exact store_array_rec_to_undef_array_rec_with_length
    CRules B storeB undefB storeB_to_undefB x lo hi l hlen state hs

theorem store_array_to_undef_array
    (CRules : SeparationLogicSig) (B : Type)
    (storeB : addr -> Int -> B -> CRules.expr)
    (undefB : addr -> Int -> CRules.expr)
    (storeB_to_undefB : forall x lo b,
      CRules.derivable1 (storeB x lo b) (undefB x lo))
    (x n : Int) (l : List B) :
    CRules.derivable1 (store_array CRules storeB x n l)
      (store_undef_array CRules undefB x n) := by
  simpa only [store_array, store_undef_array, Int.sub_zero] using
    store_array_rec_to_undef_array_rec CRules B storeB undefB
      storeB_to_undefB x 0 n l

private theorem store_undef_array_rec_split_to_missing_i_aux
    (CRules : SeparationLogicSig)
    (undefB : addr -> Int -> CRules.expr)
    (x lo i hi : Int) (len : Nat)
    (hlen : len = (hi - lo).toNat) (hiRange : lo <= i ∧ i < hi) :
    CRules.derivable1 (store_undef_array_rec CRules undefB x lo hi len)
      (CRules.sepcon (undefB x i)
        (store_undef_array_missing_i_rec CRules undefB x i lo hi len)) := by
  induction len generalizing lo with
  | zero =>
      omega
  | succ len ih =>
      have htailLen : len = (hi - (lo + 1)).toNat := by omega
      simp only [store_undef_array_rec, store_undef_array_missing_i_rec]
      by_cases heq : i = lo
      · subst i
        exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (Automation.orp_intros_left
            (coq_prop_andp_right CRules (lo = lo) _ _
              (CRules.toContext.derivable1_refl _) rfl))
      · have hgt : i > lo := by omega
        have hTail := ih (lo := lo + 1) htailLen (by omega)
        refine CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl _) hTail) ?_
        refine CRules.toContext.derivable1_trans _ _ _
          (Automation.logic_equiv_sepcon_swap_rule CRules
            (undefB x lo) (undefB x i)
            (store_undef_array_missing_i_rec CRules undefB
              x i (lo + 1) hi len)).left ?_
        exact CRules.toContext.derivable1_sepcon_mono _ _ _ _
          (CRules.toContext.derivable1_refl _)
          (Automation.orp_intros_right
            (coq_prop_andp_right CRules (i > lo) _ _
              (CRules.toContext.derivable1_refl _) hgt))

theorem store_undef_array_rec_split_to_missing_i
    (CRules : SeparationLogicSig)
    (undefB : addr -> Int -> CRules.expr)
    (x lo i hi : Int) (h : lo <= i ∧ i < hi) :
    CRules.derivable1
      (store_undef_array_rec CRules undefB x lo hi (hi - lo).toNat)
      (CRules.sepcon (undefB x i)
        (store_undef_array_missing_i_rec CRules undefB
          x i lo hi (hi - lo).toNat)) :=
  store_undef_array_rec_split_to_missing_i_aux CRules undefB
    x lo i hi (hi - lo).toNat rfl h

theorem store_undef_array_split_to_missing_i
    (CRules : SeparationLogicSig)
    (undefB : addr -> Int -> CRules.expr)
    (x i n : Int) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (store_undef_array CRules undefB x n)
      (CRules.sepcon (undefB x i)
        (store_undef_array_missing_i_rec CRules undefB x i 0 n n.toNat)) := by
  simpa only [store_undef_array, Int.sub_zero] using
    store_undef_array_rec_split_to_missing_i CRules undefB x 0 i n h

namespace Array2Lib

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}

def row_addr (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (m i : Int) : addr :=
  x + i * m * ES.sizeA

def row_store (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (m : Int) (x : addr) (i : Int) (row : List ES.A) : CRules.expr :=
  ArrayLib.full ES (row_addr ES x m i) m row

def mixed_row_store (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (m : Int) (x : addr) (i : Int) (row : List (Option ES.A)) : CRules.expr :=
  ArrayLib.mixed_full ES (row_addr ES x m i) m row

def undef_row_store (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (m : Int) (x : addr) (i : Int) : CRules.expr :=
  ArrayLib.undef_full ES (row_addr ES x m i) m

def full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n m : Int) (rows : List (List ES.A)) : CRules.expr :=
  store_array CRules (row_store ES m) x n rows

def missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi m : Int) (rows : List (List ES.A)) : CRules.expr :=
  store_array_missing_i_rec CRules (row_store ES m) x i lo hi rows

def mixed_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n m : Int) (rows : List (List (Option ES.A))) : CRules.expr :=
  store_array CRules (mixed_row_store ES m) x n rows

def mixed_missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi m : Int)
    (rows : List (List (Option ES.A))) : CRules.expr :=
  store_array_missing_i_rec CRules (mixed_row_store ES m) x i lo hi rows

def undef_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n m : Int) : CRules.expr :=
  store_undef_array CRules (undef_row_store ES m) x n

def undef_missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (i lo hi m : Int) : CRules.expr :=
  store_undef_array_missing_i_rec CRules (undef_row_store ES m)
    x i lo hi (hi - lo).toNat

theorem full_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (rows : List (List ES.A)) :
    CRules.derivable1 (full ES x n m rows)
      (CRules.coq_prop (Zlength rows = n)) := by
  exact store_array_Zlength CRules (List ES.A) (row_store ES m) x n rows

theorem mixed_full_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_full ES x n m rows)
      (CRules.coq_prop (Zlength rows = n)) := by
  exact store_array_Zlength CRules (List (Option ES.A))
    (mixed_row_store ES m) x n rows

theorem missing_i_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi m : Int) (rows : List (List ES.A)) :
    CRules.derivable1 (missing_i ES x i lo hi m rows)
      (CRules.coq_prop (Zlength rows = hi - lo)) := by
  exact store_array_missing_i_rec_Zlength CRules (List ES.A)
    (row_store ES m) x i lo hi rows

theorem mixed_missing_i_Zlength
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i lo hi m : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_missing_i ES x i lo hi m rows)
      (CRules.coq_prop (Zlength rows = hi - lo)) := by
  exact store_array_missing_i_rec_Zlength CRules (List (Option ES.A))
    (mixed_row_store ES m) x i lo hi rows

theorem full_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (rows : List (List ES.A)) :
    CRules.derivable1 (full ES x n m rows) (CRules.coq_prop (0 <= n)) := by
  exact store_array_valid CRules (List ES.A) (row_store ES m) x n rows

theorem mixed_full_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_full ES x n m rows)
      (CRules.coq_prop (0 <= n)) := by
  exact store_array_valid CRules (List (Option ES.A))
    (mixed_row_store ES m) x n rows

theorem row_store_to_undef_row_store
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x m i : Int) (row : List ES.A) :
    CRules.derivable1 (row_store ES m x i row) (undef_row_store ES m x i) := by
  exact ArrayLib.full_to_undef_full ES (row_addr ES x m i) m row

theorem mixed_row_store_to_undef_row_store
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x m i : Int) (row : List (Option ES.A)) :
    CRules.derivable1 (mixed_row_store ES m x i row)
      (undef_row_store ES m x i) := by
  exact ArrayLib.mixed_full_to_undef_full ES (row_addr ES x m i) m row

theorem full_split_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n m : Int) (rows : List (List ES.A)) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (full ES x n m rows)
      (CRules.sepcon
        (ArrayLib.full ES (row_addr ES x m i) m (Znth i rows []))
        (missing_i ES x i 0 n m rows)) := by
  exact store_array_split_to_missing_i CRules (List ES.A)
    (row_store ES m) x i n rows [] h

theorem missing_i_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n m : Int) (rows : List (List ES.A)) (row : List ES.A)
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon (ArrayLib.full ES (row_addr ES x m i) m row)
        (missing_i ES x i 0 n m rows))
      (full ES x n m (replace_Znth i row rows)) := by
  exact store_array_missing_i_merge_to_array CRules (List ES.A)
    (row_store ES m) x i n row rows h

theorem mixed_full_split_to_mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n m : Int) (rows : List (List (Option ES.A)))
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (mixed_full ES x n m rows)
      (CRules.sepcon
        (ArrayLib.mixed_full ES (row_addr ES x m i) m (Znth i rows []))
        (mixed_missing_i ES x i 0 n m rows)) := by
  exact store_array_split_to_missing_i CRules (List (Option ES.A))
    (mixed_row_store ES m) x i n rows [] h

theorem mixed_missing_i_merge_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n m : Int) (rows : List (List (Option ES.A)))
    (row : List (Option ES.A)) (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon
        (ArrayLib.mixed_full ES (row_addr ES x m i) m row)
        (mixed_missing_i ES x i 0 n m rows))
      (mixed_full ES x n m (replace_Znth i row rows)) := by
  exact store_array_missing_i_merge_to_array CRules (List (Option ES.A))
    (mixed_row_store ES m) x i n row rows h

theorem undef_full_split_to_undef_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n m : Int) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (undef_full ES x n m)
      (CRules.sepcon (ArrayLib.undef_full ES (row_addr ES x m i) m)
        (undef_missing_i ES x i 0 n m)) := by
  simpa only [undef_full, undef_row_store, undef_missing_i, Int.sub_zero] using
    store_undef_array_split_to_missing_i CRules
      (undef_row_store ES m) x i n h

theorem full_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (rows : List (List ES.A)) :
    CRules.derivable1 (full ES x n m rows) (undef_full ES x n m) := by
  exact store_array_to_undef_array CRules (List ES.A)
    (row_store ES m) (undef_row_store ES m)
    (fun x i row => row_store_to_undef_row_store ES x m i row) x n rows

theorem mixed_full_to_undef_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_full ES x n m rows) (undef_full ES x n m) := by
  exact store_array_to_undef_array CRules (List (Option ES.A))
    (mixed_row_store ES m) (undef_row_store ES m)
    (fun x i row => mixed_row_store_to_undef_row_store ES x m i row) x n rows

theorem undef_full_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n m : Int) :
    CRules.derivable1 (undef_full ES x n m) (CRules.coq_prop (0 <= n)) := by
  intro _ hs
  change 0 <= n
  by_cases hn : 0 <= n
  · exact hn
  · have hzero : n.toNat = 0 := by omega
    simp only [undef_full, store_undef_array, hzero,
      store_undef_array_rec] at hs
    change 0 = n ∧ _ at hs
    omega

end Array2Lib

end Array2LibCoreSig

end SimpleC.SL.Array2LibCore
