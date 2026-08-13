import SimpleC.SL.ArrayLib

namespace SimpleC.SL.PtrArray2LibCore

open AUXLib
open SimpleC.SL.ArrayLib
open SimpleC.SL.ArrayLib.ArrayLibSig
open SimpleC.SL.ArrayLibCore
open SimpleC.SL.ArrayLibCore.ArrayLibCoreSig
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.Mem
open SimpleC.SL.StoreAux
open SimpleC.SL.StoreAux.StoreLibSig
open Unifysl.LogicGenerator.demo932
open scoped SimpleC.SL.SAC

structure PtrArray2LibCoreSig
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _CRules)
    (_SLibSig : StoreLibSig _CRules _DePredSig)
    (_ALibSig : ArrayLibSig _CRules _DePredSig _SLibSig) : Type where

namespace PtrArray2LibCoreSig

def canonical (CRules : SeparationLogicSig)
    (DePredSig : DerivedPredSig CRules)
    (SLibSig : StoreLibSig CRules DePredSig)
    (ALibSig : ArrayLibSig CRules DePredSig SLibSig) :
    PtrArray2LibCoreSig CRules DePredSig SLibSig ALibSig := {}

namespace PtrArray2Lib

variable {CRules : SeparationLogicSig}
variable {DePredSig : DerivedPredSig CRules}
variable {SLibSig : StoreLibSig CRules DePredSig}

def remove_Znth {B : Type} (i : Int) (l : List B) : List B :=
  firstn i.toNat l ++ skipn (Nat.succ i.toNat) l

theorem replace_nth_decomp {B : Type} (n : Nat) (l : List B) (v : B)
    (h : n < l.length) :
    replace_nth n l v = firstn n l ++ v :: skipn (Nat.succ n) l := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
      cases n with
      | zero => simp [replace_nth, firstn, skipn]
      | succ n =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simp only [replace_nth, firstn, skipn]
          exact congrArg (fun ys => x :: ys) (ih n h)

theorem replace_Znth_decomp {B : Type} (i : Int) (l : List B) (v : B)
    (h : 0 <= i ∧ i < Zlength l) :
    replace_Znth i v l =
      firstn i.toNat l ++ v :: skipn (Nat.succ i.toNat) l := by
  unfold replace_Znth
  apply replace_nth_decomp
  apply Int.ofNat_lt.mp
  rw [Int.toNat_of_nonneg h.1]
  exact h.2

theorem Znth_combine {B C : Type} (i : Int) (l1 : List B) (l2 : List C)
    (d1 : B) (d2 : C) (hi : 0 <= i ∧ i < Zlength l1)
    (hlen : Zlength l1 = Zlength l2) :
    Znth i (combine l1 l2) (d1, d2) =
      (Znth i l1 d1, Znth i l2 d2) := by
  induction l1 generalizing i l2 with
  | nil =>
      simp [Zlength] at hi
      omega
  | cons b l1 ih =>
      cases l2 with
      | nil =>
          simp [Zlength] at hlen
          omega
      | cons c l2 =>
          by_cases hzero : i = 0
          · subst i
            simp [combine, Znth]
          · have hpos : i > 0 := by omega
            change Znth i ((b, c) :: combine l1 l2) (d1, d2) =
              (Znth i (b :: l1) d1, Znth i (c :: l2) d2)
            rw [Znth_cons (d1, d2) i (b, c) (combine l1 l2) hpos]
            rw [Znth_cons d1 i b l1 hpos]
            rw [Znth_cons d2 i c l2 hpos]
            apply ih (i := i - 1) (l2 := l2)
            · simp only [Zlength_cons] at hi
              omega
            · simp only [Zlength_cons] at hlen
              omega

theorem combine_replace_Znth_r {B C : Type} (i : Int)
    (l1 : List B) (l2 : List C) (d1 : B) (v : C)
    (hi : 0 <= i ∧ i < Zlength l1)
    (hlen : Zlength l1 = Zlength l2) :
    combine l1 (replace_Znth i v l2) =
      replace_Znth i (Znth i l1 d1, v) (combine l1 l2) := by
  induction l1 generalizing i l2 with
  | nil =>
      simp [Zlength] at hi
      omega
  | cons b l1 ih =>
      cases l2 with
      | nil =>
          simp [Zlength] at hlen
          omega
      | cons c l2 =>
          by_cases hzero : i = 0
          · subst i
            rfl
          · have hpos : i > 0 := by omega
            rw [replace_Znth_cons i v c l2 hpos]
            change combine (b :: l1) (c :: replace_Znth (i - 1) v l2) =
              replace_Znth i (Znth i (b :: l1) d1, v)
                ((b, c) :: combine l1 l2)
            rw [replace_Znth_cons i (Znth i (b :: l1) d1, v)
              (b, c) (combine l1 l2) hpos]
            rw [Znth_cons d1 i b l1 hpos]
            exact congrArg (fun ys => (b, c) :: ys)
              (ih (i := i - 1) (l2 := l2) (by
                simp only [Zlength_cons] at hi
                omega) (by
                simp only [Zlength_cons] at hlen
                omega))

theorem single_to_iter_sepcon (CRules : SeparationLogicSig) (P : CRules.expr) :
    CRules.derivable1 P (CRules.toContext.iter_sepcon [P]) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_emp_r P)
    (CRules.toContext.derivable1_sepcon_comm P CRules.emp)

private theorem iter_sepcon_single_to (CRules : SeparationLogicSig)
    (P : CRules.expr) :
    CRules.derivable1 (CRules.toContext.iter_sepcon [P]) P := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_comm CRules.emp P)
    (CRules.toContext.derivable1_sepcon_emp_l P)

private theorem logic_equiv_sepcon_swap_middle (CRules : SeparationLogicSig)
    (P Q R : CRules.expr) :
    CRules.logic_equiv
      (CRules.sepcon P (CRules.sepcon Q R))
      (CRules.sepcon (CRules.sepcon P R) Q) := by
  constructor
  · exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.logic_equiv_sepcon_assoc P Q R).left <|
      CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.derivable1_sepcon_comm (CRules.sepcon P Q) R) <|
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.logic_equiv_sepcon_assoc R P Q).left <|
          CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_sepcon_comm R P)
            (CRules.toContext.derivable1_refl Q)
  · exact CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_sepcon_comm P R)
        (CRules.toContext.derivable1_refl Q)) <|
      CRules.toContext.derivable1_trans _ _ _
        (CRules.toContext.logic_equiv_sepcon_assoc R P Q).right <|
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_comm R (CRules.sepcon P Q)) <|
          (CRules.toContext.logic_equiv_sepcon_assoc P Q R).right

private theorem iter_sepcon_extract_middle_left (CRules : SeparationLogicSig)
    (xs zs : List CRules.expr) (P : CRules.expr) :
    CRules.derivable1
      (CRules.toContext.iter_sepcon (xs ++ P :: zs))
      (CRules.sepcon P (CRules.toContext.iter_sepcon (xs ++ zs))) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_iter_sepcon2 xs (P :: zs)) <|
    CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl _)
        (CRules.toContext.derivable1_sepcon_iter_sepcon2 [P] zs)) <|
      CRules.toContext.derivable1_trans _ _ _
        (logic_equiv_sepcon_swap_middle CRules _ _ _).left <|
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_sepcon_iter_sepcon1 xs zs)
            (iter_sepcon_single_to CRules P))
          (CRules.toContext.derivable1_sepcon_comm _ P)

private theorem iter_sepcon_insert_middle_left (CRules : SeparationLogicSig)
    (xs zs : List CRules.expr) (P : CRules.expr) :
    CRules.derivable1
      (CRules.sepcon P (CRules.toContext.iter_sepcon (xs ++ zs)))
      (CRules.toContext.iter_sepcon (xs ++ P :: zs)) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.derivable1_sepcon_comm P _) <|
    CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_sepcon_iter_sepcon2 xs zs)
        (single_to_iter_sepcon CRules P)) <|
      CRules.toContext.derivable1_trans _ _ _
        (logic_equiv_sepcon_swap_middle CRules _ _ _).right <|
        CRules.toContext.derivable1_trans _ _ _
          (CRules.toContext.derivable1_sepcon_mono _ _ _ _
            (CRules.toContext.derivable1_refl _)
            (CRules.toContext.derivable1_sepcon_iter_sepcon1 [P] zs))
          (CRules.toContext.derivable1_sepcon_iter_sepcon1 xs (P :: zs))

theorem iter_sepcon_split_remove_Znth (CRules : SeparationLogicSig)
    {B : Type} (P : B -> CRules.expr) (i : Int) (l : List B) (d : B)
    (h : 0 <= i ∧ i < Zlength l) :
    CRules.derivable1 (CRules.toContext.iter_sepcon (l.map P))
      (CRules.sepcon (P (Znth i l d))
        (CRules.toContext.iter_sepcon ((remove_Znth i l).map P))) := by
  have hnat : i.toNat < l.length := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg h.1]
    exact h.2
  have hdecomp := firstn_skipSn d i.toNat l hnat
  have hmapDecomp : l.map P =
      List.map P (firstn i.toNat l) ++
        P (nth i.toNat l d) :: List.map P (skipn i.toNat.succ l) := by
    calc
      l.map P =
          (firstn i.toNat l ++ nth i.toNat l d :: skipn i.toNat.succ l).map P :=
        congrArg (List.map P) hdecomp
      _ = List.map P (firstn i.toNat l) ++
          P (nth i.toNat l d) :: List.map P (skipn i.toNat.succ l) := by
        simp only [List.map_append, List.map_cons]
  rw [hmapDecomp]
  simp only [remove_Znth, Znth, List.map_append]
  exact iter_sepcon_extract_middle_left CRules
    (List.map P (firstn i.toNat l))
    (List.map P (skipn i.toNat.succ l))
    (P (nth i.toNat l d))

theorem iter_sepcon_merge_remove_Znth (CRules : SeparationLogicSig)
    {B : Type} (P : B -> CRules.expr) (i : Int) (l : List B) (v : B)
    (h : 0 <= i ∧ i < Zlength l) :
    CRules.derivable1
      (CRules.sepcon (P v)
        (CRules.toContext.iter_sepcon ((remove_Znth i l).map P)))
      (CRules.toContext.iter_sepcon ((replace_Znth i v l).map P)) := by
  rw [replace_Znth_decomp i l v h]
  simp only [List.map_append, List.map_cons, remove_Znth]
  exact iter_sepcon_insert_middle_left CRules
    (List.map P (firstn i.toNat l))
    (List.map P (skipn i.toNat.succ l)) (P v)

def row_block (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (pr : addr × List ES.A) : CRules.expr :=
  ArrayLib.full ES pr.1 (Zlength pr.2) pr.2

def mixed_row_block (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (pr : addr × List (Option ES.A)) : CRules.expr :=
  ArrayLib.mixed_full ES pr.1 (Zlength pr.2) pr.2

def row_blocks (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (row_ptrs : List Int) (rows : List (List ES.A)) : CRules.expr :=
  CRules.toContext.iter_sepcon ((combine row_ptrs rows).map (row_block ES))

def mixed_row_blocks (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (row_ptrs : List Int) (rows : List (List (Option ES.A))) : CRules.expr :=
  CRules.toContext.iter_sepcon
    ((combine row_ptrs rows).map (mixed_row_block ES))

def row_blocks_missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (i : Int) (row_ptrs : List Int) (rows : List (List ES.A)) : CRules.expr :=
  CRules.toContext.iter_sepcon
    ((remove_Znth i (combine row_ptrs rows)).map (row_block ES))

def mixed_row_blocks_missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (i : Int) (row_ptrs : List Int)
    (rows : List (List (Option ES.A))) : CRules.expr :=
  CRules.toContext.iter_sepcon
    ((remove_Znth i (combine row_ptrs rows)).map (mixed_row_block ES))

noncomputable def full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) (rows : List (List ES.A)) : CRules.expr :=
  CRules.exp (List Int) fun row_ptrs =>
    CRules.andp
      (CRules.coq_prop (Zlength row_ptrs = n ∧ Zlength rows = n))
      (CRules.sepcon
        ((PtrArray CRules DePredSig SLibSig).full x n row_ptrs)
        (row_blocks ES row_ptrs rows))

noncomputable def missing_i (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n i row_ptr : Int) (rows : List (List ES.A)) : CRules.expr :=
  CRules.exp (List Int) fun row_ptrs =>
    CRules.andp
      (CRules.coq_prop
        (Zlength row_ptrs = n ∧ Zlength rows = n ∧
          row_ptr = Znth i row_ptrs 0))
      (CRules.sepcon
        ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n row_ptrs)
        (row_blocks_missing_i ES i row_ptrs rows))

noncomputable def mixed_full (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) (rows : List (List (Option ES.A))) : CRules.expr :=
  CRules.exp (List Int) fun row_ptrs =>
    CRules.andp
      (CRules.coq_prop (Zlength row_ptrs = n ∧ Zlength rows = n))
      (CRules.sepcon
        ((PtrArray CRules DePredSig SLibSig).full x n row_ptrs)
        (mixed_row_blocks ES row_ptrs rows))

noncomputable def mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n i row_ptr : Int)
    (rows : List (List (Option ES.A))) : CRules.expr :=
  CRules.exp (List Int) fun row_ptrs =>
    CRules.andp
      (CRules.coq_prop
        (Zlength row_ptrs = n ∧ Zlength rows = n ∧
          row_ptr = Znth i row_ptrs 0))
      (CRules.sepcon
        ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n row_ptrs)
        (mixed_row_blocks_missing_i ES i row_ptrs rows))

noncomputable def undef_full (_ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x : addr) (n : Int) : CRules.expr :=
  (PtrArray CRules DePredSig SLibSig).undef_full x n

theorem full_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (rows : List (List ES.A)) :
    CRules.derivable1 (full ES x n rows)
      (CRules.coq_prop (Zlength rows = n)) := by
  intro state
  rintro ⟨_rowPtrs, hlen, _hspatial⟩
  exact hlen.2

theorem mixed_full_Zlength (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) (rows : List (List (Option ES.A))) :
    CRules.derivable1 (mixed_full ES x n rows)
      (CRules.coq_prop (Zlength rows = n)) := by
  intro state
  rintro ⟨_rowPtrs, hlen, _hspatial⟩
  exact hlen.2

theorem undef_full_valid (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x n : Int) :
    CRules.derivable1 (undef_full ES x n) (CRules.coq_prop (0 <= n)) := by
  exact (PtrArray CRules DePredSig SLibSig).undef_full_valid x n

theorem Zlength_combine_eq {B C : Type} (l1 : List B) (l2 : List C)
    (h : Zlength l1 = Zlength l2) :
    Zlength (combine l1 l2) = Zlength l1 := by
  unfold Zlength at h ⊢
  have hnat : l1.length = l2.length := Int.ofNat.inj h
  simp only [combine, List.length_zip, hnat, Nat.min_self]

theorem row_blocks_split_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (i : Int) (row_ptrs : List Int) (rows : List (List ES.A))
    (hi : 0 <= i ∧ i < Zlength row_ptrs)
    (hlen : Zlength row_ptrs = Zlength rows) :
    CRules.derivable1 (row_blocks ES row_ptrs rows)
      (CRules.sepcon
        (ArrayLib.full ES (Znth i row_ptrs 0)
          (Zlength (Znth i rows [])) (Znth i rows []))
        (row_blocks_missing_i ES i row_ptrs rows)) := by
  have hcombine : 0 <= i ∧ i < Zlength (combine row_ptrs rows) := by
    rw [Zlength_combine_eq row_ptrs rows hlen]
    exact hi
  have hsplit := iter_sepcon_split_remove_Znth CRules (row_block ES) i
    (combine row_ptrs rows) (0, []) hcombine
  have hselected := Znth_combine i row_ptrs rows 0 [] hi hlen
  simpa only [row_blocks, row_blocks_missing_i, row_block, hselected] using hsplit

theorem mixed_row_blocks_split_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (i : Int) (row_ptrs : List Int)
    (rows : List (List (Option ES.A)))
    (hi : 0 <= i ∧ i < Zlength row_ptrs)
    (hlen : Zlength row_ptrs = Zlength rows) :
    CRules.derivable1 (mixed_row_blocks ES row_ptrs rows)
      (CRules.sepcon
        (ArrayLib.mixed_full ES (Znth i row_ptrs 0)
          (Zlength (Znth i rows [])) (Znth i rows []))
        (mixed_row_blocks_missing_i ES i row_ptrs rows)) := by
  have hcombine : 0 <= i ∧ i < Zlength (combine row_ptrs rows) := by
    rw [Zlength_combine_eq row_ptrs rows hlen]
    exact hi
  have hsplit := iter_sepcon_split_remove_Znth CRules (mixed_row_block ES) i
    (combine row_ptrs rows) (0, []) hcombine
  have hselected := Znth_combine i row_ptrs rows 0 [] hi hlen
  simpa only [mixed_row_blocks, mixed_row_blocks_missing_i,
    mixed_row_block, hselected] using hsplit

theorem row_blocks_missing_i_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (i : Int) (row_ptrs : List Int) (rows : List (List ES.A))
    (row : List ES.A) (hi : 0 <= i ∧ i < Zlength row_ptrs)
    (hlen : Zlength row_ptrs = Zlength rows) :
    CRules.derivable1
      (CRules.sepcon
        (ArrayLib.full ES (Znth i row_ptrs 0) (Zlength row) row)
        (row_blocks_missing_i ES i row_ptrs rows))
      (row_blocks ES row_ptrs (replace_Znth i row rows)) := by
  have hcombine : 0 <= i ∧ i < Zlength (combine row_ptrs rows) := by
    rw [Zlength_combine_eq row_ptrs rows hlen]
    exact hi
  have hmerge := iter_sepcon_merge_remove_Znth CRules (row_block ES) i
    (combine row_ptrs rows) (Znth i row_ptrs 0, row) hcombine
  have hreplace := combine_replace_Znth_r i row_ptrs rows 0 row hi hlen
  simpa only [row_blocks, row_blocks_missing_i, row_block, hreplace] using hmerge

theorem mixed_row_blocks_missing_i_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (i : Int) (row_ptrs : List Int)
    (rows : List (List (Option ES.A))) (row : List (Option ES.A))
    (hi : 0 <= i ∧ i < Zlength row_ptrs)
    (hlen : Zlength row_ptrs = Zlength rows) :
    CRules.derivable1
      (CRules.sepcon
        (ArrayLib.mixed_full ES (Znth i row_ptrs 0) (Zlength row) row)
        (mixed_row_blocks_missing_i ES i row_ptrs rows))
      (mixed_row_blocks ES row_ptrs (replace_Znth i row rows)) := by
  have hcombine : 0 <= i ∧ i < Zlength (combine row_ptrs rows) := by
    rw [Zlength_combine_eq row_ptrs rows hlen]
    exact hi
  have hmerge := iter_sepcon_merge_remove_Znth CRules (mixed_row_block ES) i
    (combine row_ptrs rows) (Znth i row_ptrs 0, row) hcombine
  have hreplace := combine_replace_Znth_r i row_ptrs rows 0 row hi hlen
  simpa only [mixed_row_blocks, mixed_row_blocks_missing_i,
    mixed_row_block, hreplace] using hmerge

private theorem sepcon_interchange (CRules : SeparationLogicSig)
    (P Q R S : CRules.expr) :
    CRules.derivable1
      (CRules.sepcon (CRules.sepcon P Q) (CRules.sepcon R S))
      (CRules.sepcon (CRules.sepcon P R) (CRules.sepcon Q S)) := by
  exact CRules.toContext.derivable1_trans _ _ _
    (CRules.toContext.logic_equiv_sepcon_assoc P Q
      (CRules.sepcon R S)).right <|
    CRules.toContext.derivable1_trans _ _ _
      (CRules.toContext.derivable1_sepcon_mono _ _ _ _
        (CRules.toContext.derivable1_refl P)
        (CRules.toContext.derivable1_trans _ _ _
          (logic_equiv_sepcon_swap_middle CRules Q R S).left
          (CRules.toContext.derivable1_sepcon_comm
            (CRules.sepcon Q S) R)))
      (CRules.toContext.logic_equiv_sepcon_assoc P R
        (CRules.sepcon Q S)).left

theorem full_split_to_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n : Int) (rows : List (List ES.A)) (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (full ES x n rows)
      (CRules.exp Int fun row_ptr =>
        CRules.sepcon
          (CRules.sepcon
            ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i row_ptr)
            (ArrayLib.full ES row_ptr (Zlength (Znth i rows []))
              (Znth i rows [])))
          (missing_i ES x n i row_ptr rows)) := by
  intro state
  rintro ⟨row_ptrs, hrowPtrs, hspatial⟩
  rcases hrowPtrs with ⟨hrowPtrs, hrows⟩
  have hiPtrs : 0 <= i ∧ i < Zlength row_ptrs := by omega
  have hlenRows : Zlength row_ptrs = Zlength rows := by omega
  have hptr := (PtrArray CRules DePredSig SLibSig).full_split_to_missing_i
    x i n row_ptrs (0 : Int) h
  have hrow := row_blocks_split_to_missing_i
    ES i row_ptrs rows hiPtrs hlenRows
  have hsplit := CRules.toContext.derivable1_sepcon_mono _ _ _ _ hptr hrow
    state hspatial
  have hreordered := sepcon_interchange CRules _ _ _ _ state hsplit
  refine ⟨Znth i row_ptrs 0, ?_⟩
  apply CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (CRules.toContext.derivable1_refl _) _ state hreordered
  intro innerState hinner
  exact ⟨row_ptrs, ⟨hrowPtrs, hrows, rfl⟩, hinner⟩

theorem missing_i_merge_to_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n row_ptr : Int) (rows : List (List ES.A)) (row : List ES.A)
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon
        (CRules.sepcon
          ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i row_ptr)
          (ArrayLib.full ES row_ptr (Zlength row) row))
        (missing_i ES x n i row_ptr rows))
      (full ES x n (replace_Znth i row rows)) := by
  intro state
  rintro ⟨s1, s2, hjoin, hstoreElem, hmissing⟩
  rcases hmissing with ⟨row_ptrs, hrowPtrs, hptrRows⟩
  rcases hrowPtrs with ⟨hrowPtrs, hrows, hrowPtr⟩
  subst row_ptr
  have hiPtrs : 0 <= i ∧ i < Zlength row_ptrs := by omega
  have hlenRows : Zlength row_ptrs = Zlength rows := by omega
  have hfour : CRules.sepcon
      (CRules.sepcon
        ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i
          (Znth i row_ptrs (0 : Int)))
        (ArrayLib.full ES (Znth i row_ptrs (0 : Int)) (Zlength row) row))
      (CRules.sepcon
        ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n row_ptrs)
        (row_blocks_missing_i ES i row_ptrs rows)) state :=
    ⟨s1, s2, hjoin, hstoreElem, hptrRows⟩
  have hreordered := sepcon_interchange CRules
    ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i
      (Znth i row_ptrs (0 : Int)))
    (ArrayLib.full ES (Znth i row_ptrs (0 : Int)) (Zlength row) row)
    ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n row_ptrs)
    (row_blocks_missing_i ES i row_ptrs rows) state hfour
  have hptr := (PtrArray CRules DePredSig SLibSig).missing_i_merge_to_full
    x i n (Znth i row_ptrs (0 : Int)) row_ptrs h
  have hrow := row_blocks_missing_i_merge_to_full
    ES i row_ptrs rows row hiPtrs hlenRows
  have hspatial := CRules.toContext.derivable1_sepcon_mono _ _ _ _ hptr hrow
    state hreordered
  rw [replace_Znth_Znth i row_ptrs (0 : Int)] at hspatial
  refine ⟨row_ptrs, ?_, hspatial⟩
  exact ⟨hrowPtrs, by simpa only [Zlength_replace_Znth] using hrows⟩

theorem mixed_full_split_to_mixed_missing_i
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n : Int) (rows : List (List (Option ES.A)))
    (h : 0 <= i ∧ i < n) :
    CRules.derivable1 (mixed_full ES x n rows)
      (CRules.exp Int fun row_ptr =>
        CRules.sepcon
          (CRules.sepcon
            ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i row_ptr)
            (ArrayLib.mixed_full ES row_ptr (Zlength (Znth i rows []))
              (Znth i rows [])))
          (mixed_missing_i ES x n i row_ptr rows)) := by
  intro state
  rintro ⟨row_ptrs, hrowPtrs, hspatial⟩
  rcases hrowPtrs with ⟨hrowPtrs, hrows⟩
  have hiPtrs : 0 <= i ∧ i < Zlength row_ptrs := by omega
  have hlenRows : Zlength row_ptrs = Zlength rows := by omega
  have hptr := (PtrArray CRules DePredSig SLibSig).full_split_to_missing_i
    x i n row_ptrs (0 : Int) h
  have hrow := mixed_row_blocks_split_to_missing_i
    ES i row_ptrs rows hiPtrs hlenRows
  have hsplit := CRules.toContext.derivable1_sepcon_mono _ _ _ _ hptr hrow
    state hspatial
  have hreordered := sepcon_interchange CRules _ _ _ _ state hsplit
  refine ⟨Znth i row_ptrs 0, ?_⟩
  apply CRules.toContext.derivable1_sepcon_mono _ _ _ _
    (CRules.toContext.derivable1_refl _) _ state hreordered
  intro innerState hinner
  exact ⟨row_ptrs, ⟨hrowPtrs, hrows, rfl⟩, hinner⟩

theorem mixed_missing_i_merge_to_mixed_full
    (ES : ELEMENT_STORE CRules DePredSig SLibSig)
    (x i n row_ptr : Int) (rows : List (List (Option ES.A)))
    (row : List (Option ES.A)) (h : 0 <= i ∧ i < n) :
    CRules.derivable1
      (CRules.sepcon
        (CRules.sepcon
          ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i row_ptr)
          (ArrayLib.mixed_full ES row_ptr (Zlength row) row))
        (mixed_missing_i ES x n i row_ptr rows))
      (mixed_full ES x n (replace_Znth i row rows)) := by
  intro state
  rintro ⟨s1, s2, hjoin, hstoreElem, hmissing⟩
  rcases hmissing with ⟨row_ptrs, hrowPtrs, hptrRows⟩
  rcases hrowPtrs with ⟨hrowPtrs, hrows, hrowPtr⟩
  subst row_ptr
  have hiPtrs : 0 <= i ∧ i < Zlength row_ptrs := by omega
  have hlenRows : Zlength row_ptrs = Zlength rows := by omega
  have hfour : CRules.sepcon
      (CRules.sepcon
        ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i
          (Znth i row_ptrs (0 : Int)))
        (ArrayLib.mixed_full ES (Znth i row_ptrs (0 : Int)) (Zlength row) row))
      (CRules.sepcon
        ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n row_ptrs)
        (mixed_row_blocks_missing_i ES i row_ptrs rows)) state :=
    ⟨s1, s2, hjoin, hstoreElem, hptrRows⟩
  have hreordered := sepcon_interchange CRules
    ((StorePtrAsElement CRules DePredSig SLibSig).storeA x i
      (Znth i row_ptrs (0 : Int)))
    (ArrayLib.mixed_full ES (Znth i row_ptrs (0 : Int)) (Zlength row) row)
    ((PtrArray CRules DePredSig SLibSig).missing_i x i 0 n row_ptrs)
    (mixed_row_blocks_missing_i ES i row_ptrs rows) state hfour
  have hptr := (PtrArray CRules DePredSig SLibSig).missing_i_merge_to_full
    x i n (Znth i row_ptrs (0 : Int)) row_ptrs h
  have hrow := mixed_row_blocks_missing_i_merge_to_full
    ES i row_ptrs rows row hiPtrs hlenRows
  have hspatial := CRules.toContext.derivable1_sepcon_mono _ _ _ _ hptr hrow
    state hreordered
  rw [replace_Znth_Znth i row_ptrs (0 : Int)] at hspatial
  refine ⟨row_ptrs, ?_, hspatial⟩
  exact ⟨hrowPtrs, by simpa only [Zlength_replace_Znth] using hrows⟩

end PtrArray2Lib

end PtrArray2LibCoreSig

end SimpleC.SL.PtrArray2LibCore
