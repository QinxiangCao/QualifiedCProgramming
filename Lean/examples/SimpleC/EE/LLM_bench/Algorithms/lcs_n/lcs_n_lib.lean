import Mathlib.Data.List.Induction
import MaxMinLib.Interface
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
open AUXLib

-- Constructor spellings emitted by symexec for the Coq option interface.
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none

def LCSNCellIndex (n row col : Int) : Int := row * (n + 1) + col

def LCSNCellRecurrence (xs ys table : List Int) (n row col : Int) : Prop :=
  ((row = 0 ∨ col = 0) ∧ Znth (LCSNCellIndex n row col) table 0 = 0) ∨
  (0 < row ∧ 0 < col ∧
    ((Znth (row - 1) xs 0 = Znth (col - 1) ys 0 ∧
       Znth (LCSNCellIndex n row col) table 0 =
         Znth (LCSNCellIndex n (row - 1) (col - 1)) table 0 + 1) ∨
     (Znth (row - 1) xs 0 ≠ Znth (col - 1) ys 0 ∧
       Znth (LCSNCellIndex n row col) table 0 =
         max (Znth (LCSNCellIndex n (row - 1) col) table 0)
           (Znth (LCSNCellIndex n row (col - 1)) table 0))))

def LCSNTableResult (xs ys : List Int) (n : Int) (table : List Int) : Prop :=
  Zlength table = (n + 1) * (n + 1) ∧ ∀ row col,
    (0 ≤ row ∧ row ≤ n) → (0 ≤ col ∧ col ≤ n) →
    LCSNCellRecurrence xs ys table n row col

def LCSNLogicalTableShape (mixed : List (Option Int)) (table : List Int) (n : Int) : Prop :=
  Zlength mixed = (n + 1) * (n + 1) ∧ Zlength table = (n + 1) * (n + 1)

def LCSNCellInitialized (mixed : List (Option Int)) (table : List Int) (n row col : Int) : Prop :=
  Znth (LCSNCellIndex n row col) mixed none = some (Znth (LCSNCellIndex n row col) table 0)

def LCSNBoundaryCell (mixed : List (Option Int)) (table : List Int) (n row col : Int) : Prop :=
  LCSNCellInitialized mixed table n row col ∧ Znth (LCSNCellIndex n row col) table 0 = 0

def LCSNInteriorCell (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row col : Int) : Prop :=
  LCSNCellInitialized mixed table n row col ∧ LCSNCellRecurrence xs ys table n row col ∧
    (0 ≤ Znth (LCSNCellIndex n row col) table 0 ∧
     Znth (LCSNCellIndex n row col) table 0 ≤ min row col)

def LCSNCellUndefined (mixed : List (Option Int)) (n row col : Int) : Prop :=
  Znth (LCSNCellIndex n row col) mixed none = none

def LCSNBoundariesReady (mixed : List (Option Int)) (table : List Int) (n : Int) : Prop :=
  (∀ row, (0 ≤ row ∧ row ≤ n) → LCSNBoundaryCell mixed table n row 0) ∧
  (∀ col, (0 ≤ col ∧ col ≤ n) → LCSNBoundaryCell mixed table n 0 col)

def LCSNCompletedInteriorRows (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n rows_done : Int) : Prop :=
  ∀ row col, (1 ≤ row ∧ row < rows_done) → (1 ≤ col ∧ col ≤ n) →
    LCSNInteriorCell xs ys mixed table n row col

def LCSNInteriorRowsUndefinedFrom (mixed : List (Option Int)) (n rows_from : Int) : Prop :=
  ∀ row col, (rows_from ≤ row ∧ row ≤ n) → (1 ≤ col ∧ col ≤ n) →
    LCSNCellUndefined mixed n row col

def LCSNColumnProgress (mixed : List (Option Int)) (table : List Int) (n rows_done : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧
  (∀ row, (0 ≤ row ∧ row < rows_done) → LCSNBoundaryCell mixed table n row 0) ∧
  (∀ row, (rows_done ≤ row ∧ row ≤ n) → LCSNCellUndefined mixed n row 0) ∧
  (∀ row col, (0 ≤ row ∧ row ≤ n) → (1 ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n row col)

def LCSNBoundaryProgress (mixed : List (Option Int)) (table : List Int) (n cols_done : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧
  (∀ row, (0 ≤ row ∧ row ≤ n) → LCSNBoundaryCell mixed table n row 0) ∧
  (∀ col, (1 ≤ col ∧ col < cols_done) → LCSNBoundaryCell mixed table n 0 col) ∧
  (∀ col, (cols_done ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n 0 col) ∧
  (∀ row col, (1 ≤ row ∧ row ≤ n) → (1 ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n row col)

def LCSNRowsProgress (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n rows_done : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧ LCSNBoundariesReady mixed table n ∧
  LCSNCompletedInteriorRows xs ys mixed table n rows_done ∧
  LCSNInteriorRowsUndefinedFrom mixed n rows_done

def LCSNRowProgress (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row next_col : Int) : Prop :=
  LCSNLogicalTableShape mixed table n ∧ LCSNBoundariesReady mixed table n ∧
  LCSNCompletedInteriorRows xs ys mixed table n row ∧
  (∀ col, (1 ≤ col ∧ col < next_col) → LCSNInteriorCell xs ys mixed table n row col) ∧
  (∀ col, (next_col ≤ col ∧ col ≤ n) → LCSNCellUndefined mixed n row col) ∧
  LCSNInteriorRowsUndefinedFrom mixed n (row + 1)

private theorem index_bounds (n r c : Int) (hn : 0 ≤ n)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n) :
    0 ≤ LCSNCellIndex n r c ∧ LCSNCellIndex n r c < (n+1)*(n+1) := by
  have h0 := Int.mul_nonneg hr.1 (show 0 ≤ n+1 by omega)
  have h1 := Int.mul_le_mul_of_nonneg_right hr.2 (show 0 ≤ n+1 by omega)
  unfold LCSNCellIndex
  grind

theorem lcsn_cell_index_injective__equal_write_and_row_exit (n r1 c1 r2 c2 : Int)
    (hn : 0 ≤ n) (hr1 : 0 ≤ r1 ∧ r1 ≤ n) (hc1 : 0 ≤ c1 ∧ c1 ≤ n)
    (hr2 : 0 ≤ r2 ∧ r2 ≤ n) (hc2 : 0 ≤ c2 ∧ c2 ≤ n)
    (he : LCSNCellIndex n r1 c1 = LCSNCellIndex n r2 c2) : r1 = r2 ∧ c1 = c2 := by
  unfold LCSNCellIndex at he
  by_cases hlt : r1 < r2
  · have h := Int.mul_le_mul_of_nonneg_right (show r1+1 ≤ r2 by omega) (show 0 ≤ n+1 by omega)
    grind
  · by_cases hgt : r2 < r1
    · have h := Int.mul_le_mul_of_nonneg_right (show r2+1 ≤ r1 by omega) (show 0 ≤ n+1 by omega)
      grind
    · have heq : r1 = r2 := by omega
      exact ⟨heq, by subst r2; omega⟩

theorem lcsn_Znth_replace_other_cell__equal_write_and_row_exit {A : Type} (d : A)
    (l : List A) (n ur uc qr qc : Int) (v : A) (hn : 0 ≤ n)
    (hur : 0 ≤ ur ∧ ur ≤ n) (huc : 0 ≤ uc ∧ uc ≤ n)
    (hqr : 0 ≤ qr ∧ qr ≤ n) (hqc : 0 ≤ qc ∧ qc ≤ n)
    (hl : Zlength l = (n+1)*(n+1)) (hd : ur ≠ qr ∨ uc ≠ qc) :
    Znth (LCSNCellIndex n qr qc) (replace_Znth (LCSNCellIndex n ur uc) v l) d =
      Znth (LCSNCellIndex n qr qc) l d := by
  apply Znth_replace_Znth_Diff
  · rw [hl]; exact index_bounds n ur uc hn hur huc
  · rw [hl]; exact index_bounds n qr qc hn hqr hqc
  · intro he
    have := lcsn_cell_index_injective__equal_write_and_row_exit n ur uc qr qc hn hur huc hqr hqc he
    rcases hd with h | h <;> simp_all

theorem lcsn_boundary_cell_replace_other__equal_write_and_row_exit
    (mixed : List (Option Int)) (table : List Int) (n ur uc qr qc v : Int) (hn : 0 ≤ n)
    (hur : 0 ≤ ur ∧ ur ≤ n) (huc : 0 ≤ uc ∧ uc ≤ n)
    (hqr : 0 ≤ qr ∧ qr ≤ n) (hqc : 0 ≤ qc ∧ qc ≤ n)
    (hm : Zlength mixed = (n+1)*(n+1)) (ht : Zlength table = (n+1)*(n+1))
    (hd : ur ≠ qr ∨ uc ≠ qc) (hp : LCSNBoundaryCell mixed table n qr qc) :
    LCSNBoundaryCell (replace_Znth (LCSNCellIndex n ur uc) (some v) mixed)
      (replace_Znth (LCSNCellIndex n ur uc) v table) n qr qc := by
  unfold LCSNBoundaryCell LCSNCellInitialized at *
  rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n ur uc qr qc (some v) hn hur huc hqr hqc hm hd,
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n ur uc qr qc v hn hur huc hqr hqc ht hd]
  exact hp

private theorem boundary_write_same (mixed : List (Option Int)) (table : List Int)
    (n r c : Int) (hn : 0 ≤ n) (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
    (hm : Zlength mixed = (n+1)*(n+1)) (ht : Zlength table = (n+1)*(n+1)) :
    LCSNBoundaryCell (replace_Znth (LCSNCellIndex n r c) (some 0) mixed)
      (replace_Znth (LCSNCellIndex n r c) 0 table) n r c := by
  unfold LCSNBoundaryCell LCSNCellInitialized
  rw [Znth_replace_Znth_Same none mixed _ _ (by rw [hm]; exact index_bounds n r c hn hr hc),
    Znth_replace_Znth_Same 0 table _ _ (by rw [ht]; exact index_bounds n r c hn hr hc)]
  exact ⟨rfl, rfl⟩

theorem lcsn_column_progress_zero__column_init_update (n : Int) (hn : 0 ≤ n) :
    LCSNColumnProgress (List.replicate ((n+1)*(n+1)).toNat (none : Option Int))
      (List.replicate ((n+1)*(n+1)).toNat (0 : Int)) n 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsq := Int.mul_nonneg (show 0 ≤ n+1 by omega) (show 0 ≤ n+1 by omega)
    simp [LCSNLogicalTableShape, Zlength, Int.toNat_of_nonneg hsq]
  · intro r hr; omega
  · intro r hr; exact Znth_repeat none _ _
  · intro r c hr hc; exact Znth_repeat none _ _

theorem lcsn_column_write_progress__column_init_update (mixed : List (Option Int))
    (table : List Int) (n i stride : Int) (hs : stride = n+1) (hn : 0 ≤ n)
    (hi : 0 ≤ i ∧ i ≤ n) (hp : LCSNColumnProgress mixed table n i) :
    LCSNColumnProgress (replace_Znth (stride*i) (some 0) mixed)
      (replace_Znth (stride*i) 0 table) n (i+1) := by
  subst stride
  have he : (n+1)*i = LCSNCellIndex n i 0 := by unfold LCSNCellIndex; grind
  rw [he]
  rcases hp with ⟨⟨hm,ht⟩, hp,hc,ho⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [Zlength_replace_Znth,hm], by rw [Zlength_replace_Znth,ht]⟩
  · intro r hr
    by_cases heq : r = i
    · subst r; exact boundary_write_same mixed table n i 0 hn hi ⟨by omega,hn⟩ hm ht
    · exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n i 0 r 0 0 hn hi ⟨by omega,hn⟩
        ⟨hr.1, by omega⟩ ⟨by omega,hn⟩ hm ht (Or.inl (Ne.symm heq)) (hp r ⟨hr.1,by omega⟩)
  · intro r hr
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n i 0 r 0 (some 0) hn hi ⟨by omega,hn⟩
      ⟨by omega,hr.2⟩ ⟨by omega,hn⟩ hm (Or.inl (by omega))]
    exact hc r ⟨by omega,hr.2⟩
  · intro r c hr hcol
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n i 0 r c (some 0) hn hi ⟨by omega,hn⟩ hr
      ⟨by omega,hcol.2⟩ hm (Or.inr (by omega))]
    exact ho r c hr hcol

theorem lcsn_column_complete_boundary_start__boundary_phase (mixed : List (Option Int))
    (table : List Int) (n : Int) (hn : 0 ≤ n) (hp : LCSNColumnProgress mixed table n (n+1)) :
    LCSNBoundaryProgress mixed table n 1 := by
  rcases hp with ⟨hs,hc,hu,ho⟩
  exact ⟨hs, fun r hr => hc r ⟨hr.1,by omega⟩, fun c hc => by omega,
    fun c hc => ho 0 c ⟨by omega,hn⟩ hc,
    fun r c hr hc => ho r c ⟨by omega,hr.2⟩ hc⟩

theorem lcsn_boundary_write_progress__boundary_phase (mixed : List (Option Int))
    (table : List Int) (n j : Int) (hj : 1 ≤ j ∧ j ≤ n)
    (hp : LCSNBoundaryProgress mixed table n j) :
    LCSNBoundaryProgress (replace_Znth j (some 0) mixed) (replace_Znth j 0 table) n (j+1) := by
  have hn : 0 ≤ n := by omega
  have he : j = LCSNCellIndex n 0 j := by simp [LCSNCellIndex]
  suffices h : LCSNBoundaryProgress (replace_Znth (LCSNCellIndex n 0 j) (some 0) mixed)
    (replace_Znth (LCSNCellIndex n 0 j) 0 table) n (j+1) by
    simpa only [LCSNCellIndex, Int.zero_mul, Int.zero_add] using h
  rcases hp with ⟨⟨hm,ht⟩,hc,hp,hs,hi⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [Zlength_replace_Znth,hm], by rw [Zlength_replace_Znth,ht]⟩
  · intro r hr
    exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n 0 j r 0 0 hn ⟨by omega,hn⟩
      ⟨by omega,hj.2⟩ hr ⟨by omega,hn⟩ hm ht (Or.inr (by omega)) (hc r hr)
  · intro c hc
    by_cases heq : c = j
    · subst c; exact boundary_write_same mixed table n 0 j hn ⟨by omega,hn⟩ ⟨by omega,hj.2⟩ hm ht
    · exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n 0 j 0 c 0 hn ⟨by omega,hn⟩
        ⟨by omega,hj.2⟩ ⟨by omega,hn⟩ ⟨by omega,by omega⟩ hm ht (Or.inr (Ne.symm heq)) (hp c ⟨hc.1,by omega⟩)
  · intro c hc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n 0 j 0 c (some 0) hn ⟨by omega,hn⟩
      ⟨by omega,hj.2⟩ ⟨by omega,hn⟩ ⟨by omega,hc.2⟩ hm (Or.inr (by omega))]
    exact hs c ⟨by omega,hc.2⟩
  · intro r c hr hc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n 0 j r c (some 0) hn ⟨by omega,hn⟩
      ⟨by omega,hj.2⟩ ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ hm (Or.inl (by omega))]
    exact hi r c hr hc

theorem lcsn_boundaries_complete_rows_start__row_phase_entry (xs ys : List Int)
    (mixed : List (Option Int)) (table : List Int) (n : Int)
    (hp : LCSNBoundaryProgress mixed table n (n+1)) : LCSNRowsProgress xs ys mixed table n 1 := by
  rcases hp with ⟨hs,hc,hr,hu,hi⟩
  refine ⟨hs, ⟨hc, ?_⟩, ?_, hi⟩
  · intro c hcol
    by_cases he : c = 0
    · subst c; exact hc 0 hcol
    · exact hr c ⟨by omega,by omega⟩
  · intro r c hr hc; omega

theorem lcsn_rows_start_row__row_phase_entry (xs ys : List Int) (mixed : List (Option Int))
    (table : List Int) (n row : Int) (hr : row ≤ n)
    (hp : LCSNRowsProgress xs ys mixed table n row) : LCSNRowProgress xs ys mixed table n row 1 := by
  rcases hp with ⟨hs,hb,hc,hu⟩
  exact ⟨hs,hb,hc,fun c hc => by omega,fun c hc => hu row c ⟨by omega,hr⟩ hc,
    fun r c hr hc => hu r c ⟨by omega,hr.2⟩ hc⟩

private theorem replace_nat_as_take_drop {A : Type} (l : List A) (i : Nat) (v : A)
    (hi : i < l.length) : replace_nth i l v = l.take i ++ v :: l.drop (i+1) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [replace_nth] using congrArg (List.cons a) (ih i (by simpa using hi))

theorem lcsn_replace_Znth_as_sublist__equal_write_and_row_exit {A : Type} (d : A)
    (l : List A) (k : Int) (v : A) (hk : 0 ≤ k ∧ k < Zlength l) :
    replace_Znth k v l = sublist 0 k l ++ v :: sublist (k+1) (Zlength l) l := by
  have hk' : k.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hk; omega
  simpa only [replace_Znth, sublist, Int.toNat_zero, List.drop_zero, Zlength,
    Int.ofNat_eq_coe, Int.toNat_natCast, List.take_length, show (k+1).toNat = k.toNat+1 by omega] using
    replace_nat_as_take_drop l k.toNat v hk'

theorem replace_Znth_sublist__max_write {A : Type} (l : List A) (i : Int) (v : A)
    (hi : 0 ≤ i ∧ i < Zlength l) :
    replace_Znth i v l = sublist 0 i l ++ v :: sublist (i+1) (Zlength l) l :=
  lcsn_replace_Znth_as_sublist__equal_write_and_row_exit v l i v hi

theorem lcsn_interior_cell_replace_before__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n ur uc qr qc v : Int)
    (hn : 0 ≤ n) (hur : 1 ≤ ur ∧ ur ≤ n) (huc : 1 ≤ uc ∧ uc ≤ n)
    (hqr : 1 ≤ qr ∧ qr ≤ n) (hqc : 1 ≤ qc ∧ qc ≤ n)
    (hm : Zlength mixed = (n+1)*(n+1)) (ht : Zlength table = (n+1)*(n+1))
    (hb : qr < ur ∨ (qr = ur ∧ qc < uc)) (hp : LCSNInteriorCell xs ys mixed table n qr qc) :
    LCSNInteriorCell xs ys (replace_Znth (LCSNCellIndex n ur uc) (some v) mixed)
      (replace_Znth (LCSNCellIndex n ur uc) v table) n qr qc := by
  have hmread := lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n ur uc qr qc (some v)
    hn ⟨by omega,hur.2⟩ ⟨by omega,huc.2⟩ ⟨by omega,hqr.2⟩ ⟨by omega,hqc.2⟩ hm (by omega)
  have hread (r c : Int) (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
      (hd : ur ≠ r ∨ uc ≠ c) :=
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n ur uc r c v hn
      ⟨by omega,hur.2⟩ ⟨by omega,huc.2⟩ hr hc ht hd
  unfold LCSNInteriorCell LCSNCellInitialized LCSNCellRecurrence at *
  rw [hmread, hread qr qc ⟨by omega,hqr.2⟩ ⟨by omega,hqc.2⟩ (by omega),
    hread (qr-1) (qc-1) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega),
    hread (qr-1) qc ⟨by omega,by omega⟩ ⟨by omega,hqc.2⟩ (by omega),
    hread qr (qc-1) ⟨by omega,hqr.2⟩ ⟨by omega,by omega⟩ (by omega)]
  exact hp

private theorem observed_cell (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row col r c : Int) (hn : 0 ≤ n) (hrow : 1 ≤ row ∧ row ≤ n) (hcol : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n)
    (hb : r < row ∨ (r = row ∧ c < col)) :
    LCSNCellInitialized mixed table n r c ∧
      (0 ≤ Znth (LCSNCellIndex n r c) table 0 ∧ Znth (LCSNCellIndex n r c) table 0 ≤ min r c) := by
  rcases hp with ⟨hs,⟨hbcol,hbrow⟩,hcomp,hpre,hsuf,hfuture⟩
  by_cases hr0 : r = 0
  · subst r
    have h := hbrow c hc
    exact ⟨h.1, by rw [h.2]; omega⟩
  · by_cases hc0 : c = 0
    · subst c
      have h := hbcol r hr
      exact ⟨h.1, by rw [h.2]; omega⟩
    · have h : LCSNInteriorCell xs ys mixed table n r c := by
        rcases hb with hb | ⟨he,hb⟩
        · exact hcomp r c ⟨by omega,hb⟩ ⟨by omega,hc.2⟩
        · subst r; exact hpre c ⟨by omega,hb⟩
      exact ⟨h.1,h.2.2⟩

theorem lcsn_diagonal_successor_bound__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n row col : Int)
    (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col) :
    0 ≤ Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1 ∧
      Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1 ≤ min row col := by
  have h := (observed_cell xs ys mixed table n row col (row-1) (col-1) hn hr hc hp
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (Or.inl (by omega))).2
  omega

private theorem row_write (xs ys : List Int) (mixed : List (Option Int)) (table : List Int)
    (n row col v : Int) (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col) (hv : 0 ≤ v ∧ v ≤ min row col)
    (hrec : LCSNCellRecurrence xs ys (replace_Znth (LCSNCellIndex n row col) v table) n row col) :
    LCSNRowProgress xs ys (replace_Znth (LCSNCellIndex n row col) (some v) mixed)
      (replace_Znth (LCSNCellIndex n row col) v table) n row (col+1) := by
  rcases hp with ⟨⟨hm,ht⟩,⟨hbcol,hbrow⟩,hcomp,hpre,hsuf,hfuture⟩
  have hr0 : 0 ≤ row ∧ row ≤ n := ⟨by omega,hr.2⟩
  have hc0 : 0 ≤ col ∧ col ≤ n := ⟨by omega,hc.2⟩
  refine ⟨⟨by rw [Zlength_replace_Znth,hm],by rw [Zlength_replace_Znth,ht]⟩,⟨?_,?_⟩,?_,?_,?_,?_⟩
  · intro r hrr
    exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n row col r 0 v hn hr0 hc0 hrr
      ⟨by omega,hn⟩ hm ht (Or.inr (by omega)) (hbcol r hrr)
  · intro c hcc
    exact lcsn_boundary_cell_replace_other__equal_write_and_row_exit mixed table n row col 0 c v hn hr0 hc0
      ⟨by omega,hn⟩ hcc hm ht (Or.inl (by omega)) (hbrow c hcc)
  · intro r c hrr hcc
    exact lcsn_interior_cell_replace_before__equal_write_and_row_exit xs ys mixed table n row col r c v hn hr hc
      ⟨hrr.1,by omega⟩ hcc hm ht (Or.inl hrr.2) (hcomp r c hrr hcc)
  · intro c hcc
    by_cases he : c = col
    · subst c
      refine ⟨?_,hrec,?_⟩
      · unfold LCSNCellInitialized
        rw [Znth_replace_Znth_Same none mixed _ _ (by rw [hm]; exact index_bounds n row col hn hr0 hc0),
          Znth_replace_Znth_Same 0 table _ _ (by rw [ht]; exact index_bounds n row col hn hr0 hc0)]
      · rw [Znth_replace_Znth_Same 0 table _ _ (by rw [ht]; exact index_bounds n row col hn hr0 hc0)]
        exact hv
    · exact lcsn_interior_cell_replace_before__equal_write_and_row_exit xs ys mixed table n row col row c v hn hr hc
        hr ⟨hcc.1,by omega⟩ hm ht (Or.inr ⟨rfl,by omega⟩) (hpre c ⟨hcc.1,by omega⟩)
  · intro c hcc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n row col row c (some v) hn hr0 hc0 hr0
      ⟨by omega,hcc.2⟩ hm (Or.inr (by omega))]
    exact hsuf c ⟨by omega,hcc.2⟩
  · intro r c hrr hcc
    unfold LCSNCellUndefined
    rw [lcsn_Znth_replace_other_cell__equal_write_and_row_exit none mixed n row col r c (some v) hn hr0 hc0
      ⟨by omega,hrr.2⟩ ⟨by omega,hcc.2⟩ hm (Or.inl (by omega))]
    exact hfuture r c hrr hcc

theorem lcsn_equal_write_progress__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n row col : Int)
    (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (he : Znth (row-1) xs 0 = Znth (col-1) ys 0)
    (hp : LCSNRowProgress xs ys mixed table n row col) :
    LCSNRowProgress xs ys (replace_Znth (LCSNCellIndex n row col)
      (some (Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1)) mixed)
      (replace_Znth (LCSNCellIndex n row col)
        (Znth (LCSNCellIndex n (row-1) (col-1)) table 0 + 1) table) n row (col+1) := by
  apply row_write xs ys mixed table n row col _ hn hr hc hp
    (lcsn_diagonal_successor_bound__equal_write_and_row_exit xs ys mixed table n row col hn hr hc hp)
  refine Or.inr ⟨by omega,by omega,Or.inl ⟨he,?_⟩⟩
  rw [Znth_replace_Znth_Same 0 table _ _ (by rw [hp.1.2]; exact index_bounds n row col hn ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩),
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n row col (row-1) (col-1) _ hn
      ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hp.1.2 (Or.inl (by omega))]

theorem lcsn_row_finish_progress__equal_write_and_row_exit
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n row next_col : Int)
    (hn : 0 ≤ n) (hr : 1 ≤ row ∧ row ≤ n) (hc : n < next_col ∧ next_col ≤ n+1)
    (hp : LCSNRowProgress xs ys mixed table n row next_col) :
    LCSNRowsProgress xs ys mixed table n (row+1) := by
  rcases hp with ⟨hs,hb,hcomp,hpre,hsuf,hfuture⟩
  refine ⟨hs,hb,?_,hfuture⟩
  intro r c hrr hcc
  by_cases he : r = row
  · subst r; exact hpre c ⟨hcc.1,by omega⟩
  · exact hcomp r c ⟨hrr.1,by omega⟩ hcc

theorem lcsn_max_write_progress__max_write (xs ys : List Int) (mixed : List (Option Int))
    (table : List Int) (n row col : Int) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n row col)
    (hne : Znth (row-1) xs 0 ≠ Znth (col-1) ys 0) :
    LCSNRowProgress xs ys (replace_Znth (LCSNCellIndex n row col)
      (some (max (Znth (LCSNCellIndex n (row-1) col) table 0)
        (Znth (LCSNCellIndex n row (col-1)) table 0))) mixed)
      (replace_Znth (LCSNCellIndex n row col)
        (max (Znth (LCSNCellIndex n (row-1) col) table 0)
          (Znth (LCSNCellIndex n row (col-1)) table 0)) table) n row (col+1) := by
  have hn : 0 ≤ n := by omega
  have ha := (observed_cell xs ys mixed table n row col (row-1) col hn hr hc hp
    ⟨by omega,by omega⟩ ⟨by omega,hc.2⟩ (Or.inl (by omega))).2
  have hl := (observed_cell xs ys mixed table n row col row (col-1) hn hr hc hp
    ⟨by omega,hr.2⟩ ⟨by omega,by omega⟩ (Or.inr ⟨rfl,by omega⟩)).2
  apply row_write xs ys mixed table n row col _ hn hr hc hp (by omega)
  refine Or.inr ⟨by omega,by omega,Or.inr ⟨hne,?_⟩⟩
  rw [Znth_replace_Znth_Same 0 table _ _ (by rw [hp.1.2]; exact index_bounds n row col hn ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩),
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n row col (row-1) col _ hn
      ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ ⟨by omega,by omega⟩ ⟨by omega,hc.2⟩ hp.1.2 (Or.inl (by omega)),
    lcsn_Znth_replace_other_cell__equal_write_and_row_exit 0 table n row col row (col-1) _ hn
      ⟨by omega,hr.2⟩ ⟨by omega,hc.2⟩ ⟨by omega,hr.2⟩ ⟨by omega,by omega⟩ hp.1.2 (Or.inr (by omega))]

theorem lcsn_completed_rows_result__finalize_and_return_index
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n : Int)
    (hn : 0 ≤ n) (hp : LCSNRowsProgress xs ys mixed table n (n+1)) :
    LCSNTableResult xs ys n table := by
  refine ⟨hp.1.2,?_⟩
  intro r c hr hc
  by_cases hr0 : r = 0
  · subst r; exact Or.inl ⟨Or.inl rfl,(hp.2.1.2 c hc).2⟩
  · by_cases hc0 : c = 0
    · subst c; exact Or.inl ⟨Or.inr rfl,(hp.2.1.1 r hr).2⟩
    · exact (hp.2.2.1 r c ⟨by omega,by omega⟩ ⟨by omega,hc.2⟩).2.1

theorem lcsn_diagonal_observation__read_exposure (xs ys : List Int)
    (mixed : List (Option Int)) (table : List Int) (n i j : Int)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n i j) :
    LCSNCellUndefined mixed n i j ∧ LCSNCellInitialized mixed table n (i-1) (j-1) ∧
    (0 ≤ Znth (LCSNCellIndex n (i-1) (j-1)) table 0 ∧ Znth (LCSNCellIndex n (i-1) (j-1)) table 0 ≤ n) := by
  have h := observed_cell xs ys mixed table n i j (i-1) (j-1) (by omega) ⟨hi,hin⟩ ⟨hj,hjn⟩ hp
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (Or.inl (by omega))
  exact ⟨hp.2.2.2.2.1 j ⟨by omega,hjn⟩, h.1, by have := h.2; omega⟩

theorem lcsn_neighbor_observations__read_exposure (xs ys : List Int)
    (mixed : List (Option Int)) (table : List Int) (n i j : Int)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hp : LCSNRowProgress xs ys mixed table n i j) :
    LCSNCellUndefined mixed n i j ∧ LCSNCellInitialized mixed table n (i-1) j ∧
      LCSNCellInitialized mixed table n i (j-1) := by
  exact ⟨hp.2.2.2.2.1 j ⟨by omega,hjn⟩,
    (observed_cell xs ys mixed table n i j (i-1) j (by omega) ⟨hi,hin⟩ ⟨hj,hjn⟩ hp
      ⟨by omega,by omega⟩ ⟨by omega,hjn⟩ (Or.inl (by omega))).1,
    (observed_cell xs ys mixed table n i j i (j-1) (by omega) ⟨hi,hin⟩ ⟨hj,hjn⟩ hp
      ⟨by omega,hin⟩ ⟨by omega,by omega⟩ (Or.inr ⟨rfl,by omega⟩)).1⟩

theorem lcsn_initialized_mixed_full_to_full__finalize_and_return_index
    (xs ys : List Int) (mixed : List (Option Int)) (table : List Int) (n : Int)
    (hn : 0 ≤ n) (hp : LCSNRowsProgress xs ys mixed table n (n+1)) :
    mixed = table.map some := by
  apply List.ext_getElem
  · simp only [List.length_map]
    have hm := hp.1.1
    have ht := hp.1.2
    simp only [Zlength, Int.ofNat_eq_coe] at hm ht
    omega
  · intro idx hidx hmap
    have htable : idx < table.length := by simpa using hmap
    have hsquare : (idx : Int) < (n+1)*(n+1) := by
      rw [← hp.1.1]
      exact Int.ofNat_lt.mpr hidx
    let r := (idx : Int).fdiv (n+1)
    let c := (idx : Int).fmod (n+1)
    have hr0 : 0 ≤ r := Int.fdiv_nonneg (by omega) (by omega)
    have hc0 : 0 ≤ c := Int.fmod_nonneg_of_pos _ (by omega)
    have hc1 : c < n+1 := Int.fmod_lt_of_pos _ (by omega)
    have hdecomp : r*(n+1)+c = (idx : Int) := Int.fdiv_mul_add_fmod _ _
    have hr1 : r ≤ n := by
      by_cases h : r ≤ n
      · exact h
      · have hh := Int.mul_le_mul_of_nonneg_right (show n+1 ≤ r by omega) (show 0 ≤ n+1 by omega)
        omega
    have hinit : LCSNCellInitialized mixed table n r c := by
      by_cases hrz : r = 0
      · rw [hrz]; exact (hp.2.1.2 c ⟨hc0,by omega⟩).1
      · by_cases hcz : c = 0
        · rw [hcz]; exact (hp.2.1.1 r ⟨hr0,hr1⟩).1
        · exact (hp.2.2.1 r c ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).1
    change Znth (r*(n+1)+c) mixed none = some (Znth (r*(n+1)+c) table 0) at hinit
    rw [hdecomp] at hinit
    simp only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem htable, Option.getD_some] at hinit
    simpa only [List.getElem_map] using hinit

end SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n
export lcs_n_lib (Some None LCSNCellIndex LCSNCellRecurrence LCSNTableResult LCSNLogicalTableShape
  LCSNCellInitialized LCSNBoundaryCell LCSNInteriorCell LCSNCellUndefined LCSNBoundariesReady
  LCSNCompletedInteriorRows LCSNInteriorRowsUndefinedFrom LCSNColumnProgress LCSNBoundaryProgress
  LCSNRowsProgress LCSNRowProgress)
end SimpleC.EE.LLM_bench.Algorithms.lcs_n

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
open AUXLib

def LCSNPositionOrder (p q : Int × Int) : Prop := p.1 < q.1 ∧ p.2 < q.2
def LCSNMatching (xs ys : List Int) (rows cols : Int) (pairs : List (Int × Int)) : Prop :=
  Forall (fun p => (0 ≤ p.1 ∧ p.1 < rows) ∧ (0 ≤ p.2 ∧ p.2 < cols) ∧
    Znth p.1 xs 0 = Znth p.2 ys 0) pairs ∧ pairs.Pairwise LCSNPositionOrder
def LCSNLength (xs ys : List Int) (answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset Int.le
    (LCSNMatching xs ys (Zlength xs) (Zlength ys)) (fun pairs => Zlength pairs) answer

end SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n
export lcs_n_lib (LCSNPositionOrder LCSNMatching LCSNLength)
end SimpleC.EE.LLM_bench.Algorithms.lcs_n

namespace SimpleC.EE.LLM_bench.Algorithms.longest_common_sequence
export SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
  (Some None LCSNCellIndex LCSNCellRecurrence LCSNTableResult LCSNLogicalTableShape
   LCSNCellInitialized LCSNBoundaryCell LCSNInteriorCell LCSNCellUndefined LCSNBoundariesReady
   LCSNCompletedInteriorRows LCSNInteriorRowsUndefinedFrom LCSNColumnProgress LCSNBoundaryProgress
   LCSNRowsProgress LCSNRowProgress LCSNPositionOrder LCSNMatching LCSNLength)
end SimpleC.EE.LLM_bench.Algorithms.longest_common_sequence

set_option maxHeartbeats 2000000
namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
open AUXLib

private theorem matching_mono (xs ys : List Int) (r c r' c' : Int)
    (ps : List (Int × Int)) (hr : r ≤ r') (hc : c ≤ c')
    (h : LCSNMatching xs ys r c ps) : LCSNMatching xs ys r' c' ps := by
  refine ⟨Forall.iff_forall_mem.mpr ?_, h.2⟩
  intro p hp
  have hv := h.1.mem hp
  exact ⟨⟨hv.1.1, by omega⟩, ⟨hv.2.1.1, by omega⟩, hv.2.2⟩

private theorem matching_snoc_inv (xs ys : List Int) (r c : Int)
    (ps : List (Int × Int)) (a b : Int)
    (h : LCSNMatching xs ys r c (ps ++ [(a,b)])) :
    (0 ≤ a ∧ a < r) ∧ (0 ≤ b ∧ b < c) ∧ Znth a xs 0 = Znth b ys 0 ∧
    LCSNMatching xs ys a b ps ∧
    (∀ p ∈ ps ++ [(a,b)], p.1 ≤ a ∧ p.2 ≤ b) := by
  have hv := h.1.mem (show (a,b) ∈ ps ++ [(a,b)] by simp)
  have hs := List.pairwise_append.mp h.2
  have hb : ∀ p ∈ ps, LCSNPositionOrder p (a,b) := by
    intro p hp
    exact hs.2.2 p hp (a,b) (by simp)
  refine ⟨hv.1, hv.2.1, hv.2.2, ⟨?_, hs.1⟩, ?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro p hp
    have hh := h.1.mem (List.mem_append_left _ hp)
    have ho := hb p hp
    exact ⟨⟨hh.1.1, ho.1⟩, ⟨hh.2.1.1, ho.2⟩, hh.2.2⟩
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have ho := hb p hp; exact ⟨le_of_lt ho.1, le_of_lt ho.2⟩
    · exact ⟨le_refl _, le_refl _⟩

private theorem matching_snoc (xs ys : List Int) (r c : Int)
    (ps : List (Int × Int)) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (he : Znth r xs 0 = Znth c ys 0) (h : LCSNMatching xs ys r c ps) :
    LCSNMatching xs ys (r+1) (c+1) (ps ++ [(r,c)]) := by
  refine ⟨Forall.iff_forall_mem.mpr ?_, List.pairwise_append.mpr ⟨h.2, by simp, ?_⟩⟩
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have hv := h.1.mem hp
      exact ⟨⟨hv.1.1, by omega⟩, ⟨hv.2.1.1, by omega⟩, hv.2.2⟩
    · exact ⟨⟨hr, by omega⟩, ⟨hc, by omega⟩, he⟩
  · intro p hp q hq
    simp only [List.mem_singleton] at hq
    subst q
    have hv := h.1.mem hp
    exact ⟨hv.1.2, hv.2.1.2⟩

private theorem matching_empty_axis (xs ys : List Int) (r c : Int)
    (ps : List (Int × Int)) (hz : r=0 ∨ c=0) (h : LCSNMatching xs ys r c ps) : ps=[] := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    have hv := h.1.mem (show p ∈ p::ps by simp)
    rcases hz with hz | hz <;> omega

private theorem mismatch_cover (xs ys : List Int) (r c : Int)
    (ps : List (Int × Int)) (he : Znth (r-1) xs 0 ≠ Znth (c-1) ys 0)
    (h : LCSNMatching xs ys r c ps) :
    LCSNMatching xs ys (r-1) c ps ∨ LCSNMatching xs ys r (c-1) ps := by
  induction ps using List.reverseRecOn with
  | nil => exact Or.inl ⟨.nil, by simp⟩
  | append_singleton ps p ih =>
    obtain ⟨a,b⟩ := p
    obtain ⟨ha,hb,hm,hpre,hlast⟩ := matching_snoc_inv xs ys r c ps a b h
    have hor : a < r-1 ∨ b < c-1 := by
      by_cases har : a = r-1
      · have hbc : b ≠ c-1 := by intro hbc; apply he; simpa only [har,hbc] using hm
        exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rcases hor with har | hbc
    · left
      refine ⟨Forall.iff_forall_mem.mpr ?_, h.2⟩
      intro p hp
      have hv := h.1.mem hp
      have hh := hlast p hp
      exact ⟨⟨hv.1.1, by omega⟩, hv.2.1, hv.2.2⟩
    · right
      refine ⟨Forall.iff_forall_mem.mpr ?_, h.2⟩
      intro p hp
      have hv := h.1.mem hp
      have hh := hlast p hp
      exact ⟨hv.1, ⟨hv.2.1.1, by omega⟩, hv.2.2⟩

theorem lcsn_table_cell_optimal (xs ys : List Int) (n : Int) (table : List Int)
    (ht : LCSNTableResult xs ys n table) (r c : Int)
    (hr : 0 ≤ r ∧ r ≤ n) (hc : 0 ≤ c ∧ c ≤ n) :
    MaxMinLib.max_value_of_subset (· ≤ ·) (LCSNMatching xs ys r c)
      (fun ps => Zlength ps) (Znth (LCSNCellIndex n r c) table 0) := by
  have main : ∀ s : Nat, ∀ r c : Int, r+c=s →
      (0 ≤ r ∧ r ≤ n) → (0 ≤ c ∧ c ≤ n) →
      MaxMinLib.max_value_of_subset (· ≤ ·) (LCSNMatching xs ys r c)
        (fun ps => Zlength ps) (Znth (LCSNCellIndex n r c) table 0) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro r c hs hr hc
      obtain ⟨hz,hv⟩ | ⟨hrp,hcp,⟨he,hv⟩ | ⟨he,hv⟩⟩ := ht.2 r c hr hc
      · refine ⟨[], ⟨⟨.nil, by simp⟩, ?_⟩, ?_⟩
        · intro ps hm
          rw [matching_empty_axis xs ys r c ps hz hm]
        · simpa only [Zlength_nil] using hv.symm
      · have hd := ih ((r-1+c-1).toNat) (by omega) (r-1) (c-1)
          (by rw [Int.toNat_of_nonneg (by omega)]; omega) (by omega) (by omega)
        obtain ⟨best, ⟨hbest,hupper⟩, hbval⟩ := hd
        dsimp only at hupper hbval
        refine ⟨best ++ [(r-1,c-1)], ⟨?_, ?_⟩, ?_⟩
        · simpa using matching_snoc xs ys (r-1) (c-1) best (by omega) (by omega) he hbest
        · intro ps hm
          change Zlength ps ≤ Zlength (best ++ [(r-1,c-1)])
          induction ps using List.reverseRecOn with
          | nil => have := Zlength_nonneg best; simp only [Zlength_nil, Zlength_app, Zlength_cons]; omega
          | append_singleton pre p hip =>
            obtain ⟨a,b⟩ := p
            obtain ⟨ha,hb,_,hp,_⟩ := matching_snoc_inv xs ys r c pre a b hm
            have hpm := matching_mono xs ys a b (r-1) (c-1) pre (by omega) (by omega) hp
            have hu := hupper pre hpm
            change Zlength pre ≤ Zlength best at hu
            simp only [Zlength_app, Zlength_cons, Zlength_nil]
            omega
        · simp only [Zlength_app, Zlength_cons, Zlength_nil]
          omega
      · have ha := ih ((r-1+c).toNat) (by omega) (r-1) c
          (by rw [Int.toNat_of_nonneg (by omega)]) (by omega) hc
        have hb := ih ((r+c-1).toNat) (by omega) r (c-1)
          (by rw [Int.toNat_of_nonneg (by omega)]; omega) hr (by omega)
        obtain ⟨a,⟨ham,hau⟩,hav⟩ := ha
        obtain ⟨b,⟨hbm,hbu⟩,hbv⟩ := hb
        dsimp only at hau hbu hav hbv
        by_cases hab : Zlength a ≤ Zlength b
        · refine ⟨b, ⟨matching_mono xs ys r (c-1) r c b (by omega) (by omega) hbm, ?_⟩, ?_⟩
          · intro ps hm
            change Zlength ps ≤ Zlength b
            rcases mismatch_cover xs ys r c ps he hm with hm | hm
            · have := hau ps hm; omega
            · exact hbu ps hm
          · rw [hv, ← hav, ← hbv, max_eq_right hab]
        · refine ⟨a, ⟨matching_mono xs ys (r-1) c r c a (by omega) (by omega) ham, ?_⟩, ?_⟩
          · intro ps hm
            change Zlength ps ≤ Zlength a
            rcases mismatch_cover xs ys r c ps he hm with hm | hm
            · exact hau ps hm
            · have := hbu ps hm; omega
          · rw [hv, ← hav, ← hbv, max_eq_left (by omega)]
  exact main (r+c).toNat r c (by rw [Int.toNat_of_nonneg (by omega)]) hr hc

theorem lcsn_table_length_result (xs ys : List Int) (n : Int) (table : List Int)
    (hn : 0 ≤ n) (hx : Zlength xs = n) (hy : Zlength ys = n)
    (ht : LCSNTableResult xs ys n table) :
    LCSNLength xs ys (Znth ((n+1)*n+n) table 0) := by
  unfold LCSNLength
  rw [hx,hy]
  simpa only [LCSNCellIndex, Int.mul_comm] using
    lcsn_table_cell_optimal xs ys n table ht n n ⟨hn, le_refl _⟩ ⟨hn, le_refl _⟩

end SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib
