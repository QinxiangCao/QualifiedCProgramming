import Init.Data.Vector.Extract
import Init.Data.Vector.InsertIdx
import Init.Data.Vector.Lemmas
import SimpleC.SL.CommonAssertion

namespace SimpleC.SL.StoreAux

open AUXLib
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open Unifysl.LogicGenerator.demo932

structure StoreLibSig
    (_CRules : SeparationLogicSig)
    (_DePredSig : DerivedPredSig _CRules) : Type where

namespace StoreLibSig

def canonical (CRules : SeparationLogicSig) (DePredSig : DerivedPredSig CRules) :
    StoreLibSig CRules DePredSig := {}

variable (CRules : SeparationLogicSig)

def vector_cons {α : Type} {n : Nat}
    (x : α) (xs : Vector α n) : Vector α (n + 1) :=
  (#v[x] ++ xs).cast (by omega)

def vector_head {α : Type} {n : Nat} (xs : Vector α (n + 1)) : α :=
  xs[0]

def vector_tail {α : Type} {n : Nat}
    (xs : Vector α (n + 1)) : Vector α n :=
  Vector.ofFn fun i => xs[i.val + 1]

private theorem vector_cons_eq {α : Type} {n : Nat} (x : α) (xs : Vector α n) :
    vector_cons x xs = (#v[x] ++ xs).cast (by omega) := by
  rfl

theorem vector_head_cons {α : Type} {n : Nat}
    (x : α) (xs : Vector α n) : vector_head (vector_cons x xs) = x := by
  rw [vector_cons_eq]
  simp only [vector_head, Vector.getElem_cast]
  rw [Vector.getElem_append_left (hi := by omega)]
  rfl

theorem vector_tail_cons {α : Type} {n : Nat}
    (x : α) (xs : Vector α n) : vector_tail (vector_cons x xs) = xs := by
  apply Vector.ext
  intro i hi
  simp only [vector_cons, vector_tail, Vector.getElem_ofFn, Vector.getElem_cast]
  rw [Vector.getElem_append_right]
  · simp
  · omega

theorem vector_cons_eta {α : Type} {n : Nat} (xs : Vector α (n + 1)) :
    vector_cons (vector_head xs) (vector_tail xs) = xs := by
  apply Vector.ext
  intro i hi
  cases i with
  | zero =>
      simp only [vector_cons, vector_head, Vector.getElem_cast]
      rw [Vector.getElem_append_left (hi := by omega)]
      rfl
  | succ i =>
      simp only [vector_cons, vector_tail, Vector.getElem_cast]
      rw [Vector.getElem_append_right]
      · simp
      · omega

private theorem pow_bytes_succ (n : Nat) :
    Z.pow 2 (8 * Int.ofNat (n + 1)) =
      256 * Z.pow 2 (8 * Int.ofNat n) := by
  change (2 : Int) ^ (8 * (n + 1)) = 256 * (2 : Int) ^ (8 * n)
  rw [show 8 * (n + 1) = 8 + 8 * n by omega]
  rw [Int.pow_add]
  rw [show (2 : Int) ^ 8 = 256 by decide]

private theorem pow_bytes_pos (n : Nat) :
    0 < Z.pow 2 (8 * Int.ofNat n) := by
  change 0 < (2 : Int) ^ (8 * n)
  exact Int.pow_pos (by decide)

theorem store_byte_eqm (p v v' : Int) (h : Byte.eqm v v') :
    CRules.derivable1 (store_byte CRules p v) (store_byte CRules p v') :=
  CRules.mstore_eqm p v v' h

theorem eqm_iff_mod_eq (x y : Int) :
    Byte.eqm x y ↔ Z.modulo x 256 = Z.modulo y 256 := by
  constructor
  · exact Byte.eqm_mod_eq x y
  · intro h
    apply Byte.eqm_trans x (Z.modulo x 256) y
    · exact Zbits.eqmod_mod 256 x
    · apply Byte.eqm_trans (Z.modulo x 256) (Z.modulo y 256) y
      · exact Byte.eqm_refl2 _ _ h
      · exact Byte.eqm_sym y (Z.modulo y 256) (Zbits.eqmod_mod 256 y)

def bytes_eqm : (n : Nat) → Vector Int n → Vector Int n → Prop
  | 0, _, _ => True
  | n + 1, v1, v2 =>
      Byte.eqm (vector_head v1) (vector_head v2) ∧
        bytes_eqm n (vector_tail v1) (vector_tail v2)

def n_bytes_to_Z : (n : Nat) → Vector Int n → Int
  | 0, _ => 0
  | n + 1, v =>
      Z.modulo (vector_head v) (Z.pow 2 8) *
          Z.pow 2 (8 * Int.ofNat n) +
        n_bytes_to_Z n (vector_tail v)

theorem n_bytes_to_Z_cons (b : Int) (n : Nat) (v : Vector Int n) :
    n_bytes_to_Z (n + 1) (vector_cons b v) =
      Z.modulo b (Z.pow 2 8) * Z.pow 2 (8 * Int.ofNat n) +
        n_bytes_to_Z n v := by
  simp [n_bytes_to_Z, vector_head_cons, vector_tail_cons]

theorem eqm_bytes_to_Z_eq (n : Nat) (v1 v2 : Vector Int n)
    (h : bytes_eqm n v1 v2) : n_bytes_to_Z n v1 = n_bytes_to_Z n v2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Byte.eqm (vector_head v1) (vector_head v2) ∧
        bytes_eqm n (vector_tail v1) (vector_tail v2) at h
      change
        Z.modulo (vector_head v1) (Z.pow 2 8) * Z.pow 2 (8 * Int.ofNat n) +
            n_bytes_to_Z n (vector_tail v1) =
          Z.modulo (vector_head v2) (Z.pow 2 8) * Z.pow 2 (8 * Int.ofNat n) +
            n_bytes_to_Z n (vector_tail v2)
      have hm := Byte.eqm_mod_eq _ _ h.1
      change Z.modulo (vector_head v1) 256 = Z.modulo (vector_head v2) 256 at hm
      rw [show Z.pow 2 8 = 256 by decide, hm, ih _ _ h.2]

def Z_to_n_bytes (v : Int) : (length : Nat) → Vector Int length
  | 0 => #v[]
  | n + 1 =>
      vector_cons
        (Z.modulo (Z.div v (Z.pow 2 (8 * Int.ofNat n))) (Z.pow 2 8))
        (Z_to_n_bytes v n)

theorem Z_to_n_bytes_succ (v : Int) (length : Nat) :
    Z_to_n_bytes v (length + 1) =
      vector_cons
        (Z.modulo (Z.div v (Z.pow 2 (8 * Int.ofNat length))) (Z.pow 2 8))
        (Z_to_n_bytes v length) := rfl

theorem Z_to_n_bytes_to_Z (length : Nat) (v : Int) :
    n_bytes_to_Z length (Z_to_n_bytes v length) =
      Z.modulo v (Z.pow 2 (8 * Int.ofNat length)) := by
  induction length with
  | zero => simp [n_bytes_to_Z, Z.pow, Z.modulo]
  | succ n ih =>
      rw [Z_to_n_bytes_succ, n_bytes_to_Z_cons, ih]
      rw [show Z.pow 2 8 = 256 by decide]
      rw [show Z.modulo (Z.modulo
          (Z.div v (Z.pow 2 (8 * Int.ofNat n))) 256) 256 =
          Z.modulo (Z.div v (Z.pow 2 (8 * Int.ofNat n))) 256 by
        exact Int.fmod_fmod _ _]
      rw [pow_bytes_succ]
      exact (Zmod_recombine v 256 (Z.pow 2 (8 * Int.ofNat n))
        (by decide) (pow_bytes_pos n)).symm

def merge_n_bytes (n : Nat) (v : Vector Int n) (x : Int) : Prop :=
  Z.modulo x (Z.pow 2 (8 * Int.ofNat n)) = n_bytes_to_Z n v

theorem merge_short_equiv_merge_n_bytes (x1 x2 y : Int) :
    merge_short x1 x2 y ↔
      merge_n_bytes 2 (vector_cons x1 (vector_cons x2 #v[])) y := by
  unfold merge_short merge_n_bytes
  simp only [n_bytes_to_Z, vector_head_cons, vector_tail_cons]
  simp only [Z.pow, Z.modulo]
  rw [Int.fmod_eq_emod_of_nonneg y (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x1 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x2 (by decide)]
  simp

theorem merge_int_equiv_merge_n_bytes (x1 x2 x3 x4 y : Int) :
    merge_int x1 x2 x3 x4 y ↔
      merge_n_bytes 4
        (vector_cons x1 (vector_cons x2 (vector_cons x3 (vector_cons x4 #v[])))) y := by
  unfold merge_int merge_n_bytes
  simp only [n_bytes_to_Z, vector_head_cons, vector_tail_cons]
  simp only [Z.modulo]
  simp only [Z.pow]
  rw [Int.fmod_eq_emod_of_nonneg y (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x1 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x2 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x3 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x4 (by decide)]
  simp
  constructor
  · intro h
    exact h.trans (by ac_rfl)
  · intro h
    exact h.trans (by ac_rfl)

theorem merge_int64_equiv_merge_n_bytes
    (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y ↔
      merge_n_bytes 8
        (vector_cons x1 (vector_cons x2 (vector_cons x3 (vector_cons x4
          (vector_cons x5 (vector_cons x6 (vector_cons x7 (vector_cons x8 #v[])))))))) y := by
  unfold merge_int64 merge_n_bytes
  simp only [n_bytes_to_Z, vector_head_cons, vector_tail_cons]
  simp only [Z.modulo]
  simp only [Z.pow]
  rw [Int.fmod_eq_emod_of_nonneg y (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x1 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x2 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x3 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x4 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x5 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x6 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x7 (by decide)]
  rw [Int.fmod_eq_emod_of_nonneg x8 (by decide)]
  simp
  constructor
  · intro h
    exact h.trans (by ac_rfl)
  · intro h
    exact h.trans (by ac_rfl)

def store_n_bytes (x : Int) : (n : Nat) → Vector Int n → CRules.expr
  | 0, _ => CRules.emp
  | n + 1, v =>
      CRules.sepcon (CRules.mstore x (vector_head v))
        (store_n_bytes (x + 1) n (vector_tail v))

def store_n_bytes_Z (x : Int) (n : Nat) (v : Int) : CRules.expr :=
  CRules.exp (Vector Int n) fun bytes =>
    CRules.andp
      (CRules.coq_prop (merge_n_bytes n bytes v))
      (store_n_bytes CRules x n bytes)

def store_n_bytes_noninit (x : Int) :
    (n : Nat) → Vector Int n → CRules.expr
  | 0, _ => CRules.emp
  | n + 1, v =>
      CRules.sepcon (CRules.mstore_noninit x)
        (store_n_bytes_noninit (x + 1) n (vector_tail v))

end StoreLibSig

end SimpleC.SL.StoreAux
