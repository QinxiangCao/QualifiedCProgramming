import AUXLib.NiaCompat
import compcert.lib.Coqlib
import compcert.lib.Integers
import Init.Data.Vector.Extract
import Init.Data.Vector.InsertIdx
import Init.Data.Vector.Lemmas
import Lean.Elab.Tactic.Omega

namespace SimpleC.SL.CArch

open CompCert

structure CArchSig : Type where
  ptr_size : Nat
  ptr_align : Int
  addr_max_unsigned : Int
  ptr_size_pos : 0 < Int.ofNat ptr_size
  ptr_size_32_or_64 : ptr_size = 4 ∨ ptr_size = 8
  ptr_align_pos : 0 < ptr_align
  ptr_aligned_aligned_4 :
    ∀ x, Z.modulo x ptr_align = 0 → Z.modulo x 4 = 0
  addr_max_unsigned_ge_7 : 7 ≤ addr_max_unsigned
  ptr_size_fits_addr : Int.ofNat ptr_size - 1 ≤ addr_max_unsigned
  int_max_fits_addr : Int.max_unsigned ≤ addr_max_unsigned

namespace CArchSig

def ptr_size_Z (self : CArchSig) : Int :=
  Int.ofNat self.ptr_size

def ptr_width_Z (self : CArchSig) : Int :=
  8 * self.ptr_size_Z

def aligned (_self : CArchSig) (align p : Int) : Prop :=
  Z.modulo p align = 0

def valid_addr_range (self : CArchSig) (p len : Int) : Prop :=
  0 ≤ p ∧ 0 ≤ len ∧ p + len - 1 ≤ self.addr_max_unsigned

def valid_object (self : CArchSig) (p len align : Int) : Prop :=
  self.valid_addr_range p len ∧ self.aligned align p

def valid_ptr_value (self : CArchSig) (v : Int) : Prop :=
  0 ≤ v ∧ v ≤ self.addr_max_unsigned

end CArchSig

namespace Arch32

def ptr_size : Nat := 4
def ptr_align : Int := 4
def addr_max_unsigned : Int := Int.max_unsigned
def ptr_size_Z : Int := Int.ofNat ptr_size
def ptr_width_Z : Int := 8 * ptr_size_Z
def aligned (align p : Int) : Prop := Z.modulo p align = 0

theorem ptr_size_pos : 0 < ptr_size_Z := by decide

theorem ptr_size_32_or_64 : ptr_size = 4 ∨ ptr_size = 8 :=
  Or.inl rfl

theorem ptr_align_pos : 0 < ptr_align := by decide

theorem ptr_aligned_aligned_4 :
    ∀ x, aligned ptr_align x → Z.modulo x 4 = 0 := by
  intro x h
  exact h

theorem addr_max_unsigned_ge_7 : 7 ≤ addr_max_unsigned := by decide

theorem ptr_size_fits_addr : ptr_size_Z - 1 ≤ addr_max_unsigned := by
  decide

theorem int_max_fits_addr : Int.max_unsigned ≤ addr_max_unsigned := by
  exact Int.le_refl _

def valid_addr_range (p len : Int) : Prop :=
  0 ≤ p ∧ 0 ≤ len ∧ p + len - 1 ≤ addr_max_unsigned

def valid_object (p len align : Int) : Prop :=
  valid_addr_range p len ∧ aligned align p

def valid_ptr_value (v : Int) : Prop :=
  0 ≤ v ∧ v ≤ addr_max_unsigned

end Arch32

def Arch32 : CArchSig where
  ptr_size := Arch32.ptr_size
  ptr_align := Arch32.ptr_align
  addr_max_unsigned := Arch32.addr_max_unsigned
  ptr_size_pos := Arch32.ptr_size_pos
  ptr_size_32_or_64 := Arch32.ptr_size_32_or_64
  ptr_align_pos := Arch32.ptr_align_pos
  ptr_aligned_aligned_4 := Arch32.ptr_aligned_aligned_4
  addr_max_unsigned_ge_7 := Arch32.addr_max_unsigned_ge_7
  ptr_size_fits_addr := Arch32.ptr_size_fits_addr
  int_max_fits_addr := Arch32.int_max_fits_addr

namespace Arch64

def ptr_size : Nat := 8
def ptr_align : Int := 8
def addr_max_unsigned : Int := Int64.max_unsigned
def ptr_size_Z : Int := Int.ofNat ptr_size
def ptr_width_Z : Int := 8 * ptr_size_Z
def aligned (align p : Int) : Prop := Z.modulo p align = 0

theorem ptr_size_pos : 0 < ptr_size_Z := by decide

theorem ptr_size_32_or_64 : ptr_size = 4 ∨ ptr_size = 8 :=
  Or.inr rfl

theorem ptr_align_pos : 0 < ptr_align := by decide

theorem ptr_aligned_aligned_4 :
    ∀ x, aligned ptr_align x → Z.modulo x 4 = 0 := by
  intro x h
  unfold aligned ptr_align at h
  unfold Z.modulo at h ⊢
  apply Int.fmod_eq_zero_of_dvd
  exact Int.dvd_trans (show (4 : Int) ∣ 8 by decide) (Int.dvd_of_fmod_eq_zero h)

theorem addr_max_unsigned_ge_7 : 7 ≤ addr_max_unsigned := by decide

theorem ptr_size_fits_addr : ptr_size_Z - 1 ≤ addr_max_unsigned := by
  decide

theorem int_max_fits_addr : Int.max_unsigned ≤ addr_max_unsigned := by
  decide

def valid_addr_range (p len : Int) : Prop :=
  0 ≤ p ∧ 0 ≤ len ∧ p + len - 1 ≤ addr_max_unsigned

def valid_object (p len align : Int) : Prop :=
  valid_addr_range p len ∧ aligned align p

def valid_ptr_value (v : Int) : Prop :=
  0 ≤ v ∧ v ≤ addr_max_unsigned

end Arch64

def Arch64 : CArchSig where
  ptr_size := Arch64.ptr_size
  ptr_align := Arch64.ptr_align
  addr_max_unsigned := Arch64.addr_max_unsigned
  ptr_size_pos := Arch64.ptr_size_pos
  ptr_size_32_or_64 := Arch64.ptr_size_32_or_64
  ptr_align_pos := Arch64.ptr_align_pos
  ptr_aligned_aligned_4 := Arch64.ptr_aligned_aligned_4
  addr_max_unsigned_ge_7 := Arch64.addr_max_unsigned_ge_7
  ptr_size_fits_addr := Arch64.ptr_size_fits_addr
  int_max_fits_addr := Arch64.int_max_fits_addr

structure CEndianSig : Type where
  bytes_eqm : (n : Nat) → Vector Int n → Vector Int n → Prop
  n_bytes_to_Z : (n : Nat) → Vector Int n → Int
  Z_to_n_bytes : Int → (length : Nat) → Vector Int length
  merge_n_bytes : (n : Nat) → Vector Int n → Int → Prop
  merge_short : Int → Int → Int → Prop
  merge_int : Int → Int → Int → Int → Int → Prop
  merge_int64 : Int → Int → Int → Int → Int → Int → Int → Int → Int → Prop
  eqm_bytes_to_Z_eq :
    ∀ n (v1 v2 : Vector Int n),
      bytes_eqm n v1 v2 → n_bytes_to_Z n v1 = n_bytes_to_Z n v2
  Z_to_n_bytes_to_Z :
    ∀ length v,
      n_bytes_to_Z length (Z_to_n_bytes v length) =
        Z.modulo v (Z.pow 2 (8 * Int.ofNat length))
  merge_n_bytes_self :
    ∀ n (v : Vector Int n), merge_n_bytes n v (n_bytes_to_Z n v)
  merge_byte_equiv_merge_n_bytes :
    ∀ x y, Byte.eqm x y ↔ merge_n_bytes 1 #v[x] y
  merge_short_equiv_merge_n_bytes :
    ∀ x1 x2 y, merge_short x1 x2 y ↔ merge_n_bytes 2 #v[x1, x2] y
  merge_int_equiv_merge_n_bytes :
    ∀ x1 x2 x3 x4 y,
      merge_int x1 x2 x3 x4 y ↔ merge_n_bytes 4 #v[x1, x2, x3, x4] y
  merge_int64_equiv_merge_n_bytes :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 y,
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y ↔
        merge_n_bytes 8 #v[x1, x2, x3, x4, x5, x6, x7, x8] y
  merge_short_eqm :
    ∀ x1 x2 y1 y2 v,
      Byte.eqm x1 y1 → Byte.eqm x2 y2 →
      merge_short x1 x2 v → merge_short y1 y2 v
  merge_int_eqm :
    ∀ x1 x2 x3 x4 y1 y2 y3 y4 v,
      Byte.eqm x1 y1 → Byte.eqm x2 y2 → Byte.eqm x3 y3 → Byte.eqm x4 y4 →
      merge_int x1 x2 x3 x4 v → merge_int y1 y2 y3 y4 v
  merge_int64_eqm :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v,
      Byte.eqm x1 y1 → Byte.eqm x2 y2 → Byte.eqm x3 y3 → Byte.eqm x4 y4 →
      Byte.eqm x5 y5 → Byte.eqm x6 y6 → Byte.eqm x7 y7 → Byte.eqm x8 y8 →
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v →
      merge_int64 y1 y2 y3 y4 y5 y6 y7 y8 v
  merge_short_value_eqm :
    ∀ x1 x2 v v',
      Z.modulo v (Z.pow 2 16) = Z.modulo v' (Z.pow 2 16) →
      merge_short x1 x2 v → merge_short x1 x2 v'
  merge_int_value_eqm :
    ∀ x1 x2 x3 x4 v v',
      Z.modulo v (Z.pow 2 32) = Z.modulo v' (Z.pow 2 32) →
      merge_int x1 x2 x3 x4 v → merge_int x1 x2 x3 x4 v'
  merge_int64_value_eqm :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 v v',
      Z.modulo v (Z.pow 2 64) = Z.modulo v' (Z.pow 2 64) →
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v →
      merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v'

def vector_cons {α : Type} {n : Nat}
    (x : α) (xs : Vector α n) : Vector α (n + 1) :=
  (#v[x] ++ xs).cast (by omega)

def vector_head {α : Type} {n : Nat} (xs : Vector α (n + 1)) : α :=
  xs[0]

def vector_tail {α : Type} {n : Nat}
    (xs : Vector α (n + 1)) : Vector α n :=
  Vector.ofFn fun i => xs[i.val + 1]

theorem vector_head_cons {α : Type} {n : Nat}
    (x : α) (xs : Vector α n) : vector_head (vector_cons x xs) = x := by
  simp only [vector_head, vector_cons, Vector.getElem_cast]
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

private theorem byte_eqm_iff_mod_eq (x y : Int) :
    Byte.eqm x y ↔ Z.modulo x 256 = Z.modulo y 256 := by
  constructor
  · exact Byte.eqm_mod_eq x y
  · intro h
    apply Byte.eqm_trans x (Z.modulo x 256) y
    · exact Zbits.eqmod_mod 256 x
    · apply Byte.eqm_trans (Z.modulo x 256) (Z.modulo y 256) y
      · exact Byte.eqm_refl2 _ _ h
      · exact Byte.eqm_sym y (Z.modulo y 256) (Zbits.eqmod_mod 256 y)

namespace BigEndian

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

def Z_to_n_bytes (v : Int) : (length : Nat) → Vector Int length
  | 0 => #v[]
  | n + 1 =>
      vector_cons
        (Z.modulo (Z.div v (Z.pow 2 (8 * Int.ofNat n))) (Z.pow 2 8))
        (Z_to_n_bytes v n)

theorem n_bytes_to_Z_cons (b : Int) (n : Nat) (v : Vector Int n) :
    n_bytes_to_Z (n + 1) (vector_cons b v) =
      Z.modulo b (Z.pow 2 8) * Z.pow 2 (8 * Int.ofNat n) +
        n_bytes_to_Z n v := by
  simp [n_bytes_to_Z, vector_head_cons, vector_tail_cons]

theorem Z_to_n_bytes_succ (v : Int) (length : Nat) :
    Z_to_n_bytes v (length + 1) =
      vector_cons
        (Z.modulo (Z.div v (Z.pow 2 (8 * Int.ofNat length))) (Z.pow 2 8))
        (Z_to_n_bytes v length) := rfl

def merge_n_bytes (n : Nat) (v : Vector Int n) (x : Int) : Prop :=
  Z.modulo x (Z.pow 2 (8 * Int.ofNat n)) = n_bytes_to_Z n v

def merge_short (x1 x2 y : Int) : Prop :=
  Z.modulo y (Z.pow 2 16) =
    Z.modulo x1 (Z.pow 2 8) * Z.pow 2 8 +
      Z.modulo x2 (Z.pow 2 8)

def merge_int (x1 x2 x3 x4 y : Int) : Prop :=
  Z.modulo y (Z.pow 2 32) =
    Z.modulo x1 (Z.pow 2 8) * Z.pow 2 24 +
    Z.modulo x2 (Z.pow 2 8) * Z.pow 2 16 +
    Z.modulo x3 (Z.pow 2 8) * Z.pow 2 8 +
    Z.modulo x4 (Z.pow 2 8)

def merge_int64 (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) : Prop :=
  Z.modulo y (Z.pow 2 64) =
    Z.modulo x1 (Z.pow 2 8) * Z.pow 2 56 +
    Z.modulo x2 (Z.pow 2 8) * Z.pow 2 48 +
    Z.modulo x3 (Z.pow 2 8) * Z.pow 2 40 +
    Z.modulo x4 (Z.pow 2 8) * Z.pow 2 32 +
    Z.modulo x5 (Z.pow 2 8) * Z.pow 2 24 +
    Z.modulo x6 (Z.pow 2 8) * Z.pow 2 16 +
    Z.modulo x7 (Z.pow 2 8) * Z.pow 2 8 +
    Z.modulo x8 (Z.pow 2 8)

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

theorem n_bytes_to_Z_range (n : Nat) (v : Vector Int n) :
    0 ≤ n_bytes_to_Z n v ∧ n_bytes_to_Z n v < Z.pow 2 (8 * Int.ofNat n) := by
  induction n with
  | zero => simp [n_bytes_to_Z, Z.pow]
  | succ n ih =>
      let b := vector_head v
      let tail := vector_tail v
      let q := Z.pow 2 (8 * Int.ofNat n)
      have hq : 0 < q := pow_bytes_pos n
      have hb0 : 0 ≤ Z.modulo b 256 := Int.fmod_nonneg_of_pos b (by decide)
      have hbhi : Z.modulo b 256 < 256 := Int.fmod_lt_of_pos b (by decide)
      have ht := ih tail
      have hb_le : Z.modulo b 256 ≤ 255 := by omega
      have ht_le : n_bytes_to_Z n tail ≤ q - 1 := by omega
      change
        0 ≤ Z.modulo b (Z.pow 2 8) * q + n_bytes_to_Z n tail ∧
          Z.modulo b (Z.pow 2 8) * q + n_bytes_to_Z n tail <
            Z.pow 2 (8 * Int.ofNat (n + 1))
      rw [show Z.pow 2 8 = 256 by decide, pow_bytes_succ]
      constructor
      · exact Int.add_nonneg
          (Int.mul_nonneg hb0 (Int.le_of_lt hq)) ht.1
      · have hmul : Z.modulo b 256 * q ≤ 255 * q :=
          Int.mul_le_mul_of_nonneg_right hb_le (Int.le_of_lt hq)
        calc
          Z.modulo b 256 * q + n_bytes_to_Z n tail ≤
              255 * q + (q - 1) := Int.add_le_add hmul ht_le
          _ < 256 * q := by omega

theorem merge_n_bytes_self (n : Nat) (v : Vector Int n) :
    merge_n_bytes n v (n_bytes_to_Z n v) := by
  unfold merge_n_bytes Z.modulo
  exact Int.fmod_eq_of_lt (n_bytes_to_Z_range n v).1 (n_bytes_to_Z_range n v).2

theorem merge_byte_equiv_merge_n_bytes (x y : Int) :
    Byte.eqm x y ↔ merge_n_bytes 1 #v[x] y := by
  simp [merge_n_bytes, n_bytes_to_Z, vector_head, Z.pow]
  rw [byte_eqm_iff_mod_eq]
  exact eq_comm

theorem merge_short_equiv_merge_n_bytes (x1 x2 y : Int) :
    merge_short x1 x2 y ↔ merge_n_bytes 2 #v[x1, x2] y := by
  simp [merge_short, merge_n_bytes, n_bytes_to_Z, vector_head, vector_tail,
    Z.pow, Z.modulo]

theorem merge_int_equiv_merge_n_bytes (x1 x2 x3 x4 y : Int) :
    merge_int x1 x2 x3 x4 y ↔ merge_n_bytes 4 #v[x1, x2, x3, x4] y := by
  simp [merge_int, merge_n_bytes, n_bytes_to_Z, vector_head, vector_tail,
    Z.pow, Z.modulo]
  constructor <;> intro h <;> omega

theorem merge_int64_equiv_merge_n_bytes
    (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y ↔
      merge_n_bytes 8 #v[x1, x2, x3, x4, x5, x6, x7, x8] y := by
  simp [merge_int64, merge_n_bytes, n_bytes_to_Z, vector_head, vector_tail,
    Z.pow, Z.modulo]
  constructor <;> intro h <;> omega

theorem merge_short_eqm (x1 x2 y1 y2 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h : merge_short x1 x2 v) : merge_short y1 y2 v := by
  have hm1 := Byte.eqm_mod_eq _ _ h1
  have hm2 := Byte.eqm_mod_eq _ _ h2
  unfold merge_short at h ⊢
  change Z.modulo x1 256 = Z.modulo y1 256 at hm1
  change Z.modulo x2 256 = Z.modulo y2 256 at hm2
  rw [show Z.pow 2 8 = 256 by decide, ← hm1, ← hm2]
  exact h

theorem merge_int_eqm (x1 x2 x3 x4 y1 y2 y3 y4 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h3 : Byte.eqm x3 y3) (h4 : Byte.eqm x4 y4)
    (h : merge_int x1 x2 x3 x4 v) : merge_int y1 y2 y3 y4 v := by
  have hm1 := Byte.eqm_mod_eq _ _ h1
  have hm2 := Byte.eqm_mod_eq _ _ h2
  have hm3 := Byte.eqm_mod_eq _ _ h3
  have hm4 := Byte.eqm_mod_eq _ _ h4
  unfold merge_int at h ⊢
  change Z.modulo x1 256 = Z.modulo y1 256 at hm1
  change Z.modulo x2 256 = Z.modulo y2 256 at hm2
  change Z.modulo x3 256 = Z.modulo y3 256 at hm3
  change Z.modulo x4 256 = Z.modulo y4 256 at hm4
  rw [show Z.pow 2 8 = 256 by decide, ← hm1, ← hm2, ← hm3, ← hm4]
  exact h

theorem merge_int64_eqm
    (x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h3 : Byte.eqm x3 y3) (h4 : Byte.eqm x4 y4)
    (h5 : Byte.eqm x5 y5) (h6 : Byte.eqm x6 y6)
    (h7 : Byte.eqm x7 y7) (h8 : Byte.eqm x8 y8)
    (h : merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v) :
    merge_int64 y1 y2 y3 y4 y5 y6 y7 y8 v := by
  have hm1 := Byte.eqm_mod_eq _ _ h1
  have hm2 := Byte.eqm_mod_eq _ _ h2
  have hm3 := Byte.eqm_mod_eq _ _ h3
  have hm4 := Byte.eqm_mod_eq _ _ h4
  have hm5 := Byte.eqm_mod_eq _ _ h5
  have hm6 := Byte.eqm_mod_eq _ _ h6
  have hm7 := Byte.eqm_mod_eq _ _ h7
  have hm8 := Byte.eqm_mod_eq _ _ h8
  unfold merge_int64 at h ⊢
  change Z.modulo x1 256 = Z.modulo y1 256 at hm1
  change Z.modulo x2 256 = Z.modulo y2 256 at hm2
  change Z.modulo x3 256 = Z.modulo y3 256 at hm3
  change Z.modulo x4 256 = Z.modulo y4 256 at hm4
  change Z.modulo x5 256 = Z.modulo y5 256 at hm5
  change Z.modulo x6 256 = Z.modulo y6 256 at hm6
  change Z.modulo x7 256 = Z.modulo y7 256 at hm7
  change Z.modulo x8 256 = Z.modulo y8 256 at hm8
  rw [show Z.pow 2 8 = 256 by decide, ← hm1, ← hm2, ← hm3, ← hm4,
    ← hm5, ← hm6, ← hm7, ← hm8]
  exact h

theorem merge_short_value_eqm (x1 x2 v v' : Int)
    (hm : Z.modulo v (Z.pow 2 16) = Z.modulo v' (Z.pow 2 16))
    (h : merge_short x1 x2 v) : merge_short x1 x2 v' := by
  unfold merge_short at h ⊢
  rw [← hm]
  exact h

theorem merge_int_value_eqm (x1 x2 x3 x4 v v' : Int)
    (hm : Z.modulo v (Z.pow 2 32) = Z.modulo v' (Z.pow 2 32))
    (h : merge_int x1 x2 x3 x4 v) : merge_int x1 x2 x3 x4 v' := by
  unfold merge_int at h ⊢
  rw [← hm]
  exact h

theorem merge_int64_value_eqm (x1 x2 x3 x4 x5 x6 x7 x8 v v' : Int)
    (hm : Z.modulo v (Z.pow 2 64) = Z.modulo v' (Z.pow 2 64))
    (h : merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v) :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v' := by
  unfold merge_int64 at h ⊢
  rw [← hm]
  exact h

end BigEndian

def BigEndian : CEndianSig where
  bytes_eqm := BigEndian.bytes_eqm
  n_bytes_to_Z := BigEndian.n_bytes_to_Z
  Z_to_n_bytes := BigEndian.Z_to_n_bytes
  merge_n_bytes := BigEndian.merge_n_bytes
  merge_short := BigEndian.merge_short
  merge_int := BigEndian.merge_int
  merge_int64 := BigEndian.merge_int64
  eqm_bytes_to_Z_eq := BigEndian.eqm_bytes_to_Z_eq
  Z_to_n_bytes_to_Z := BigEndian.Z_to_n_bytes_to_Z
  merge_n_bytes_self := BigEndian.merge_n_bytes_self
  merge_byte_equiv_merge_n_bytes := BigEndian.merge_byte_equiv_merge_n_bytes
  merge_short_equiv_merge_n_bytes := BigEndian.merge_short_equiv_merge_n_bytes
  merge_int_equiv_merge_n_bytes := BigEndian.merge_int_equiv_merge_n_bytes
  merge_int64_equiv_merge_n_bytes := BigEndian.merge_int64_equiv_merge_n_bytes
  merge_short_eqm := BigEndian.merge_short_eqm
  merge_int_eqm := BigEndian.merge_int_eqm
  merge_int64_eqm := BigEndian.merge_int64_eqm
  merge_short_value_eqm := BigEndian.merge_short_value_eqm
  merge_int_value_eqm := BigEndian.merge_int_value_eqm
  merge_int64_value_eqm := BigEndian.merge_int64_value_eqm

namespace LittleEndian

def bytes_eqm : (n : Nat) → Vector Int n → Vector Int n → Prop
  | 0, _, _ => True
  | n + 1, v1, v2 =>
      Byte.eqm (vector_head v1) (vector_head v2) ∧
        bytes_eqm n (vector_tail v1) (vector_tail v2)

def n_bytes_to_Z : (n : Nat) → Vector Int n → Int
  | 0, _ => 0
  | n + 1, v =>
      Z.modulo (vector_head v) (Z.pow 2 8) +
        Z.pow 2 8 * n_bytes_to_Z n (vector_tail v)

def Z_to_n_bytes (v : Int) : (length : Nat) → Vector Int length
  | 0 => #v[]
  | n + 1 =>
      vector_cons (Z.modulo v (Z.pow 2 8))
        (Z_to_n_bytes (Z.div v (Z.pow 2 8)) n)

def merge_n_bytes (n : Nat) (v : Vector Int n) (x : Int) : Prop :=
  Z.modulo x (Z.pow 2 (8 * Int.ofNat n)) = n_bytes_to_Z n v

def merge_short (x1 x2 y : Int) : Prop :=
  Z.modulo y (Z.pow 2 16) =
    Z.modulo x1 (Z.pow 2 8) + Z.modulo x2 (Z.pow 2 8) * Z.pow 2 8

def merge_int (x1 x2 x3 x4 y : Int) : Prop :=
  Z.modulo y (Z.pow 2 32) =
    Z.modulo x1 (Z.pow 2 8) +
    Z.modulo x2 (Z.pow 2 8) * Z.pow 2 8 +
    Z.modulo x3 (Z.pow 2 8) * Z.pow 2 16 +
    Z.modulo x4 (Z.pow 2 8) * Z.pow 2 24

def merge_int64 (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) : Prop :=
  Z.modulo y (Z.pow 2 64) =
    Z.modulo x1 (Z.pow 2 8) +
    Z.modulo x2 (Z.pow 2 8) * Z.pow 2 8 +
    Z.modulo x3 (Z.pow 2 8) * Z.pow 2 16 +
    Z.modulo x4 (Z.pow 2 8) * Z.pow 2 24 +
    Z.modulo x5 (Z.pow 2 8) * Z.pow 2 32 +
    Z.modulo x6 (Z.pow 2 8) * Z.pow 2 40 +
    Z.modulo x7 (Z.pow 2 8) * Z.pow 2 48 +
    Z.modulo x8 (Z.pow 2 8) * Z.pow 2 56

theorem n_bytes_to_Z_cons (b : Int) (n : Nat) (v : Vector Int n) :
    n_bytes_to_Z (n + 1) (vector_cons b v) =
      Z.modulo b (Z.pow 2 8) + Z.pow 2 8 * n_bytes_to_Z n v := by
  simp [n_bytes_to_Z, vector_head_cons, vector_tail_cons]

theorem eqm_bytes_to_Z_eq (n : Nat) (v1 v2 : Vector Int n)
    (h : bytes_eqm n v1 v2) : n_bytes_to_Z n v1 = n_bytes_to_Z n v2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Byte.eqm (vector_head v1) (vector_head v2) ∧
        bytes_eqm n (vector_tail v1) (vector_tail v2) at h
      change
        Z.modulo (vector_head v1) (Z.pow 2 8) +
            Z.pow 2 8 * n_bytes_to_Z n (vector_tail v1) =
          Z.modulo (vector_head v2) (Z.pow 2 8) +
            Z.pow 2 8 * n_bytes_to_Z n (vector_tail v2)
      have hm := Byte.eqm_mod_eq _ _ h.1
      change Z.modulo (vector_head v1) 256 = Z.modulo (vector_head v2) 256 at hm
      rw [show Z.pow 2 8 = 256 by decide, hm, ih _ _ h.2]

theorem Z_to_n_bytes_to_Z (length : Nat) (v : Int) :
    n_bytes_to_Z length (Z_to_n_bytes v length) =
      Z.modulo v (Z.pow 2 (8 * Int.ofNat length)) := by
  induction length generalizing v with
  | zero => simp [n_bytes_to_Z, Z.pow, Z.modulo]
  | succ n ih =>
      rw [show Z_to_n_bytes v (n + 1) =
        vector_cons (Z.modulo v (Z.pow 2 8))
          (Z_to_n_bytes (Z.div v (Z.pow 2 8)) n) by rfl]
      rw [n_bytes_to_Z_cons]
      rw [show Z.modulo (Z.modulo v (Z.pow 2 8)) (Z.pow 2 8) =
        Z.modulo v (Z.pow 2 8) by
          unfold Z.modulo
          exact Int.fmod_fmod _ _]
      change
        Z.modulo v (Z.pow 2 8) + Z.pow 2 8 *
            n_bytes_to_Z n (Z_to_n_bytes (Z.div v (Z.pow 2 8)) n) =
          Z.modulo v (Z.pow 2 (8 * Int.ofNat (n + 1)))
      rw [ih]
      rw [show Z.pow 2 8 = 256 by decide, pow_bytes_succ]
      have h := Zmod_recombine v (Z.pow 2 (8 * Int.ofNat n)) 256
        (pow_bytes_pos n) (by decide)
      rw [show 256 * Z.pow 2 (8 * Int.ofNat n) =
        Z.pow 2 (8 * Int.ofNat n) * 256 by ac_rfl]
      calc
        Z.modulo v 256 + 256 * Z.modulo (Z.div v 256)
            (Z.pow 2 (8 * Int.ofNat n)) =
            Z.modulo (Z.div v 256) (Z.pow 2 (8 * Int.ofNat n)) * 256 +
              Z.modulo v 256 := by ac_rfl
        _ = Z.modulo v (Z.pow 2 (8 * Int.ofNat n) * 256) := h.symm

theorem n_bytes_to_Z_range (n : Nat) (v : Vector Int n) :
    0 ≤ n_bytes_to_Z n v ∧ n_bytes_to_Z n v < Z.pow 2 (8 * Int.ofNat n) := by
  induction n with
  | zero => simp [n_bytes_to_Z, Z.pow]
  | succ n ih =>
      let b := vector_head v
      let tail := vector_tail v
      let q := Z.pow 2 (8 * Int.ofNat n)
      have hb0 : 0 ≤ Z.modulo b 256 := Int.fmod_nonneg_of_pos b (by decide)
      have hbhi : Z.modulo b 256 < 256 := Int.fmod_lt_of_pos b (by decide)
      have ht := ih tail
      have hb_le : Z.modulo b 256 ≤ 255 := by omega
      have ht_le : n_bytes_to_Z n tail ≤ q - 1 := by omega
      change
        0 ≤ Z.modulo b (Z.pow 2 8) + Z.pow 2 8 * n_bytes_to_Z n tail ∧
          Z.modulo b (Z.pow 2 8) + Z.pow 2 8 * n_bytes_to_Z n tail <
            Z.pow 2 (8 * Int.ofNat (n + 1))
      rw [show Z.pow 2 8 = 256 by decide, pow_bytes_succ]
      constructor
      · exact Int.add_nonneg hb0 (Int.mul_nonneg (by decide) ht.1)
      · have hmul : 256 * n_bytes_to_Z n tail ≤ 256 * (q - 1) :=
          Int.mul_le_mul_of_nonneg_left ht_le (by decide)
        calc
          Z.modulo b 256 + 256 * n_bytes_to_Z n tail ≤
              255 + 256 * (q - 1) := Int.add_le_add hb_le hmul
          _ < 256 * q := by omega

theorem merge_n_bytes_self (n : Nat) (v : Vector Int n) :
    merge_n_bytes n v (n_bytes_to_Z n v) := by
  unfold merge_n_bytes Z.modulo
  exact Int.fmod_eq_of_lt (n_bytes_to_Z_range n v).1 (n_bytes_to_Z_range n v).2

theorem merge_byte_equiv_merge_n_bytes (x y : Int) :
    Byte.eqm x y ↔ merge_n_bytes 1 #v[x] y := by
  simp [merge_n_bytes, n_bytes_to_Z, vector_head, Z.pow]
  rw [byte_eqm_iff_mod_eq]
  exact eq_comm

theorem merge_short_equiv_merge_n_bytes (x1 x2 y : Int) :
    merge_short x1 x2 y ↔ merge_n_bytes 2 #v[x1, x2] y := by
  simp [merge_short, merge_n_bytes, n_bytes_to_Z, vector_head, vector_tail,
    Z.pow, Z.modulo]
  constructor <;> intro h <;> omega

theorem merge_int_equiv_merge_n_bytes (x1 x2 x3 x4 y : Int) :
    merge_int x1 x2 x3 x4 y ↔ merge_n_bytes 4 #v[x1, x2, x3, x4] y := by
  simp [merge_int, merge_n_bytes, n_bytes_to_Z, vector_head, vector_tail,
    Z.pow, Z.modulo]
  constructor <;> intro h <;> omega

theorem merge_int64_equiv_merge_n_bytes
    (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 y ↔
      merge_n_bytes 8 #v[x1, x2, x3, x4, x5, x6, x7, x8] y := by
  simp [merge_int64, merge_n_bytes, n_bytes_to_Z, vector_head, vector_tail,
    Z.pow, Z.modulo]
  constructor <;> intro h <;> omega

theorem merge_short_eqm (x1 x2 y1 y2 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h : merge_short x1 x2 v) : merge_short y1 y2 v := by
  have hm1 := Byte.eqm_mod_eq _ _ h1
  have hm2 := Byte.eqm_mod_eq _ _ h2
  unfold merge_short at h ⊢
  change Z.modulo x1 256 = Z.modulo y1 256 at hm1
  change Z.modulo x2 256 = Z.modulo y2 256 at hm2
  rw [show Z.pow 2 8 = 256 by decide, ← hm1, ← hm2]
  exact h

theorem merge_int_eqm (x1 x2 x3 x4 y1 y2 y3 y4 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h3 : Byte.eqm x3 y3) (h4 : Byte.eqm x4 y4)
    (h : merge_int x1 x2 x3 x4 v) : merge_int y1 y2 y3 y4 v := by
  have hm1 := Byte.eqm_mod_eq _ _ h1
  have hm2 := Byte.eqm_mod_eq _ _ h2
  have hm3 := Byte.eqm_mod_eq _ _ h3
  have hm4 := Byte.eqm_mod_eq _ _ h4
  unfold merge_int at h ⊢
  change Z.modulo x1 256 = Z.modulo y1 256 at hm1
  change Z.modulo x2 256 = Z.modulo y2 256 at hm2
  change Z.modulo x3 256 = Z.modulo y3 256 at hm3
  change Z.modulo x4 256 = Z.modulo y4 256 at hm4
  rw [show Z.pow 2 8 = 256 by decide, ← hm1, ← hm2, ← hm3, ← hm4]
  exact h

theorem merge_int64_eqm
    (x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h3 : Byte.eqm x3 y3) (h4 : Byte.eqm x4 y4)
    (h5 : Byte.eqm x5 y5) (h6 : Byte.eqm x6 y6)
    (h7 : Byte.eqm x7 y7) (h8 : Byte.eqm x8 y8)
    (h : merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v) :
    merge_int64 y1 y2 y3 y4 y5 y6 y7 y8 v := by
  have hm1 := Byte.eqm_mod_eq _ _ h1
  have hm2 := Byte.eqm_mod_eq _ _ h2
  have hm3 := Byte.eqm_mod_eq _ _ h3
  have hm4 := Byte.eqm_mod_eq _ _ h4
  have hm5 := Byte.eqm_mod_eq _ _ h5
  have hm6 := Byte.eqm_mod_eq _ _ h6
  have hm7 := Byte.eqm_mod_eq _ _ h7
  have hm8 := Byte.eqm_mod_eq _ _ h8
  unfold merge_int64 at h ⊢
  change Z.modulo x1 256 = Z.modulo y1 256 at hm1
  change Z.modulo x2 256 = Z.modulo y2 256 at hm2
  change Z.modulo x3 256 = Z.modulo y3 256 at hm3
  change Z.modulo x4 256 = Z.modulo y4 256 at hm4
  change Z.modulo x5 256 = Z.modulo y5 256 at hm5
  change Z.modulo x6 256 = Z.modulo y6 256 at hm6
  change Z.modulo x7 256 = Z.modulo y7 256 at hm7
  change Z.modulo x8 256 = Z.modulo y8 256 at hm8
  rw [show Z.pow 2 8 = 256 by decide, ← hm1, ← hm2, ← hm3, ← hm4,
    ← hm5, ← hm6, ← hm7, ← hm8]
  exact h

theorem merge_short_value_eqm (x1 x2 v v' : Int)
    (hm : Z.modulo v (Z.pow 2 16) = Z.modulo v' (Z.pow 2 16))
    (h : merge_short x1 x2 v) : merge_short x1 x2 v' := by
  unfold merge_short at h ⊢
  rw [← hm]
  exact h

theorem merge_int_value_eqm (x1 x2 x3 x4 v v' : Int)
    (hm : Z.modulo v (Z.pow 2 32) = Z.modulo v' (Z.pow 2 32))
    (h : merge_int x1 x2 x3 x4 v) : merge_int x1 x2 x3 x4 v' := by
  unfold merge_int at h ⊢
  rw [← hm]
  exact h

theorem merge_int64_value_eqm (x1 x2 x3 x4 x5 x6 x7 x8 v v' : Int)
    (hm : Z.modulo v (Z.pow 2 64) = Z.modulo v' (Z.pow 2 64))
    (h : merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v) :
    merge_int64 x1 x2 x3 x4 x5 x6 x7 x8 v' := by
  unfold merge_int64 at h ⊢
  rw [← hm]
  exact h

end LittleEndian

def LittleEndian : CEndianSig where
  bytes_eqm := LittleEndian.bytes_eqm
  n_bytes_to_Z := LittleEndian.n_bytes_to_Z
  Z_to_n_bytes := LittleEndian.Z_to_n_bytes
  merge_n_bytes := LittleEndian.merge_n_bytes
  merge_short := LittleEndian.merge_short
  merge_int := LittleEndian.merge_int
  merge_int64 := LittleEndian.merge_int64
  eqm_bytes_to_Z_eq := LittleEndian.eqm_bytes_to_Z_eq
  Z_to_n_bytes_to_Z := LittleEndian.Z_to_n_bytes_to_Z
  merge_n_bytes_self := LittleEndian.merge_n_bytes_self
  merge_byte_equiv_merge_n_bytes := LittleEndian.merge_byte_equiv_merge_n_bytes
  merge_short_equiv_merge_n_bytes := LittleEndian.merge_short_equiv_merge_n_bytes
  merge_int_equiv_merge_n_bytes := LittleEndian.merge_int_equiv_merge_n_bytes
  merge_int64_equiv_merge_n_bytes := LittleEndian.merge_int64_equiv_merge_n_bytes
  merge_short_eqm := LittleEndian.merge_short_eqm
  merge_int_eqm := LittleEndian.merge_int_eqm
  merge_int64_eqm := LittleEndian.merge_int64_eqm
  merge_short_value_eqm := LittleEndian.merge_short_value_eqm
  merge_int_value_eqm := LittleEndian.merge_int_value_eqm
  merge_int64_value_eqm := LittleEndian.merge_int64_value_eqm

end SimpleC.SL.CArch
