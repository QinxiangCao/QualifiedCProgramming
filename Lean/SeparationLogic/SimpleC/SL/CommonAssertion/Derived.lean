import SimpleC.SL.CommonAssertion.Core
import SimpleC.SL.FloatLib

namespace SimpleC.SL.CommonAssertion.DerivedPredSig

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CArch
open SimpleC.SL.IntLib
open SimpleC.SL.FloatLib
open Unifysl.LogicGenerator.demo932
open SimpleC.SL.CommonAssertion

variable (Arch : CArchSig) (Endian : CEndianSig) (CRules : SeparationLogicSig)

def canonical : DerivedPredSig Arch Endian CRules := {}

noncomputable abbrev sizeof_front_end_type : front_end_type -> Int :=
  CNotationSig.sizeof_front_end_type Arch

theorem sizeof_int : sizeof_front_end_type Arch FET_int = 4 :=
  CNotationSig.sizeof_int Arch

theorem sizeof_char : sizeof_front_end_type Arch FET_char = 1 :=
  CNotationSig.sizeof_char Arch

theorem sizeof_int64 : sizeof_front_end_type Arch FET_int64 = 8 :=
  CNotationSig.sizeof_int64 Arch

theorem sizeof_short : sizeof_front_end_type Arch FET_short = 2 :=
  CNotationSig.sizeof_short Arch

theorem sizeof_uint : sizeof_front_end_type Arch FET_uint = 4 :=
  CNotationSig.sizeof_uint Arch

theorem sizeof_uchar : sizeof_front_end_type Arch FET_uchar = 1 :=
  CNotationSig.sizeof_uchar Arch

theorem sizeof_uint64 : sizeof_front_end_type Arch FET_uint64 = 8 :=
  CNotationSig.sizeof_uint64 Arch

theorem sizeof_int128 : sizeof_front_end_type Arch FET_int128 = 16 :=
  CNotationSig.sizeof_int128 Arch

theorem sizeof_uint128 : sizeof_front_end_type Arch FET_uint128 = 16 :=
  CNotationSig.sizeof_uint128 Arch

theorem sizeof_ushort : sizeof_front_end_type Arch FET_ushort = 2 :=
  CNotationSig.sizeof_ushort Arch

theorem sizeof_float : sizeof_front_end_type Arch FET_float = 4 :=
  CNotationSig.sizeof_float Arch

theorem sizeof_double : sizeof_front_end_type Arch FET_double = 8 :=
  CNotationSig.sizeof_double Arch

theorem sizeof_long_double : sizeof_front_end_type Arch FET_long_double = 16 :=
  CNotationSig.sizeof_long_double Arch

theorem sizeof_ptr :
    sizeof_front_end_type Arch FET_ptr = Arch.ptr_size_Z :=
  CNotationSig.sizeof_ptr Arch

abbrev eval_addr := CNotationSig.eval_addr Arch
abbrev addr_of_array_subst := CNotationSig.addr_of_array_subst Arch
abbrev addr_of_array_subst' := CNotationSig.addr_of_array_subst' Arch
abbrev const_array_pi := CNotationSig.const_array_pi Arch
abbrev const_array_pi' := CNotationSig.const_array_pi' Arch
abbrev addr_of_arrow_field := CNotationSig.addr_of_arrow_field Arch

abbrev addr_max_unsigned : Int := Arch.addr_max_unsigned
abbrev ptr_size : Nat := Arch.ptr_size
abbrev ptr_align : Int := Arch.ptr_align
abbrev ptr_size_Z : Int := Arch.ptr_size_Z
abbrev ptr_width_Z : Int := Arch.ptr_width_Z
abbrev aligned : Int -> Int -> Prop := Arch.aligned

abbrev bytes_eqm := Endian.bytes_eqm
abbrev n_bytes_to_Z := Endian.n_bytes_to_Z
abbrev Z_to_n_bytes := Endian.Z_to_n_bytes
abbrev merge_n_bytes := Endian.merge_n_bytes
abbrev merge_short := Endian.merge_short
abbrev merge_int := Endian.merge_int
abbrev merge_int64 := Endian.merge_int64

def vec1 (x : Int) : Vector Int 1 := #v[x]
def vec2 (x1 x2 : Int) : Vector Int 2 := #v[x1, x2]
def vec4 (x1 x2 x3 x4 : Int) : Vector Int 4 := #v[x1, x2, x3, x4]
def vec8 (x1 x2 x3 x4 x5 x6 x7 x8 : Int) : Vector Int 8 :=
  #v[x1, x2, x3, x4, x5, x6, x7, x8]

theorem ptr_size_32_or_64 : ptr_size Arch = 4 ∨ ptr_size Arch = 8 :=
  Arch.ptr_size_32_or_64

theorem ptr_size_pos : 0 < ptr_size_Z Arch :=
  Arch.ptr_size_pos

theorem ptr_align_pos : 0 < ptr_align Arch :=
  Arch.ptr_align_pos

theorem ptr_aligned_aligned_4 :
    ∀ x, aligned Arch (ptr_align Arch) x -> Z.modulo x 4 = 0 :=
  Arch.ptr_aligned_aligned_4

theorem addr_max_unsigned_ge_7 : 7 <= addr_max_unsigned Arch :=
  Arch.addr_max_unsigned_ge_7

theorem ptr_size_fits_addr : ptr_size_Z Arch - 1 <= addr_max_unsigned Arch :=
  Arch.ptr_size_fits_addr

theorem int_max_fits_addr : Int.max_unsigned <= addr_max_unsigned Arch :=
  Arch.int_max_fits_addr

theorem eqm_bytes_to_Z_eq (n : Nat) (v1 v2 : Vector Int n) :
    bytes_eqm Endian n v1 v2 ->
      n_bytes_to_Z Endian n v1 = n_bytes_to_Z Endian n v2 :=
  Endian.eqm_bytes_to_Z_eq n v1 v2

theorem Z_to_n_bytes_to_Z (length : Nat) (v : Int) :
    n_bytes_to_Z Endian length (Z_to_n_bytes Endian v length) =
      Z.modulo v (Z.pow 2 (8 * Int.ofNat length)) :=
  Endian.Z_to_n_bytes_to_Z length v

theorem merge_n_bytes_self (n : Nat) (v : Vector Int n) :
    merge_n_bytes Endian n v (n_bytes_to_Z Endian n v) :=
  Endian.merge_n_bytes_self n v

theorem merge_byte_equiv_merge_n_bytes (x y : Int) :
    Byte.eqm x y <-> merge_n_bytes Endian 1 (vec1 x) y :=
  Endian.merge_byte_equiv_merge_n_bytes x y

theorem merge_short_equiv_merge_n_bytes (x1 x2 y : Int) :
    merge_short Endian x1 x2 y <->
      merge_n_bytes Endian 2 (vec2 x1 x2) y :=
  Endian.merge_short_equiv_merge_n_bytes x1 x2 y

theorem merge_int_equiv_merge_n_bytes (x1 x2 x3 x4 y : Int) :
    merge_int Endian x1 x2 x3 x4 y <->
      merge_n_bytes Endian 4 (vec4 x1 x2 x3 x4) y :=
  Endian.merge_int_equiv_merge_n_bytes x1 x2 x3 x4 y

theorem merge_int64_equiv_merge_n_bytes
    (x1 x2 x3 x4 x5 x6 x7 x8 y : Int) :
    merge_int64 Endian x1 x2 x3 x4 x5 x6 x7 x8 y <->
      merge_n_bytes Endian 8 (vec8 x1 x2 x3 x4 x5 x6 x7 x8) y :=
  Endian.merge_int64_equiv_merge_n_bytes x1 x2 x3 x4 x5 x6 x7 x8 y

theorem merge_short_eqm
    (x1 x2 y1 y2 v : Int) (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2) :
    merge_short Endian x1 x2 v -> merge_short Endian y1 y2 v :=
  Endian.merge_short_eqm x1 x2 y1 y2 v h1 h2

theorem merge_int_eqm
    (x1 x2 x3 x4 y1 y2 y3 y4 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h3 : Byte.eqm x3 y3) (h4 : Byte.eqm x4 y4) :
    merge_int Endian x1 x2 x3 x4 v -> merge_int Endian y1 y2 y3 y4 v :=
  Endian.merge_int_eqm x1 x2 x3 x4 y1 y2 y3 y4 v h1 h2 h3 h4

theorem merge_int64_eqm
    (x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 y6 y7 y8 v : Int)
    (h1 : Byte.eqm x1 y1) (h2 : Byte.eqm x2 y2)
    (h3 : Byte.eqm x3 y3) (h4 : Byte.eqm x4 y4)
    (h5 : Byte.eqm x5 y5) (h6 : Byte.eqm x6 y6)
    (h7 : Byte.eqm x7 y7) (h8 : Byte.eqm x8 y8) :
    merge_int64 Endian x1 x2 x3 x4 x5 x6 x7 x8 v ->
      merge_int64 Endian y1 y2 y3 y4 y5 y6 y7 y8 v :=
  Endian.merge_int64_eqm x1 x2 x3 x4 x5 x6 x7 x8
    y1 y2 y3 y4 y5 y6 y7 y8 v h1 h2 h3 h4 h5 h6 h7 h8

theorem merge_short_value_eqm (x1 x2 v v' : Int)
    (h : Z.modulo v (Z.pow 2 16) = Z.modulo v' (Z.pow 2 16)) :
    merge_short Endian x1 x2 v -> merge_short Endian x1 x2 v' :=
  Endian.merge_short_value_eqm x1 x2 v v' h

theorem merge_int_value_eqm (x1 x2 x3 x4 v v' : Int)
    (h : Z.modulo v (Z.pow 2 32) = Z.modulo v' (Z.pow 2 32)) :
    merge_int Endian x1 x2 x3 x4 v -> merge_int Endian x1 x2 x3 x4 v' :=
  Endian.merge_int_value_eqm x1 x2 x3 x4 v v' h

theorem merge_int64_value_eqm (x1 x2 x3 x4 x5 x6 x7 x8 v v' : Int)
    (h : Z.modulo v (Z.pow 2 64) = Z.modulo v' (Z.pow 2 64)) :
    merge_int64 Endian x1 x2 x3 x4 x5 x6 x7 x8 v ->
      merge_int64 Endian x1 x2 x3 x4 x5 x6 x7 x8 v' :=
  Endian.merge_int64_value_eqm x1 x2 x3 x4 x5 x6 x7 x8 v v' h

abbrev valid_addr_range : Int -> Int -> Prop := Arch.valid_addr_range
abbrev valid_object : Int -> Int -> Int -> Prop := Arch.valid_object

def isvalidptr_char (x : Int) : Prop :=
  x >= 0 ∧ x <= addr_max_unsigned Arch

def isvalidptr_short (x : Int) : Prop :=
  x >= 0 ∧ x + 1 <= addr_max_unsigned Arch ∧ aligned_2 x

def isvalidptr_int (x : Int) : Prop :=
  x >= 0 ∧ x + 3 <= addr_max_unsigned Arch ∧ aligned_4 x

def isvalidptr_int64 (x : Int) : Prop :=
  x >= 0 ∧ x + 7 <= addr_max_unsigned Arch ∧ aligned_4 x

def isvalidptr_int128 (x : Int) : Prop :=
  x >= 0 ∧ x + 15 <= addr_max_unsigned Arch ∧ aligned_4 x

def isvalidptr_float (x : Int) : Prop :=
  x >= 0 ∧ x + 3 <= addr_max_unsigned Arch ∧ aligned_4 x

def isvalidptr_double (x : Int) : Prop :=
  x >= 0 ∧ x + 7 <= addr_max_unsigned Arch ∧ aligned_8 x

def isvalidptr_long_double (x : Int) : Prop :=
  x >= 0 ∧ x + 15 <= addr_max_unsigned Arch ∧ aligned_8 x

def isvalidptr (x : Int) : Prop :=
  x >= 0 ∧ x + ptr_size_Z Arch - 1 <= addr_max_unsigned Arch ∧
    Arch.aligned Arch.ptr_align x

abbrev valid_ptr_value : Int -> Prop := Arch.valid_ptr_value

include Arch Endian

abbrev store_byte : addr -> Int -> CRules.expr := CRules.mstore

def store_2byte (x : addr) (value : Int) : CRules.expr :=
  CRules.exp Int fun z1 =>
    CRules.exp Int fun z2 =>
      CRules.andp
        (CRules.coq_prop (merge_short Endian z1 z2 value))
        (CRules.sepcon (store_byte CRules x z1) (store_byte CRules (x + 1) z2))

def store_4byte (x : addr) (value : Int) : CRules.expr :=
  CRules.exp Int fun z1 =>
    CRules.exp Int fun z2 =>
      CRules.exp Int fun z3 =>
        CRules.exp Int fun z4 =>
          CRules.andp
            (CRules.coq_prop (merge_int Endian z1 z2 z3 z4 value))
            (CRules.sepcon (store_byte CRules x z1)
              (CRules.sepcon (store_byte CRules (x + 1) z2)
                (CRules.sepcon (store_byte CRules (x + 2) z3)
                  (store_byte CRules (x + 3) z4))))

def store_8byte (x : addr) (value : Int) : CRules.expr :=
  CRules.exp Int fun z1 =>
    CRules.exp Int fun z2 =>
      CRules.exp Int fun z3 =>
        CRules.exp Int fun z4 =>
          CRules.exp Int fun z5 =>
            CRules.exp Int fun z6 =>
              CRules.exp Int fun z7 =>
                CRules.exp Int fun z8 =>
                  CRules.andp
                    (CRules.coq_prop
                      (merge_int64 Endian z1 z2 z3 z4 z5 z6 z7 z8 value))
                    (CRules.sepcon (store_byte CRules x z1)
                      (CRules.sepcon (store_byte CRules (x + 1) z2)
                        (CRules.sepcon (store_byte CRules (x + 2) z3)
                          (CRules.sepcon (store_byte CRules (x + 3) z4)
                            (CRules.sepcon (store_byte CRules (x + 4) z5)
                              (CRules.sepcon (store_byte CRules (x + 5) z6)
                                (CRules.sepcon (store_byte CRules (x + 6) z7)
                                  (store_byte CRules (x + 7) z8))))))))

def store_bytes (x : addr) : (n : Nat) -> Vector Int n -> CRules.expr
  | 0, _ => CRules.emp
  | n + 1, bytes =>
      CRules.sepcon
        (store_byte CRules x (SimpleC.SL.CArch.vector_head bytes))
        (store_bytes (x + 1) n (SimpleC.SL.CArch.vector_tail bytes))

def store_16byte (x : addr) (value : Int) : CRules.expr :=
  CRules.exp (Vector Int 16) fun bytes =>
    CRules.andp
      (CRules.coq_prop (merge_n_bytes Endian 16 bytes value))
      (store_bytes CRules x 16 bytes)

abbrev store_byte_noninit : addr -> CRules.expr := CRules.mstore_noninit

def store_2byte_noninit (x : addr) : CRules.expr :=
  CRules.sepcon (store_byte_noninit CRules x) (store_byte_noninit CRules (x + 1))

def store_4byte_noninit (x : addr) : CRules.expr :=
  CRules.sepcon (store_byte_noninit CRules x)
    (CRules.sepcon (store_byte_noninit CRules (x + 1))
      (CRules.sepcon (store_byte_noninit CRules (x + 2))
        (store_byte_noninit CRules (x + 3))))

def store_8byte_noninit (x : addr) : CRules.expr :=
  CRules.sepcon (store_byte_noninit CRules x) <|
    CRules.sepcon (store_byte_noninit CRules (x + 1)) <|
      CRules.sepcon (store_byte_noninit CRules (x + 2)) <|
        CRules.sepcon (store_byte_noninit CRules (x + 3)) <|
          CRules.sepcon (store_byte_noninit CRules (x + 4)) <|
            CRules.sepcon (store_byte_noninit CRules (x + 5)) <|
              CRules.sepcon (store_byte_noninit CRules (x + 6))
                (store_byte_noninit CRules (x + 7))

def store_bytes_noninit (x : addr) : Nat -> CRules.expr
  | 0 => CRules.emp
  | n + 1 =>
      CRules.sepcon (store_byte_noninit CRules x)
        (store_bytes_noninit (x + 1) n)

def store_16byte_noninit (x : addr) : CRules.expr :=
  store_bytes_noninit CRules x 16

def store_char (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_char Arch x ∧ value <= Byte.max_signed ∧ value >= Byte.min_signed))
    (store_byte CRules x value)

def undef_store_char (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_char Arch x))
    (store_byte_noninit CRules x)

def store_uchar (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_char Arch x ∧ value >= 0 ∧ value <= Byte.max_unsigned))
    (store_byte CRules x value)

def undef_store_uchar (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_char Arch x))
    (store_byte_noninit CRules x)

def store_short (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_short Arch x ∧ value <= 32767 ∧ value >= -32768))
    (store_2byte Endian CRules x value)

def undef_store_short (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_short Arch x))
    (store_2byte_noninit CRules x)

def store_ushort (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_short Arch x ∧ value >= 0 ∧ value <= 65535))
    (store_2byte Endian CRules x value)

def undef_store_ushort (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_short Arch x))
    (store_2byte_noninit CRules x)

def store_int (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int Arch x ∧ value <= Int.max_signed ∧ value >= Int.min_signed))
    (store_4byte Endian CRules x value)

def undef_store_int (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int Arch x))
    (store_4byte_noninit CRules x)

def store_uint (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int Arch x ∧ value >= 0 ∧ value <= Int.max_unsigned))
    (store_4byte Endian CRules x value)

def undef_store_uint (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int Arch x))
    (store_4byte_noninit CRules x)

def store_int64 (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int64 Arch x ∧ value <= Int64.max_signed ∧ value >= Int64.min_signed))
    (store_8byte Endian CRules x value)

def undef_store_int64 (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int64 Arch x))
    (store_8byte_noninit CRules x)

def store_uint64 (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int64 Arch x ∧ value >= 0 ∧ value <= Int64.max_unsigned))
    (store_8byte Endian CRules x value)

def undef_store_uint64 (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int64 Arch x))
    (store_8byte_noninit CRules x)

def store_int128 (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int128 Arch x ∧ value <= Int128.max_signed ∧ value >= Int128.min_signed))
    (store_16byte Endian CRules x value)

def undef_store_int128 (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int128 Arch x))
    (store_16byte_noninit CRules x)

def store_uint128 (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int128 Arch x ∧ value >= 0 ∧ value <= Int128.max_unsigned))
    (store_16byte Endian CRules x value)

def undef_store_uint128 (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int128 Arch x))
    (store_16byte_noninit CRules x)

def store_float (x : addr) (value : fp32) : CRules.expr :=
  match bits_of_float_value value with
  | some z =>
      CRules.andp
        (CRules.coq_prop
          (isvalidptr_float Arch x ∧ 0 <= z ∧ z <= Int.max_unsigned))
        (store_4byte Endian CRules x z)
  | none => CRules.coq_prop False

def store_double (x : addr) (value : fp64) : CRules.expr :=
  match bits_of_double_value value with
  | some z =>
      CRules.andp
        (CRules.coq_prop
          (isvalidptr_double Arch x ∧ 0 <= z ∧ z <= Int64.max_unsigned))
        (store_8byte Endian CRules x z)
  | none => CRules.coq_prop False

def store_long_double (x : addr) (value : fp128) : CRules.expr :=
  match bits_of_long_double_value value with
  | some z =>
      CRules.andp
        (CRules.coq_prop
          (isvalidptr_long_double Arch x ∧ 0 <= z ∧ z <= max_unsigned_128))
        (store_16byte Endian CRules x z)
  | none => CRules.coq_prop False

def store_finite_float (x : addr) (value : fp32) : CRules.expr :=
  CRules.andp (CRules.coq_prop (fp32_isFinite value)) (store_float Arch Endian CRules x value)

def store_finite_double (x : addr) (value : fp64) : CRules.expr :=
  CRules.andp (CRules.coq_prop (fp64_isFinite value)) (store_double Arch Endian CRules x value)

def store_finite_long_double (x : addr) (value : fp128) : CRules.expr :=
  CRules.andp (CRules.coq_prop (fp128_isFinite value))
    (store_long_double Arch Endian CRules x value)

def undef_store_float (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_float Arch x))
    (store_4byte_noninit CRules x)

def undef_store_double (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_double Arch x))
    (store_8byte_noninit CRules x)

def undef_store_long_double (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_long_double Arch x))
    (store_16byte_noninit CRules x)

abbrev undef_store_finite_float : addr -> CRules.expr := undef_store_float Arch CRules
abbrev undef_store_finite_double : addr -> CRules.expr := undef_store_double Arch CRules
abbrev undef_store_finite_long_double : addr -> CRules.expr :=
  undef_store_long_double Arch CRules

def store_ptr (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop (isvalidptr Arch x ∧ valid_ptr_value Arch value))
    (match ptr_size Arch with
    | 4 => store_4byte Endian CRules x value
    | 8 => store_8byte Endian CRules x value
    | _ => CRules.coq_prop False)

def undef_store_ptr (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr Arch x))
    (match ptr_size Arch with
    | 4 => store_4byte_noninit CRules x
    | 8 => store_8byte_noninit CRules x
    | _ => CRules.coq_prop False)

def Invalid_store {A : Type} (_x : addr) (_value : A) : CRules.expr :=
  CRules.coq_prop False

def Invalid_undef_store (_x : addr) : CRules.expr :=
  CRules.coq_prop False

def dup_data_at_error (_x : addr) : CRules.expr :=
  CRules.coq_prop False

def dup_data_at_error_prop : Prop := True

def store_array_rec {A : Type}
    (storeA : addr -> Int -> A -> CRules.expr) (x : addr)
    (lo hi : Int) : List A -> CRules.expr
  | [] =>
      CRules.andp (CRules.coq_prop (lo = hi))
        (CRules.andp (CRules.coq_prop (([] : List A) = [])) CRules.emp)
  | a :: rest =>
      CRules.sepcon (storeA x lo a)
        (store_array_rec storeA x (lo + 1) hi rest)

def store_array_missing_i_rec {A : Type}
    (storeA : addr -> Int -> A -> CRules.expr) (x : addr)
    (i lo hi : Int) : List A -> CRules.expr
  | [] => CRules.coq_prop False
  | a :: rest =>
      CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo))
          (store_array_rec CRules storeA x (lo + 1) hi rest))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (storeA x lo a)
            (store_array_missing_i_rec storeA x i (lo + 1) hi rest)))

def store_array {A : Type}
    (storeA : addr -> Int -> A -> CRules.expr) (x : addr)
    (n : Int) (values : List A) : CRules.expr :=
  store_array_rec CRules storeA x 0 n values

def store_undef_array_rec
    (storeA : addr -> Int -> CRules.expr) (x : addr)
    (lo hi : Int) : Nat -> CRules.expr
  | 0 => CRules.andp (CRules.coq_prop (lo = hi)) CRules.emp
  | n + 1 =>
      CRules.sepcon (storeA x lo)
        (store_undef_array_rec storeA x (lo + 1) hi n)

def store_undef_array_missing_i_rec
    (storeA : addr -> Int -> CRules.expr) (x : addr)
    (i lo hi : Int) : Nat -> CRules.expr
  | 0 => CRules.coq_prop False
  | n + 1 =>
      CRules.orp
        (CRules.andp (CRules.coq_prop (i = lo))
          (store_undef_array_rec CRules storeA x (lo + 1) hi n))
        (CRules.andp (CRules.coq_prop (i > lo))
          (CRules.sepcon (storeA x lo)
            (store_undef_array_missing_i_rec storeA x i (lo + 1) hi n)))

def store_undef_array
    (storeA : addr -> Int -> CRules.expr) (x : addr) (n : Int) : CRules.expr :=
  store_undef_array_rec CRules storeA x 0 n n.toNat

def store_align4_list : List Int -> CRules.expr
  | [] => CRules.emp
  | x :: rest =>
      CRules.andp (CRules.coq_prop (isvalidptr_int Arch x))
        (CRules.sepcon (store_4byte_noninit CRules x) (store_align4_list rest))

def store_align4_n (n : Int) : CRules.expr :=
  CRules.exp (List Int) fun addresses =>
    CRules.andp
      (CRules.coq_prop
        (Zlength addresses = n ∧
          interval_list 3 0 (addr_max_unsigned Arch) addresses))
      (store_align4_list Arch CRules addresses)

def store_align_list : List Int -> CRules.expr
  | [] => CRules.emp
  | x :: rest =>
      CRules.andp (CRules.coq_prop (isvalidptr_char Arch x))
        (CRules.sepcon (store_byte_noninit CRules x) (store_align_list rest))

def store_align_n (n : Int) : CRules.expr :=
  CRules.exp (List Int) fun addresses =>
    CRules.andp
      (CRules.coq_prop
        (Zlength addresses = n ∧
          interval_list 0 0 (addr_max_unsigned Arch) addresses))
      (store_align_list Arch CRules addresses)

def front_end_type_value : front_end_type -> Type
  | FET_float => fp32
  | FET_double => fp64
  | FET_long_double => fp128
  | _ => Int

def typed_poly_store (type : front_end_type) :
    addr -> front_end_type_value type -> CRules.expr :=
  match type with
  | FET_int => store_int Arch Endian CRules
  | FET_char => store_char Arch CRules
  | FET_int64 => store_int64 Arch Endian CRules
  | FET_short => store_short Arch Endian CRules
  | FET_uint => store_uint Arch Endian CRules
  | FET_uchar => store_uchar Arch CRules
  | FET_uint64 => store_uint64 Arch Endian CRules
  | FET_int128 => store_int128 Arch Endian CRules
  | FET_uint128 => store_uint128 Arch Endian CRules
  | FET_ushort => store_ushort Arch Endian CRules
  | FET_float => store_float Arch Endian CRules
  | FET_double => store_double Arch Endian CRules
  | FET_long_double => store_long_double Arch Endian CRules
  | FET_ptr => store_ptr Arch Endian CRules
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ => Invalid_store CRules

def poly_store : front_end_type -> addr -> Int -> CRules.expr
  | FET_int => store_int Arch Endian CRules
  | FET_char => store_char Arch CRules
  | FET_int64 => store_int64 Arch Endian CRules
  | FET_short => store_short Arch Endian CRules
  | FET_uint => store_uint Arch Endian CRules
  | FET_uchar => store_uchar Arch CRules
  | FET_uint64 => store_uint64 Arch Endian CRules
  | FET_int128 => store_int128 Arch Endian CRules
  | FET_uint128 => store_uint128 Arch Endian CRules
  | FET_ushort => store_ushort Arch Endian CRules
  | FET_float => fun x z => store_float Arch Endian CRules x (fp32_of_bits z)
  | FET_double => fun x z => store_double Arch Endian CRules x (fp64_of_bits z)
  | FET_long_double => fun x z => store_long_double Arch Endian CRules x (fp128_of_bits z)
  | FET_ptr => store_ptr Arch Endian CRules
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ => Invalid_store CRules

def poly_undef_store : front_end_type -> addr -> CRules.expr
  | FET_int => undef_store_int Arch CRules
  | FET_char => undef_store_char Arch CRules
  | FET_int64 => undef_store_int64 Arch CRules
  | FET_short => undef_store_short Arch CRules
  | FET_uint => undef_store_uint Arch CRules
  | FET_uchar => undef_store_uchar Arch CRules
  | FET_uint64 => undef_store_uint64 Arch CRules
  | FET_int128 => undef_store_int128 Arch CRules
  | FET_uint128 => undef_store_uint128 Arch CRules
  | FET_ushort => undef_store_ushort Arch CRules
  | FET_float => undef_store_float Arch CRules
  | FET_double => undef_store_double Arch CRules
  | FET_long_double => undef_store_long_double Arch CRules
  | FET_ptr => undef_store_ptr Arch CRules
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ => Invalid_undef_store CRules

def struct_padding (_x : lvalue_expr) (_struct_name : String) : CRules.expr :=
  CRules.emp

def union_padding (_x : lvalue_expr) (_union_name _field_name : String) : CRules.expr :=
  CRules.emp

omit Arch Endian

theorem coq_prop_andp_left (P : Prop) (Q R : CRules.expr)
    (h : P -> CRules.derivable1 Q R) :
    CRules.derivable1 (CRules.andp (CRules.coq_prop P) Q) R := by
  intro state hPQ
  exact h hPQ.1 state hPQ.2

theorem coq_prop_andp_right (P : Prop) (Q R : CRules.expr)
    (hRQ : CRules.derivable1 R Q) (hP : P) :
    CRules.derivable1 R (CRules.andp (CRules.coq_prop P) Q) := by
  intro state hR
  exact ⟨hP, hRQ state hR⟩

theorem coq_prop_imply (P Q : Prop) (h : P -> Q) :
    CRules.derivable1 (CRules.coq_prop P) (CRules.coq_prop Q) := by
  intro _ hP
  exact h hP

theorem coq_prop_False_left (P : Prop) (Q : CRules.expr) (h : P -> False) :
    CRules.derivable1 (CRules.coq_prop P) Q := by
  intro _ hP
  exact False.elim (h hP)

theorem orp_sepcon_left (P Q R : CRules.expr) :
    CRules.derivable1 (CRules.sepcon (CRules.orp P Q) R)
      (CRules.orp (CRules.sepcon P R) (CRules.sepcon Q R)) := by
  intro state h
  rcases h with ⟨s1, s2, hj, hPQ, hR⟩
  rcases hPQ with hP | hQ
  · exact Or.inl ⟨s1, s2, hj, hP, hR⟩
  · exact Or.inr ⟨s1, s2, hj, hQ, hR⟩

theorem orp_sepcon_right (P Q R : CRules.expr) :
    CRules.derivable1 (CRules.sepcon P (CRules.orp Q R))
      (CRules.orp (CRules.sepcon P Q) (CRules.sepcon P R)) := by
  intro state h
  rcases h with ⟨s1, s2, hj, hP, hQR⟩
  rcases hQR with hQ | hR
  · exact Or.inl ⟨s1, s2, hj, hP, hQ⟩
  · exact Or.inr ⟨s1, s2, hj, hP, hR⟩

theorem orp_sepcon_left' (P Q R : CRules.expr) :
    CRules.derivable1 (CRules.orp (CRules.sepcon P R) (CRules.sepcon Q R))
      (CRules.sepcon (CRules.orp P Q) R) := by
  intro state h
  rcases h with h | h
  · rcases h with ⟨s1, s2, hj, hP, hR⟩
    exact ⟨s1, s2, hj, Or.inl hP, hR⟩
  · rcases h with ⟨s1, s2, hj, hQ, hR⟩
    exact ⟨s1, s2, hj, Or.inr hQ, hR⟩

theorem orp_sepcon_right' (P Q R : CRules.expr) :
    CRules.derivable1 (CRules.orp (CRules.sepcon P Q) (CRules.sepcon P R))
      (CRules.sepcon P (CRules.orp Q R)) := by
  intro state h
  rcases h with h | h
  · rcases h with ⟨s1, s2, hj, hP, hQ⟩
    exact ⟨s1, s2, hj, hP, Or.inl hQ⟩
  · rcases h with ⟨s1, s2, hj, hP, hR⟩
    exact ⟨s1, s2, hj, hP, Or.inr hR⟩

theorem orp_sepcon_left_equiv (P Q R : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon (CRules.orp P Q) R)
      (CRules.orp (CRules.sepcon P R) (CRules.sepcon Q R)) :=
  ⟨orp_sepcon_left CRules P Q R, orp_sepcon_left' CRules P Q R⟩

theorem orp_sepcon_right_equiv (P Q R : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon P (CRules.orp Q R))
      (CRules.orp (CRules.sepcon P Q) (CRules.sepcon P R)) :=
  ⟨orp_sepcon_right CRules P Q R, orp_sepcon_right' CRules P Q R⟩

theorem exp_right_exists {A : Type} (P : CRules.expr) (Q : A -> CRules.expr)
    (h : exists x, CRules.derivable1 P (Q x)) :
    CRules.derivable1 P (CRules.exp A Q) := by
  rcases h with ⟨x, hx⟩
  intro state hP
  exact ⟨x, hx state hP⟩

theorem derivable1_imp (P Q : CRules.expr) (state : CRules.model)
    (hPQ : CRules.derivable1 P Q) (hP : P state) : Q state :=
  hPQ state hP

theorem derivable1_andp_mono (x1 x2 y1 y2 : CRules.expr)
    (hx : CRules.derivable1 x1 x2) (hy : CRules.derivable1 y1 y2) :
    CRules.derivable1 (CRules.andp x1 y1) (CRules.andp x2 y2) := by
  intro state h
  exact ⟨hx state h.1, hy state h.2⟩

theorem ex_logic_equiv_andp {A : Type} (P : A -> CRules.expr) (Q : CRules.expr) :
    CRules.logic_equiv (CRules.andp (CRules.exp A P) Q)
      (CRules.exp A fun x => CRules.andp (P x) Q) := by
  constructor
  · intro state h
    rcases h.1 with ⟨x, hx⟩
    exact ⟨x, hx, h.2⟩
  · intro state h
    rcases h with ⟨x, hx, hQ⟩
    exact ⟨⟨x, hx⟩, hQ⟩

theorem wand_equiv (P Q P' Q' : CRules.expr)
    (hP : CRules.logic_equiv P P') (hQ : CRules.logic_equiv Q Q') :
    CRules.logic_equiv (CRules.wand P Q) (CRules.wand P' Q') := by
  constructor
  · intro state h m1 m2 hj hP'
    exact hQ.1 m2 (h m1 m2 hj (hP.2 m1 hP'))
  · intro state h m1 m2 hj hp
    exact hQ.2 m2 (h m1 m2 hj (hP.1 m1 hp))

theorem ex_logic_equiv_sepcon {A : Type}
    (P : A -> CRules.expr) (Q : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon (CRules.exp A P) Q)
      (CRules.exp A fun x => CRules.sepcon (P x) Q) := by
  constructor
  · intro state h
    rcases h with ⟨s1, s2, hj, ⟨x, hx⟩, hQ⟩
    exact ⟨x, s1, s2, hj, hx, hQ⟩
  · intro state h
    rcases h with ⟨x, s1, s2, hj, hx, hQ⟩
    exact ⟨s1, s2, hj, ⟨x, hx⟩, hQ⟩

theorem prop_add_left (P : CRules.expr) (Q : Prop)
    (h : CRules.derivable1 P (CRules.coq_prop Q)) :
    CRules.logic_equiv P (CRules.andp (CRules.coq_prop Q) P) := by
  constructor
  · intro state hP
    exact ⟨h state hP, hP⟩
  · intro _ hQP
    exact hQP.2

theorem truep_andp_left_equiv (P : CRules.expr) :
    CRules.logic_equiv (CRules.andp CRules.truep P) P := by
  constructor <;> intro state h
  · exact h.2
  · exact ⟨True.intro, h⟩

theorem truep_andp_right_equiv (P : CRules.expr) :
    CRules.logic_equiv (CRules.andp P CRules.truep) P := by
  constructor <;> intro state h
  · exact h.1
  · exact ⟨h, True.intro⟩

theorem sepcon_emp_equiv (P : CRules.expr) :
    CRules.logic_equiv (CRules.sepcon P CRules.emp) P :=
  CRules.toContext.logic_equiv_sepcon_emp P

theorem sepcon_cancel_res_emp (P Q : CRules.expr)
    (hQ : CRules.derivable1 CRules.emp Q) :
    CRules.derivable1 P (CRules.sepcon P Q) := by
  exact CRules.toContext.derivable1_trans P (CRules.sepcon P CRules.emp)
    (CRules.sepcon P Q)
    (CRules.toContext.derivable1_sepcon_emp_r P)
    (CRules.toContext.derivable1_sepcon_mono P P CRules.emp Q
      (CRules.toContext.derivable1_refl P) hQ)

theorem sepcon_cancel_end (P Q R : CRules.expr)
    (hR : CRules.derivable1 P R) (hQ : CRules.derivable1 CRules.emp Q) :
    CRules.derivable1 P (CRules.sepcon R Q) := by
  exact CRules.toContext.derivable1_trans P (CRules.sepcon P CRules.emp)
    (CRules.sepcon R Q)
    (CRules.toContext.derivable1_sepcon_emp_r P)
    (CRules.toContext.derivable1_sepcon_mono P R CRules.emp Q hR hQ)

theorem sepcon_prop_equiv (P : CRules.expr) (Q : Prop) :
    CRules.logic_equiv (CRules.sepcon P (CRules.coq_prop Q))
      (CRules.andp (CRules.coq_prop Q) (CRules.sepcon P CRules.truep)) := by
  constructor
  · intro state h
    rcases h with ⟨s1, s2, hj, hP, hQ⟩
    exact ⟨hQ, ⟨s1, s2, hj, hP, True.intro⟩⟩
  · intro state h
    rcases h.2 with ⟨s1, s2, hj, hP, _⟩
    exact ⟨s1, s2, hj, hP, h.1⟩

theorem exp_exp_right {A : Type} (P : CRules.expr) (Q : A -> CRules.expr)
    (h : exists x, CRules.derivable1 P (Q x)) :
    CRules.derivable1 P (CRules.exp A Q) :=
  exp_right_exists CRules P Q h

theorem exp_allp_left {A : Type} (P : A -> CRules.expr) (Q : CRules.expr)
    (h : exists x, CRules.derivable1 (P x) Q) :
    CRules.derivable1 (CRules.allp A P) Q := by
  rcases h with ⟨x, hx⟩
  intro state hP
  exact hx state (hP x)

theorem exp_allp_swap {A B : Type} (P : A -> B -> CRules.expr) :
    CRules.derivable1 (CRules.exp A fun x => CRules.allp B fun y => P x y)
      (CRules.allp B fun y => CRules.exp A fun x => P x y) := by
  intro state h y
  rcases h with ⟨x, hx⟩
  exact ⟨x, hx y⟩

theorem allp_allp_swap {A B : Type} (P : A -> B -> CRules.expr) :
    CRules.derivable1 (CRules.allp A fun x => CRules.allp B fun y => P x y)
      (CRules.allp B fun y => CRules.allp A fun x => P x y) := by
  intro state h y x
  exact h x y

abbrev derivable1_wand_sepcon_adjoint :=
  CRules.toContext.derivable1s_wand_sepcon_adjoint

end SimpleC.SL.CommonAssertion.DerivedPredSig

namespace SimpleC.SL.CommonAssertion.DerivedPredSigCompat

open SimpleC.SL.CArch
open SimpleC.SL.CommonAssertion

/-!
Legacy Arch32/BigEndian compatibility view retained for callers migrated before
the architecture parameterization. Canonical P0-7/P0-8 code uses
`DerivedPredSig` with explicit architecture and endian arguments; new code must
not extend this fixed view.
-/

abbrev Sig (CRules : SeparationLogicSig) :=
  DerivedPredSig CArch.Arch32 CArch.BigEndian CRules

def canonical (CRules : SeparationLogicSig) : Sig CRules :=
  DerivedPredSig.canonical CArch.Arch32 CArch.BigEndian CRules

abbrev store_2byte := DerivedPredSig.store_2byte CArch.BigEndian
abbrev store_4byte := DerivedPredSig.store_4byte CArch.BigEndian
abbrev store_8byte := DerivedPredSig.store_8byte CArch.BigEndian
abbrev store_16byte := DerivedPredSig.store_16byte CArch.BigEndian

abbrev store_char := DerivedPredSig.store_char CArch.Arch32
abbrev undef_store_char := DerivedPredSig.undef_store_char CArch.Arch32
abbrev store_uchar := DerivedPredSig.store_uchar CArch.Arch32
abbrev undef_store_uchar := DerivedPredSig.undef_store_uchar CArch.Arch32
abbrev store_short := DerivedPredSig.store_short CArch.Arch32 CArch.BigEndian
abbrev undef_store_short := DerivedPredSig.undef_store_short CArch.Arch32
abbrev store_ushort := DerivedPredSig.store_ushort CArch.Arch32 CArch.BigEndian
abbrev undef_store_ushort := DerivedPredSig.undef_store_ushort CArch.Arch32
abbrev store_int := DerivedPredSig.store_int CArch.Arch32 CArch.BigEndian
abbrev undef_store_int := DerivedPredSig.undef_store_int CArch.Arch32
abbrev store_uint := DerivedPredSig.store_uint CArch.Arch32 CArch.BigEndian
abbrev undef_store_uint := DerivedPredSig.undef_store_uint CArch.Arch32
abbrev store_int64 := DerivedPredSig.store_int64 CArch.Arch32 CArch.BigEndian
abbrev undef_store_int64 := DerivedPredSig.undef_store_int64 CArch.Arch32
abbrev store_uint64 := DerivedPredSig.store_uint64 CArch.Arch32 CArch.BigEndian
abbrev undef_store_uint64 := DerivedPredSig.undef_store_uint64 CArch.Arch32
abbrev store_int128 := DerivedPredSig.store_int128 CArch.Arch32 CArch.BigEndian
abbrev undef_store_int128 := DerivedPredSig.undef_store_int128 CArch.Arch32
abbrev store_uint128 := DerivedPredSig.store_uint128 CArch.Arch32 CArch.BigEndian
abbrev undef_store_uint128 := DerivedPredSig.undef_store_uint128 CArch.Arch32
abbrev store_float := DerivedPredSig.store_float CArch.Arch32 CArch.BigEndian
abbrev undef_store_float := DerivedPredSig.undef_store_float CArch.Arch32
abbrev store_double := DerivedPredSig.store_double CArch.Arch32 CArch.BigEndian
abbrev undef_store_double := DerivedPredSig.undef_store_double CArch.Arch32
abbrev store_long_double :=
  DerivedPredSig.store_long_double CArch.Arch32 CArch.BigEndian
abbrev undef_store_long_double := DerivedPredSig.undef_store_long_double CArch.Arch32
abbrev store_finite_float :=
  DerivedPredSig.store_finite_float CArch.Arch32 CArch.BigEndian
abbrev store_finite_double :=
  DerivedPredSig.store_finite_double CArch.Arch32 CArch.BigEndian
abbrev store_finite_long_double :=
  DerivedPredSig.store_finite_long_double CArch.Arch32 CArch.BigEndian
abbrev undef_store_finite_float :=
  DerivedPredSig.undef_store_finite_float CArch.Arch32
abbrev undef_store_finite_double :=
  DerivedPredSig.undef_store_finite_double CArch.Arch32
abbrev undef_store_finite_long_double :=
  DerivedPredSig.undef_store_finite_long_double CArch.Arch32
abbrev store_ptr := DerivedPredSig.store_ptr CArch.Arch32 CArch.BigEndian
abbrev undef_store_ptr := DerivedPredSig.undef_store_ptr CArch.Arch32

abbrev store_align4_list := DerivedPredSig.store_align4_list CArch.Arch32
abbrev store_align4_n := DerivedPredSig.store_align4_n CArch.Arch32
abbrev store_align_list := DerivedPredSig.store_align_list CArch.Arch32
abbrev store_align_n := DerivedPredSig.store_align_n CArch.Arch32
abbrev typed_poly_store :=
  DerivedPredSig.typed_poly_store CArch.Arch32 CArch.BigEndian
abbrev poly_store := DerivedPredSig.poly_store CArch.Arch32 CArch.BigEndian
abbrev poly_undef_store := DerivedPredSig.poly_undef_store CArch.Arch32

end SimpleC.SL.CommonAssertion.DerivedPredSigCompat
