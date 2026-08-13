import SimpleC.SL.CommonAssertion.Core

namespace SimpleC.SL.CommonAssertion.DerivedPredSig

open AUXLib
open SimpleC.SL.CNotation
open Unifysl.LogicGenerator.demo932
open SimpleC.SL.CommonAssertion

variable (CRules : SeparationLogicSig)

def canonical : DerivedPredSig CRules := {}

abbrev store_byte : addr -> Int -> CRules.expr := CRules.mstore

def store_2byte (x : addr) (value : Int) : CRules.expr :=
  CRules.exp Int fun z1 =>
    CRules.exp Int fun z2 =>
      CRules.andp
        (CRules.coq_prop (merge_short z1 z2 value))
        (CRules.sepcon (store_byte CRules x z1) (store_byte CRules (x + 1) z2))

def store_4byte (x : addr) (value : Int) : CRules.expr :=
  CRules.exp Int fun z1 =>
    CRules.exp Int fun z2 =>
      CRules.exp Int fun z3 =>
        CRules.exp Int fun z4 =>
          CRules.andp
            (CRules.coq_prop (merge_int z1 z2 z3 z4 value))
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
                      (merge_int64 z1 z2 z3 z4 z5 z6 z7 z8 value))
                    (CRules.sepcon (store_byte CRules x z1)
                      (CRules.sepcon (store_byte CRules (x + 1) z2)
                        (CRules.sepcon (store_byte CRules (x + 2) z3)
                          (CRules.sepcon (store_byte CRules (x + 3) z4)
                            (CRules.sepcon (store_byte CRules (x + 4) z5)
                              (CRules.sepcon (store_byte CRules (x + 5) z6)
                                (CRules.sepcon (store_byte CRules (x + 6) z7)
                                  (store_byte CRules (x + 7) z8))))))))

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

def store_char (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_char x ∧ value <= Byte.max_signed ∧ value >= Byte.min_signed))
    (store_byte CRules x value)

def undef_store_char (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_char x)) (store_byte_noninit CRules x)

def store_uchar (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_char x ∧ value >= 0 ∧ value <= Byte.max_unsigned))
    (store_byte CRules x value)

def undef_store_uchar (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_char x)) (store_byte_noninit CRules x)

def store_short (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop (isvalidptr_short x ∧ value <= 32767 ∧ value >= -32768))
    (store_2byte CRules x value)

def undef_store_short (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_short x)) (store_2byte_noninit CRules x)

def store_ushort (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop (isvalidptr_short x ∧ value >= 0 ∧ value <= 65535))
    (store_2byte CRules x value)

def undef_store_ushort (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_short x)) (store_2byte_noninit CRules x)

def store_int (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int x ∧ value <= Int.max_signed ∧ value >= Int.min_signed))
    (store_4byte CRules x value)

def undef_store_int (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int x)) (store_4byte_noninit CRules x)

def store_uint (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int x ∧ value >= 0 ∧ value <= Int.max_unsigned))
    (store_4byte CRules x value)

def undef_store_uint (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int x)) (store_4byte_noninit CRules x)

def store_int64 (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int64 x ∧ value <= Int64.max_signed ∧ value >= Int64.min_signed))
    (store_8byte CRules x value)

def undef_store_int64 (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int64 x)) (store_8byte_noninit CRules x)

def store_uint64 (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop
      (isvalidptr_int64 x ∧ value >= 0 ∧ value <= Int64.max_unsigned))
    (store_8byte CRules x value)

def undef_store_uint64 (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr_int64 x)) (store_8byte_noninit CRules x)

def store_ptr (x : addr) (value : Int) : CRules.expr :=
  CRules.andp
    (CRules.coq_prop (isvalidptr x ∧ value >= 0 ∧ value <= Int.max_unsigned))
    (store_4byte CRules x value)

def undef_store_ptr (x : addr) : CRules.expr :=
  CRules.andp (CRules.coq_prop (isvalidptr x)) (store_4byte_noninit CRules x)

def Invalid_store (_x : addr) (_value : Int) : CRules.expr :=
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
      CRules.andp (CRules.coq_prop (isvalidptr x))
        (CRules.sepcon (store_4byte_noninit CRules x) (store_align4_list rest))

def store_align4_n (n : Int) : CRules.expr :=
  CRules.exp (List Int) fun addresses =>
    CRules.andp
      (CRules.coq_prop
        (Zlength addresses = n ∧ interval_list 3 0 Int.max_unsigned addresses))
      (store_align4_list CRules addresses)

def store_align_list : List Int -> CRules.expr
  | [] => CRules.emp
  | x :: rest =>
      CRules.andp (CRules.coq_prop (isvalidptr_char x))
        (CRules.sepcon (store_byte_noninit CRules x) (store_align_list rest))

def store_align_n (n : Int) : CRules.expr :=
  CRules.exp (List Int) fun addresses =>
    CRules.andp
      (CRules.coq_prop
        (Zlength addresses = n ∧ interval_list 0 0 Int.max_unsigned addresses))
      (store_align_list CRules addresses)

def poly_store : front_end_type -> addr -> Int -> CRules.expr
  | FET_int => store_int CRules
  | FET_char => store_char CRules
  | FET_int64 => store_int64 CRules
  | FET_short => store_short CRules
  | FET_uint => store_uint CRules
  | FET_uchar => store_uchar CRules
  | FET_uint64 => store_uint64 CRules
  | FET_ushort => store_ushort CRules
  | FET_ptr => store_ptr CRules
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ => Invalid_store CRules

def poly_undef_store : front_end_type -> addr -> CRules.expr
  | FET_int => undef_store_int CRules
  | FET_char => undef_store_char CRules
  | FET_int64 => undef_store_int64 CRules
  | FET_short => undef_store_short CRules
  | FET_uint => undef_store_uint CRules
  | FET_uchar => undef_store_uchar CRules
  | FET_uint64 => undef_store_uint64 CRules
  | FET_ushort => undef_store_ushort CRules
  | FET_ptr => undef_store_ptr CRules
  | FET_struct _ | FET_union _ | FET_enum _ | FET_alias _ => Invalid_undef_store CRules

def struct_padding (_x : lvalue_expr) (_struct_name : String) : CRules.expr :=
  CRules.emp

def union_padding (_x : lvalue_expr) (_union_name _field_name : String) : CRules.expr :=
  CRules.emp

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
