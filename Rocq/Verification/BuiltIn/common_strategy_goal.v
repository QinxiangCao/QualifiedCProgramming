From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition common_strategy0 :=
  forall (__builtin_A : Type) (x : __builtin_A),
    TT &&
    (“ (x = x) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy1 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (__builtin_A : Type) (x : __builtin_A),
    TT &&
    emp -*
    TT &&
    (“ (x = x) ”) &&
    emp
    ).

Definition common_strategy6 :=
  forall (ty : front_end_type) (y : (front_end_type_value ty)) (x : (front_end_type_value ty)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x))
    |--
    (
    TT &&
    (“ (should_be_equal x y) ”) &&
    emp **
    ((poly_store ty p x))
    ) ** (
    TT &&
    (“ (x = y) ”) &&
    emp **
    ((poly_store ty p y)) -*
    TT &&
    emp **
    ((poly_store ty p y))
    ).

Definition common_strategy19 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_int p x))
    |--
    (
    TT &&
    (“ (x >= (INT_MIN)) ”) &&
    emp **
    ((poly_store FET_int p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy20 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_int p x))
    |--
    (
    TT &&
    (“ (x <= (INT_MAX)) ”) &&
    emp **
    ((poly_store FET_int p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy21 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_uint p x))
    |--
    (
    TT &&
    (“ (x >= 0) ”) &&
    emp **
    ((poly_store FET_uint p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy22 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_uint p x))
    |--
    (
    TT &&
    (“ (x <= (UINT_MAX)) ”) &&
    emp **
    ((poly_store FET_uint p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy36 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_int64 p x))
    |--
    (
    TT &&
    (“ (x >= (INT64_MIN)) ”) &&
    emp **
    ((poly_store FET_int64 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy37 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_int64 p x))
    |--
    (
    TT &&
    (“ (x <= (INT64_MAX)) ”) &&
    emp **
    ((poly_store FET_int64 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy38 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_uint64 p x))
    |--
    (
    TT &&
    (“ (x >= 0) ”) &&
    emp **
    ((poly_store FET_uint64 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy39 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_uint64 p x))
    |--
    (
    TT &&
    (“ (x <= (UINT64_MAX)) ”) &&
    emp **
    ((poly_store FET_uint64 p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy46 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_bool p x))
    |--
    (
    TT &&
    (“ (x >= 0) ”) &&
    emp **
    ((poly_store FET_bool p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy47 :=
  forall (x : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_bool p x))
    |--
    (
    TT &&
    (“ (x <= 1) ”) &&
    emp **
    ((poly_store FET_bool p x))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy3 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (__builtin_A : Type) (y : __builtin_A) (x : __builtin_A),
    TT &&
    (“ (x = y) ” || “ (y = x) ”) &&
    emp -*
    TT &&
    (“ (x = y) ” || “ (y = x) ”) &&
    emp
    ).

Definition common_strategy15 :=
  forall (ty : front_end_type) (ty1 : front_end_type) (x : (front_end_type_value ty)) (y : (front_end_type_value ty1)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x)) **
    ((poly_store ty1 p y))
    |--
    (
    TT &&
    (“ (dup_data_at_error_prop) ”) &&
    emp **
    ((poly_store ty p x)) **
    ((poly_store ty1 p y))
    ) ** (
    TT &&
    emp **
    ((dup_data_at_error p)) -*
    TT &&
    emp
    ).

Definition common_strategy16 :=
  forall (ty : front_end_type) (ty1 : front_end_type) (x : (front_end_type_value ty)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x)) **
    ((poly_undef_store ty1 p))
    |--
    (
    TT &&
    (“ (dup_data_at_error_prop) ”) &&
    emp **
    ((poly_store ty p x)) **
    ((poly_undef_store ty1 p))
    ) ** (
    TT &&
    emp **
    ((dup_data_at_error p)) -*
    TT &&
    emp
    ).

Definition common_strategy17 :=
  forall (ty : front_end_type) (ty1 : front_end_type) (p : Z),
    TT &&
    emp **
    ((poly_undef_store ty p)) **
    ((poly_undef_store ty1 p))
    |--
    (
    TT &&
    (“ (dup_data_at_error_prop) ”) &&
    emp **
    ((poly_undef_store ty p)) **
    ((poly_undef_store ty1 p))
    ) ** (
    TT &&
    emp **
    ((dup_data_at_error p)) -*
    TT &&
    emp
    ).

Definition common_strategy12 :=
  forall (__builtin_A : Type) (b : __builtin_A) (a : __builtin_A),
    TT &&
    (“ (should_be_equal a b) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition common_strategy13 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (__builtin_A : Type) (b : __builtin_A) (a : __builtin_A),
    TT &&
    emp -*
    TT &&
    (“ (should_be_equal a b) ”) &&
    emp
    ).

Definition common_strategy18 :=
  TT &&
  (“ (dup_data_at_error_prop) ”) &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  TT &&
  emp -*
  TT &&
  emp
  ).

Definition common_strategy7 :=
  forall (ty : front_end_type) (x : (front_end_type_value ty)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_store ty p x))
    ).

Definition common_strategy8 :=
  forall (ty : front_end_type) (x : (front_end_type_value ty)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : (front_end_type_value ty)),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      (“ (x = y) ”) &&
      emp **
      ((poly_store ty p y))
      ).

Definition common_strategy9 :=
  forall (ty : front_end_type) (x : (front_end_type_value ty)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store ty p))
    ).

Definition common_strategy10 :=
  forall (ty : front_end_type) (p : Z),
    TT &&
    emp **
    ((poly_undef_store ty p))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store ty p))
    ).

Definition common_strategy11 :=
  forall (ty : front_end_type) (q : Z) (p : Z) (x : (front_end_type_value ty)),
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp **
    ((poly_store ty p x))
    |--
    (
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp
    ) ** (
    ALL (y : (front_end_type_value ty)),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store ty q y))
      ).

Definition common_strategy23 :=
  forall (n : Z),
    TT &&
    (“ (n > 0) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (x : Z),
      TT &&
      emp -*
      TT &&
      (“ ((unsigned_last_nbits x n) >= 0) ”) &&
      emp
      ).

Definition common_strategy14 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (ty : front_end_type) (x : (front_end_type_value ty)) (p : Z),
    TT &&
    emp **
    ((poly_store ty p x)) -*
    TT &&
    emp **
    ((poly_undef_store ty p))
    ).

Module Type common_Strategy_Correct.

  Axiom common_strategy0_correctness : common_strategy0.
  Axiom common_strategy1_correctness : common_strategy1.
  Axiom common_strategy6_correctness : common_strategy6.
  Axiom common_strategy19_correctness : common_strategy19.
  Axiom common_strategy20_correctness : common_strategy20.
  Axiom common_strategy21_correctness : common_strategy21.
  Axiom common_strategy22_correctness : common_strategy22.
  Axiom common_strategy36_correctness : common_strategy36.
  Axiom common_strategy37_correctness : common_strategy37.
  Axiom common_strategy38_correctness : common_strategy38.
  Axiom common_strategy39_correctness : common_strategy39.
  Axiom common_strategy46_correctness : common_strategy46.
  Axiom common_strategy47_correctness : common_strategy47.
  Axiom common_strategy3_correctness : common_strategy3.
  Axiom common_strategy15_correctness : common_strategy15.
  Axiom common_strategy16_correctness : common_strategy16.
  Axiom common_strategy17_correctness : common_strategy17.
  Axiom common_strategy12_correctness : common_strategy12.
  Axiom common_strategy13_correctness : common_strategy13.
  Axiom common_strategy18_correctness : common_strategy18.
  Axiom common_strategy7_correctness : common_strategy7.
  Axiom common_strategy8_correctness : common_strategy8.
  Axiom common_strategy9_correctness : common_strategy9.
  Axiom common_strategy10_correctness : common_strategy10.
  Axiom common_strategy11_correctness : common_strategy11.
  Axiom common_strategy23_correctness : common_strategy23.
  Axiom common_strategy14_correctness : common_strategy14.

End common_Strategy_Correct.
