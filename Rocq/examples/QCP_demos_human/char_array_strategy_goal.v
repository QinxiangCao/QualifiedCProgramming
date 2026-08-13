Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition char_array_strategy1 :=
  forall (i : Z) (n : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((CharArray.full p n l))
    |--
    (
    TT &&
    emp **
    ((CharArray.missing_i p i 0 n l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth i l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) v))
      ).

Definition char_array_strategy4 :=
  forall (p : Z) (l1 : (@list Z)) (n : Z),
    TT &&
    emp **
    ((CharArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((CharArray.full p n l2))
      ).

Definition char_array_strategy5 :=
  forall (p : Z) (v : Z) (l : (@list Z)) (n : Z) (i : Z),
    TT &&
    emp **
    ((CharArray.missing_i p i v n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray.missing_i p i v n l))
    ).

Definition char_array_strategy6 :=
  forall (n : Z) (p : Z) (l1 : (@list Z)),
    TT &&
    emp **
    ((CharArray.full p n l1))
    |--
    (
    TT &&
    (“ (Z.le 0 n) ”) &&
    emp **
    ((CharArray.full p n l1))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition char_array_strategy7 :=
  forall (n : Z),
    TT &&
    (“ (n = 0) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (l = (@nil Z)) ”) &&
      emp -*
      TT &&
      emp **
      ((CharArray.full p n l))
      ).

Definition char_array_strategy8 :=
  forall (l : Z),
    TT &&
    (“ (l = 0) ”) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (p : Z) (r : Z),
      TT &&
      emp **
      ((CharArray.undef_full p r)) -*
      TT &&
      emp **
      ((CharArray.undef_seg p l r))
      ).

Definition char_array_strategy9 :=
  forall (i : Z) (n : Z) (l : Z) (p : Z),
    TT &&
    (“ (Z.le l i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((CharArray.undef_seg p l n))
    |--
    (
    TT &&
    emp **
    ((CharArray.undef_missing_i p i l n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char)))))
    ).

Definition char_array_strategy2 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((CharArray.missing_i p i 0 n l)) **
    ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) (Znth i l  0)))
    |--
    (
    TT &&
    emp **
    ((CharArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition char_array_strategy11 :=
  forall (r : Z) (n : Z) (l : Z) (p : Z),
    TT &&
    (“ (l = r) ”) &&
    (“ (Z.lt r n) ”) &&
    emp **
    ((CharArray.undef_missing_i p l r n))
    |--
    (
    TT &&
    emp **
    ((CharArray.undef_seg p (Z.add l 1) n))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition char_array_strategy3 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((CharArray.missing_i p i 0 n l)) **
    ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) v))
    |--
    (
    TT &&
    emp **
    ((CharArray.full p n (@replace_Znth Z i v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition char_array_strategy10 :=
  forall (i : Z) (n : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    (“ (i = n) ”) &&
    emp **
    ((CharArray.full p n l)) **
    ((poly_store FET_char (Z.add p (Z.mul i (@sizeof_front_end_type FET_char))) v))
    |--
    (
    TT &&
    emp **
    ((CharArray.full p (Z.add n 1) (@app Z l (@cons Z v (@nil Z)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type char_array_Strategy_Correct.

  Axiom char_array_strategy1_correctness : char_array_strategy1.
  Axiom char_array_strategy4_correctness : char_array_strategy4.
  Axiom char_array_strategy5_correctness : char_array_strategy5.
  Axiom char_array_strategy6_correctness : char_array_strategy6.
  Axiom char_array_strategy7_correctness : char_array_strategy7.
  Axiom char_array_strategy8_correctness : char_array_strategy8.
  Axiom char_array_strategy9_correctness : char_array_strategy9.
  Axiom char_array_strategy2_correctness : char_array_strategy2.
  Axiom char_array_strategy11_correctness : char_array_strategy11.
  Axiom char_array_strategy3_correctness : char_array_strategy3.
  Axiom char_array_strategy10_correctness : char_array_strategy10.

End char_array_Strategy_Correct.
