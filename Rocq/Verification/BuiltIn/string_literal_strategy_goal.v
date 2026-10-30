From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Local Open Scope sac.

Definition string_literal_strategy1 :=
  forall (addr : Z) (s : string) (LitMap : (string -> Z)),
    TT &&
    (“ (addr = (LitMap s)) ”) &&
    emp **
    ((GlobalStrings LitMap))
    |--
    (
    TT &&
    emp **
    ((GlobalStrings_missing LitMap (@cons string s (@nil string))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_stringLit addr s))
    ).

Definition string_literal_strategy3 :=
  forall (addr : Z) (s : string) (LitMap : (string -> Z)) (l : (@list string)),
    TT &&
    (“ (addr = (LitMap s)) ”) &&
    emp **
    ((GlobalStrings_missing LitMap l))
    |--
    (
    TT &&
    emp **
    ((GlobalStrings_missing LitMap (@cons string s l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_stringLit addr s))
    ).

Definition string_literal_strategy5 :=
  forall (i : Z) (s : string) (addr : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < ((StringLength s) + 1)) ”) &&
    emp **
    ((store_stringLit addr s))
    |--
    (
    TT &&
    emp **
    ((store_stringLit addr s))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth i (StringToList s (i + 1))  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char (addr + (i * sizeof(CHAR))) v))
      ).

Definition string_literal_strategy6 :=
  forall (addr : Z) (s1 : string),
    TT &&
    emp **
    ((store_stringLit addr s1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (s2 : string),
      TT &&
      (“ (s1 = s2) ”) &&
      emp -*
      TT &&
      emp **
      ((store_stringLit addr s2))
      ).

Definition string_literal_strategy7 :=
  forall (addr : Z) (s : string) (LitMap : (string -> Z)),
    TT &&
    (“ (addr = (LitMap s)) ”) &&
    emp **
    ((GlobalStrings LitMap)) **
    ((store_stringLit addr s))
    |--
    (
    TT &&
    emp **
    ((store_stringLit addr s)) **
    ((GlobalStrings_missing LitMap (@cons string s (@nil string))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition string_literal_strategy8 :=
  forall (i : Z) (zs : (@list Z)) (addr : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < ((string_length zs) + 1)) ”) &&
    emp **
    ((store_string addr zs))
    |--
    (
    TT &&
    emp **
    ((store_string addr zs))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth i (c_string zs)  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char (addr + (i * sizeof(CHAR))) v))
      ).

Definition string_literal_strategy2 :=
  forall (LitMap : (string -> Z)) (s : string),
    TT &&
    emp **
    ((GlobalStrings_missing LitMap (@cons string s (@nil string)))) **
    ((store_stringLit (LitMap s) s))
    |--
    (
    TT &&
    emp **
    ((GlobalStrings LitMap))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition string_literal_strategy4 :=
  forall (l : (@list string)) (LitMap : (string -> Z)) (s : string),
    TT &&
    emp **
    ((GlobalStrings_missing LitMap (@cons string s l))) **
    ((store_stringLit (LitMap s) s))
    |--
    (
    TT &&
    emp **
    ((GlobalStrings_missing LitMap l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type string_literal_Strategy_Correct.

  Axiom string_literal_strategy1_correctness : string_literal_strategy1.
  Axiom string_literal_strategy3_correctness : string_literal_strategy3.
  Axiom string_literal_strategy5_correctness : string_literal_strategy5.
  Axiom string_literal_strategy6_correctness : string_literal_strategy6.
  Axiom string_literal_strategy7_correctness : string_literal_strategy7.
  Axiom string_literal_strategy8_correctness : string_literal_strategy8.
  Axiom string_literal_strategy2_correctness : string_literal_strategy2.
  Axiom string_literal_strategy4_correctness : string_literal_strategy4.

End string_literal_Strategy_Correct.
