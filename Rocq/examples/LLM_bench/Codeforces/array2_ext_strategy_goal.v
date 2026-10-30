From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.array2_ext_lib.
Local Open Scope sac.

Definition array2_ext_strategy1 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_missing_i (p + ((i * m) * sizeof(INT))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Array2.mixed_val (Znth i rows __default_app1_app1_Z) j)) ”) &&
      (“ (Array2.mixed_def (Znth i rows __default_app1_app1_Z) j) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int ((p + ((i * m) * sizeof(INT))) + (j * sizeof(INT))) v))
      ).

Definition array2_ext_strategy2 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_missing_i (p + ((i * m) * sizeof(INT))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Array2.mixed_val (Znth i rows __default_app1_app1_Z) j)) ”) &&
      (“ (Array2.mixed_def (Znth i rows __default_app1_app1_Z) j) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (p + (((i * m) + j) * sizeof(INT))) v))
      ).

Definition array2_ext_strategy3 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_missing_i (p + (i * (w * sizeof(INT)))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Array2.mixed_val (Znth i rows __default_app1_app1_Z) j)) ”) &&
      (“ (Array2.mixed_def (Znth i rows __default_app1_app1_Z) j) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int ((p + (i * (w * sizeof(INT)))) + (j * sizeof(INT))) v))
      ).

Definition array2_ext_strategy4 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_missing_i (p + ((i * m) * sizeof(INT))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int ((p + ((i * m) * sizeof(INT))) + (j * sizeof(INT)))))
    ).

Definition array2_ext_strategy5 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_missing_i (p + ((i * m) * sizeof(INT))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int (p + (((i * m) + j) * sizeof(INT)))))
    ).

Definition array2_ext_strategy6 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_missing_i (p + (i * (w * sizeof(INT)))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_int ((p + (i * (w * sizeof(INT)))) + (j * sizeof(INT)))))
    ).

Definition array2_ext_strategy13 :=
  forall (p : Z) (m : Z) (rows : (@list (@list (@option Z)))) (n : Z),
    TT &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list (@list Z))),
      TT &&
      (“ (rows = (Array2.some_rows l)) ”) &&
      emp -*
      TT &&
      emp **
      ((IntArray2.full p n m l))
      ).

Definition array2_ext_strategy14 :=
  forall (p : Z) (m : Z) (rows : (@list (@list (@option Z)))) (n : Z),
    TT &&
    emp **
    ((IntArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray2.undef_full p n m))
    ).

Definition array2_ext_strategy15 :=
  forall (p : Z) (m : Z) (rows : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((IntArray2.full p n m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray2.undef_full p n m))
    ).

Definition array2_ext_strategy19 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_missing_i (p + ((i * m) * sizeof(CHAR))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Array2.mixed_val (Znth i rows __default_app1_app1_Z) j)) ”) &&
      (“ (Array2.mixed_def (Znth i rows __default_app1_app1_Z) j) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char ((p + ((i * m) * sizeof(CHAR))) + (j * sizeof(CHAR))) v))
      ).

Definition array2_ext_strategy20 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_missing_i (p + ((i * m) * sizeof(CHAR))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Array2.mixed_val (Znth i rows __default_app1_app1_Z) j)) ”) &&
      (“ (Array2.mixed_def (Znth i rows __default_app1_app1_Z) j) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char (p + (((i * m) + j) * sizeof(CHAR))) v))
      ).

Definition array2_ext_strategy21 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_missing_i (p + (i * (w * sizeof(CHAR)))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Array2.mixed_val (Znth i rows __default_app1_app1_Z) j)) ”) &&
      (“ (Array2.mixed_def (Znth i rows __default_app1_app1_Z) j) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_char ((p + (i * (w * sizeof(CHAR)))) + (j * sizeof(CHAR))) v))
      ).

Definition array2_ext_strategy22 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_missing_i (p + ((i * m) * sizeof(CHAR))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_char ((p + ((i * m) * sizeof(CHAR))) + (j * sizeof(CHAR)))))
    ).

Definition array2_ext_strategy23 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_missing_i (p + ((i * m) * sizeof(CHAR))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_char (p + (((i * m) + j) * sizeof(CHAR)))))
    ).

Definition array2_ext_strategy24 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (__default_app1_app1_Z : (@list (@option Z))) (p : Z) (rows : (@list (@list (@option Z)))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_missing_i (p + (i * (w * sizeof(CHAR)))) j 0 m (Znth i rows __default_app1_app1_Z)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_undef_store FET_char ((p + (i * (w * sizeof(CHAR)))) + (j * sizeof(CHAR)))))
    ).

Definition array2_ext_strategy31 :=
  forall (p : Z) (m : Z) (rows : (@list (@list (@option Z)))) (n : Z),
    TT &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list (@list Z))),
      TT &&
      (“ (rows = (Array2.some_rows l)) ”) &&
      emp -*
      TT &&
      emp **
      ((CharArray2.full p n m l))
      ).

Definition array2_ext_strategy32 :=
  forall (p : Z) (m : Z) (rows : (@list (@list (@option Z)))) (n : Z),
    TT &&
    emp **
    ((CharArray2.mixed_full p n m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray2.undef_full p n m))
    ).

Definition array2_ext_strategy33 :=
  forall (p : Z) (m : Z) (rows : (@list (@list Z))) (n : Z),
    TT &&
    emp **
    ((CharArray2.full p n m rows))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray2.undef_full p n m))
    ).

Definition array2_ext_strategy7 :=
  forall (i : Z) (n : Z) (rows : (@list (@list (@option Z)))) (m : Z) (p : Z) (row : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_full (p + ((i * m) * sizeof(INT))) m row))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_full p n m (Array2.replace_mixed_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy8 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (rows : (@list (@list (@option Z)))) (p : Z) (row : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_full (p + (i * (w * sizeof(INT)))) m row))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_full p n m (Array2.replace_mixed_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy9 :=
  forall (i : Z) (n : Z) (rows : (@list (@list (@option Z)))) (m : Z) (p : Z) (row : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((IntArray2.mixed_missing_i p i 0 n m rows)) **
    ((IntArray.mixed_full (p + ((i * m) * sizeof(INT))) m row))
    |--
    (
    TT &&
    emp **
    ((IntArray2.mixed_full p n m (Array2.replace_mixed_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy25 :=
  forall (i : Z) (n : Z) (rows : (@list (@list (@option Z)))) (m : Z) (p : Z) (row : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_full (p + ((i * m) * sizeof(CHAR))) m row))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_full p n m (Array2.replace_mixed_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy26 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (rows : (@list (@list (@option Z)))) (p : Z) (row : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_full (p + (i * (w * sizeof(CHAR)))) m row))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_full p n m (Array2.replace_mixed_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy27 :=
  forall (i : Z) (n : Z) (rows : (@list (@list (@option Z)))) (m : Z) (p : Z) (row : (@list (@option Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharArray2.mixed_missing_i p i 0 n m rows)) **
    ((CharArray.mixed_full (p + ((i * m) * sizeof(CHAR))) m row))
    |--
    (
    TT &&
    emp **
    ((CharArray2.mixed_full p n m (Array2.replace_mixed_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy10 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((IntArray2.undef_full p n m))
    |--
    (
    TT &&
    emp **
    ((IntArray2.undef_missing_i p i 0 n m)) **
    ((IntArray.undef_full (p + ((i * m) * sizeof(INT))) m))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int ((p + ((i * m) * sizeof(INT))) + (j * sizeof(INT))))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int ((p + ((i * m) * sizeof(INT))) + (j * sizeof(INT)))))
    ).

Definition array2_ext_strategy11 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((IntArray2.undef_full p n m))
    |--
    (
    TT &&
    emp **
    ((IntArray2.undef_missing_i p i 0 n m)) **
    ((IntArray.undef_full (p + ((i * m) * sizeof(INT))) m))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int (p + (((i * m) + j) * sizeof(INT))))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int (p + (((i * m) + j) * sizeof(INT)))))
    ).

Definition array2_ext_strategy12 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((IntArray2.undef_full p n m))
    |--
    (
    TT &&
    emp **
    ((IntArray2.undef_missing_i p i 0 n m)) **
    ((IntArray.undef_full (p + (i * (w * sizeof(INT)))) m))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int ((p + (i * (w * sizeof(INT)))) + (j * sizeof(INT))))) -*
    TT &&
    emp **
    ((poly_undef_store FET_int ((p + (i * (w * sizeof(INT)))) + (j * sizeof(INT)))))
    ).

Definition array2_ext_strategy28 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.undef_full p n m))
    |--
    (
    TT &&
    emp **
    ((CharArray2.undef_missing_i p i 0 n m)) **
    ((CharArray.undef_full (p + ((i * m) * sizeof(CHAR))) m))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_char ((p + ((i * m) * sizeof(CHAR))) + (j * sizeof(CHAR))))) -*
    TT &&
    emp **
    ((poly_undef_store FET_char ((p + ((i * m) * sizeof(CHAR))) + (j * sizeof(CHAR)))))
    ).

Definition array2_ext_strategy29 :=
  forall (j : Z) (m : Z) (i : Z) (n : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    emp **
    ((CharArray2.undef_full p n m))
    |--
    (
    TT &&
    emp **
    ((CharArray2.undef_missing_i p i 0 n m)) **
    ((CharArray.undef_full (p + ((i * m) * sizeof(CHAR))) m))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_char (p + (((i * m) + j) * sizeof(CHAR))))) -*
    TT &&
    emp **
    ((poly_undef_store FET_char (p + (((i * m) + j) * sizeof(CHAR)))))
    ).

Definition array2_ext_strategy30 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (j : Z) (p : Z),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (0 <= j) ”) &&
    (“ (j < m) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.undef_full p n m))
    |--
    (
    TT &&
    emp **
    ((CharArray2.undef_missing_i p i 0 n m)) **
    ((CharArray.undef_full (p + (i * (w * sizeof(CHAR)))) m))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_char ((p + (i * (w * sizeof(CHAR)))) + (j * sizeof(CHAR))))) -*
    TT &&
    emp **
    ((poly_undef_store FET_char ((p + (i * (w * sizeof(CHAR)))) + (j * sizeof(CHAR)))))
    ).

Definition array2_ext_strategy16 :=
  forall (i : Z) (n : Z) (rows : (@list (@list Z))) (m : Z) (p : Z) (row : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.full (p + ((i * m) * sizeof(CHAR))) m row))
    |--
    (
    TT &&
    emp **
    ((CharArray2.full p n m (Array2.replace_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy17 :=
  forall (w : Z) (m : Z) (n : Z) (i : Z) (rows : (@list (@list Z))) (p : Z) (row : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    (“ (w = m) ”) &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.full (p + (i * (w * sizeof(CHAR)))) m row))
    |--
    (
    TT &&
    emp **
    ((CharArray2.full p n m (Array2.replace_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition array2_ext_strategy18 :=
  forall (i : Z) (n : Z) (rows : (@list (@list Z))) (m : Z) (p : Z) (row : (@list Z)),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((CharArray2.missing_i p i 0 n m rows)) **
    ((CharArray.full (p + ((i * m) * sizeof(CHAR))) m row))
    |--
    (
    TT &&
    emp **
    ((CharArray2.full p n m (Array2.replace_row i row rows)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type array2_ext_Strategy_Correct.

  Axiom array2_ext_strategy1_correctness : array2_ext_strategy1.
  Axiom array2_ext_strategy2_correctness : array2_ext_strategy2.
  Axiom array2_ext_strategy3_correctness : array2_ext_strategy3.
  Axiom array2_ext_strategy4_correctness : array2_ext_strategy4.
  Axiom array2_ext_strategy5_correctness : array2_ext_strategy5.
  Axiom array2_ext_strategy6_correctness : array2_ext_strategy6.
  Axiom array2_ext_strategy13_correctness : array2_ext_strategy13.
  Axiom array2_ext_strategy14_correctness : array2_ext_strategy14.
  Axiom array2_ext_strategy15_correctness : array2_ext_strategy15.
  Axiom array2_ext_strategy19_correctness : array2_ext_strategy19.
  Axiom array2_ext_strategy20_correctness : array2_ext_strategy20.
  Axiom array2_ext_strategy21_correctness : array2_ext_strategy21.
  Axiom array2_ext_strategy22_correctness : array2_ext_strategy22.
  Axiom array2_ext_strategy23_correctness : array2_ext_strategy23.
  Axiom array2_ext_strategy24_correctness : array2_ext_strategy24.
  Axiom array2_ext_strategy31_correctness : array2_ext_strategy31.
  Axiom array2_ext_strategy32_correctness : array2_ext_strategy32.
  Axiom array2_ext_strategy33_correctness : array2_ext_strategy33.
  Axiom array2_ext_strategy7_correctness : array2_ext_strategy7.
  Axiom array2_ext_strategy8_correctness : array2_ext_strategy8.
  Axiom array2_ext_strategy9_correctness : array2_ext_strategy9.
  Axiom array2_ext_strategy25_correctness : array2_ext_strategy25.
  Axiom array2_ext_strategy26_correctness : array2_ext_strategy26.
  Axiom array2_ext_strategy27_correctness : array2_ext_strategy27.
  Axiom array2_ext_strategy10_correctness : array2_ext_strategy10.
  Axiom array2_ext_strategy11_correctness : array2_ext_strategy11.
  Axiom array2_ext_strategy12_correctness : array2_ext_strategy12.
  Axiom array2_ext_strategy28_correctness : array2_ext_strategy28.
  Axiom array2_ext_strategy29_correctness : array2_ext_strategy29.
  Axiom array2_ext_strategy30_correctness : array2_ext_strategy30.
  Axiom array2_ext_strategy16_correctness : array2_ext_strategy16.
  Axiom array2_ext_strategy17_correctness : array2_ext_strategy17.
  Axiom array2_ext_strategy18_correctness : array2_ext_strategy18.

End array2_ext_Strategy_Correct.
