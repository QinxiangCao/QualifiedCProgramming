From SimpleC.Verification Require Import StrategyPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.vec_qcp_lib.
Local Open Scope sac.

Definition vec_qcp_strategy70 :=
  forall (v : Z) (l : (@list Z)),
    TT &&
    emp **
    ((Veci.rep v l))
    |--
    (
    TT &&
    emp **
    ((Veci.rep v l))
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (0 <= (@Zlength Z l)) ” && “ ((@Zlength Z l) <= (INT_MAX)) ”) &&
    emp
    ).

Definition vec_qcp_strategy71 :=
  forall (v : Z) (l : (@list Z)),
    TT &&
    emp **
    ((Vecp.rep v l))
    |--
    (
    TT &&
    emp **
    ((Vecp.rep v l))
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (0 <= (@Zlength Z l)) ” && “ ((@Zlength Z l) <= (INT_MAX)) ”) &&
    emp
    ).

Definition vec_qcp_strategy208 :=
  forall (v : Z) (l : (@list Z)) (p : Z),
    TT &&
    emp **
    ((Veci.rep_ptr v p l))
    |--
    (
    TT &&
    emp **
    ((Veci.rep_ptr v p l))
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (0 <= (@Zlength Z l)) ” && “ ((@Zlength Z l) <= (INT_MAX)) ”) &&
    emp
    ).

Definition vec_qcp_strategy308 :=
  forall (v : Z) (l : (@list Z)) (p : Z),
    TT &&
    emp **
    ((Vecp.rep_ptr v p l))
    |--
    (
    TT &&
    emp **
    ((Vecp.rep_ptr v p l))
    ) ** (
    TT &&
    emp -*
    TT &&
    (“ (0 <= (@Zlength Z l)) ” && “ ((@Zlength Z l) <= (INT_MAX)) ”) &&
    emp
    ).

Definition vec_qcp_strategy35 :=
  forall (cap : Z) (raw_v : Z) (closed_v : Z) (required_cut : Z) (actual_cut : Z) (words : (@list Z)) (p : Z),
    TT &&
    (“ (raw_v = closed_v) ”) &&
    (“ (actual_cut = required_cut) ”) &&
    (“ (0 <= (@Zlength Z (@sublist Z 0 actual_cut words))) ”) &&
    (“ ((@Zlength Z (@sublist Z 0 actual_cut words)) <= cap) ”) &&
    (“ (cap <= (INT_MAX)) ”) &&
    emp **
    ((poly_store FET_int &( ((raw_v)) # "vecp_t" ->ₛ "size") (@Zlength Z (@sublist Z 0 actual_cut words)))) **
    ((poly_store FET_int &( ((raw_v)) # "vecp_t" ->ₛ "cap") cap)) **
    ((poly_store FET_ptr &( ((raw_v)) # "vecp_t" ->ₛ "ptr") p)) **
    ((PtrArray.seg p 0 (@Zlength Z (@sublist Z 0 actual_cut words)) (@sublist Z 0 actual_cut words))) **
    ((PtrArray.undef_seg p (@Zlength Z (@sublist Z 0 actual_cut words)) cap))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    (“ (vec_buf_ok cap p) ”) &&
    emp -*
    TT &&
    emp **
    ((Vecp.rep closed_v (@sublist Z 0 required_cut words)))
    ).

Definition vec_qcp_strategy207 :=
  forall (v : Z) (l : (@list Z)),
    TT &&
    emp **
    ((Veci.rep v l))
    |--
    EX (p : Z),
      (
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ) ** (
      ALL (target_l : (@list Z)) (target_p : Z),
        TT &&
        emp **
        ((Veci.rep_ptr v target_p target_l)) -*
        TT &&
        emp **
        ((Veci.rep_ptr v target_p target_l))
        ).

Definition vec_qcp_strategy307 :=
  forall (v : Z) (l : (@list Z)),
    TT &&
    emp **
    ((Vecp.rep v l))
    |--
    EX (p : Z),
      (
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ) ** (
      ALL (target_l : (@list Z)) (target_p : Z),
        TT &&
        emp **
        ((Vecp.rep_ptr v target_p target_l)) -*
        TT &&
        emp **
        ((Vecp.rep_ptr v target_p target_l))
        ).

Definition vec_qcp_strategy209 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") n)) **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
    ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") q)) **
    ((IntArray.seg q 0 n k)) **
    ((IntArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy210 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") n)) **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
    ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") q)) **
    ((IntArray.full q n k)) **
    ((IntArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy309 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") n)) **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
    ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") q)) **
    ((PtrArray.seg q 0 n k)) **
    ((PtrArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy310 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") n)) **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
    ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") q)) **
    ((PtrArray.full q n k)) **
    ((PtrArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy212 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((Veci.header v q n cap)) **
    ((IntArray.seg q 0 n k)) **
    ((IntArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy213 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((Veci.header v q n cap)) **
    ((IntArray.full q n k)) **
    ((IntArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy312 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((Vecp.header v q n cap)) **
    ((PtrArray.seg q 0 n k)) **
    ((PtrArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy313 :=
  forall (k : (@list Z)) (v : Z) (q : Z) (cap : Z) (n : Z),
    TT &&
    emp **
    ((Vecp.header v q n cap)) **
    ((PtrArray.full q n k)) **
    ((PtrArray.undef_seg q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= n) ”) &&
      (“ (n <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy401 :=
  forall (i : Z) (n : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls))
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (l = (@Znth (@list Z) i ls (@nil Z))) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep (Vecp.slot b i) l))
      ).

Definition vec_qcp_strategy402 :=
  forall (i : Z) (n : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep (Vecp.slot b i) (@Znth (@list Z) i ls (@nil Z))))
    ) ** (
    ALL (p : Z) (l : (@list Z)) (y : Z),
      TT &&
      emp **
      ((Vecp.rep_ptr (Vecp.slot b i) p l) || (poly_store FET_int &( (((Vecp.slot b i))) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( (((Vecp.slot b i))) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( (((Vecp.slot b i))) # "vecp_t" ->ₛ "ptr") y)) -*
      TT &&
      emp **
      ((Vecp.rep_ptr (Vecp.slot b i) p l) || (poly_store FET_int &( (((Vecp.slot b i))) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( (((Vecp.slot b i))) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( (((Vecp.slot b i))) # "vecp_t" ->ₛ "ptr") y))
      ).

Definition vec_qcp_strategy403 :=
  forall (i : Z) (n : Z) (b : Z) (w : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    emp **
    ((VecpArray.missing_i b i 0 n ls))
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (l = (@Znth (@list Z) i ls (@nil Z))) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep w l))
      ).

Definition vec_qcp_strategy404 :=
  forall (i : Z) (n : Z) (b : Z) (w : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep w (@Znth (@list Z) i ls (@nil Z))))
    ) ** (
    ALL (p : Z) (l : (@list Z)) (y : Z),
      TT &&
      emp **
      ((Vecp.rep_ptr w p l) || (poly_store FET_int &( ((w)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((w)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((w)) # "vecp_t" ->ₛ "ptr") y)) -*
      TT &&
      emp **
      ((Vecp.rep_ptr w p l) || (poly_store FET_int &( ((w)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((w)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((w)) # "vecp_t" ->ₛ "ptr") y))
      ).

Definition vec_qcp_strategy405 :=
  forall (i : Z) (n : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls))
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (l = (@Znth (@list Z) i ls (@nil Z))) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep (b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))) l))
      ).

Definition vec_qcp_strategy406 :=
  forall (i : Z) (n : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep (b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))) (@Znth (@list Z) i ls (@nil Z))))
    ) ** (
    ALL (p : Z) (l : (@list Z)) (y : Z),
      TT &&
      emp **
      ((Vecp.rep_ptr (b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))) p l) || (poly_store FET_int &( (((b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))))) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( (((b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))))) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( (((b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))))) # "vecp_t" ->ₛ "ptr") y)) -*
      TT &&
      emp **
      ((Vecp.rep_ptr (b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))) p l) || (poly_store FET_int &( (((b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))))) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( (((b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))))) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( (((b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))))) # "vecp_t" ->ₛ "ptr") y))
      ).

Definition vec_qcp_strategy407 :=
  forall (i : Z) (n : Z) (m : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (m = n) ”) &&
    (“ (0 <= i) ”) &&
    (“ (i < n) ”) &&
    emp **
    ((VecpArray.full b n ls))
    |--
    (
    TT &&
    emp **
    ((Vecp.rep (Vecp.slot b i) (@Znth (@list Z) i ls (@nil Z))))
    ) ** (
    ALL (ms : (@list (@list Z))),
      TT &&
      (“ (ms = ls) ”) &&
      emp -*
      TT &&
      emp **
      ((VecpArray.missing_i b i 0 m ms))
      ).

Definition vec_qcp_strategy408 :=
  forall (m : Z) (n : Z) (b : Z) (l1 : (@list (@list Z))),
    TT &&
    (“ (m = n) ”) &&
    emp **
    ((VecpArray.full b n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list (@list Z))),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((VecpArray.full b m l2))
      ).

Definition vec_qcp_strategy409 :=
  forall (hi2 : Z) (hi : Z) (j : Z) (i : Z) (lo : Z) (lo2 : Z) (b : Z) (l1 : (@list (@list Z))),
    TT &&
    (“ (j = i) ”) &&
    (“ (lo2 = lo) ”) &&
    (“ (hi2 = hi) ”) &&
    emp **
    ((VecpArray.missing_i b i lo hi l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list (@list Z))),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((VecpArray.missing_i b j lo2 hi2 l2))
      ).

Definition vec_qcp_strategy60 :=
  forall (p : Z) (q : Z) (hi : Z) (l : (@list Z)) (lo : Z),
    TT &&
    (“ (p = q) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((IntArray.seg q lo hi l))
    ).

Definition vec_qcp_strategy68 :=
  forall (hi : Z) (hi2 : Z) (p : Z) (q : Z) (lo2 : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (p = q) ”) &&
    (“ (lo = lo2) ”) &&
    (“ (hi = hi2) ”) &&
    emp **
    ((PtrArray.seg p lo hi l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.seg q lo2 hi2 l))
    ).

Definition vec_qcp_strategy411 :=
  forall (n : Z) (i : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep (Vecp.slot b i) (@Znth (@list Z) i ls (@nil Z))))
    |--
    (
    TT &&
    emp **
    ((VecpArray.full b n ls))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition vec_qcp_strategy413 :=
  forall (i : Z) (b : Z) (w : Z) (n : Z) (ls : (@list (@list Z))),
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep w (@Znth (@list Z) i ls (@nil Z))))
    |--
    (
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    emp **
    ((VecpArray.full b n ls))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition vec_qcp_strategy415 :=
  forall (n : Z) (i : Z) (b : Z) (ls : (@list (@list Z))),
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep (b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))) (@Znth (@list Z) i ls (@nil Z))))
    |--
    (
    TT &&
    emp **
    ((VecpArray.full b n ls))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition vec_qcp_strategy2 :=
  forall (l : (@list Z)) (v : Z),
    TT &&
    emp **
    ((Veci.rep v l))
    |--
    EX (p : Z) (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
        ).

Definition vec_qcp_strategy5 :=
  forall (y : Z) (v : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
    ) ** (
    ALL (p : Z) (cap : Z) (l : (@list Z)),
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Veci.rep v l))
      ).

Definition vec_qcp_strategy7 :=
  forall (v : Z),
    TT &&
    emp **
    ((Veci.shell v))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "size"))) **
    ((poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "cap"))) **
    ((poly_undef_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr")))
    ) ** (
    ALL (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr"))) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr")))
      ).

Definition vec_qcp_strategy8 :=
  forall (y : Z) (v : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr")))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr")))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "size"))) **
    ((poly_undef_store FET_int &( ((v)) # "veci_t" ->ₛ "cap"))) **
    ((poly_undef_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr"))) -*
    TT &&
    emp **
    ((Veci.shell v))
    ).

Definition vec_qcp_strategy102 :=
  forall (l : (@list Z)) (v : Z),
    TT &&
    emp **
    ((Vecp.rep v l))
    |--
    EX (p : Z) (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
        ).

Definition vec_qcp_strategy105 :=
  forall (y : Z) (v : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
    ) ** (
    ALL (p : Z) (cap : Z) (l : (@list Z)),
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Vecp.rep v l))
      ).

Definition vec_qcp_strategy116 :=
  forall (i : Z) (j : Z) (w : Z) (base : Z) (k : (@list Z)),
    TT &&
    (“ (w = (Vecp.slot base i)) ” || “ ((Vecp.slot base i) = w) ”) &&
    (“ (i = j) ”) &&
    emp **
    ((Vecp.rep w k))
    |--
    (
    TT &&
    (“ (w = (Vecp.slot base i)) ” || “ ((Vecp.slot base i) = w) ”) &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (k = l) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep (Vecp.slot base j) l))
      ).

Definition vec_qcp_strategy95 :=
  forall (read_index : Z) (base : Z) (requested : Z) (index : Z) (n : Z) (cap : Z) (q : Z),
    TT &&
    (“ (read_index = index) ” || “ (index = read_index) ”) &&
    (“ (requested = (Vecp.slot base read_index)) ” || “ ((Vecp.slot base read_index) = requested) ”) &&
    emp **
    ((Vecp.header requested q n cap))
    |--
    (
    TT &&
    (“ (read_index = index) ” || “ (index = read_index) ”) &&
    (“ (requested = (Vecp.slot base read_index)) ” || “ ((Vecp.slot base read_index) = requested) ”) &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp **
      ((PtrArray.seg q 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg q (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Vecp.rep (Vecp.slot base index) l))
      ).

Definition vec_qcp_strategy107 :=
  forall (v : Z),
    TT &&
    emp **
    ((Vecp.shell v))
    |--
    (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "size"))) **
    ((poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap"))) **
    ((poly_undef_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr")))
    ) ** (
    ALL (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr"))) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr")))
      ).

Definition vec_qcp_strategy108 :=
  forall (y : Z) (v : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr")))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "size")) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap")) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y) || (poly_undef_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr")))
    ) ** (
    TT &&
    emp **
    ((poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "size"))) **
    ((poly_undef_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap"))) **
    ((poly_undef_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr"))) -*
    TT &&
    emp **
    ((Vecp.shell v))
    ).

Definition vec_qcp_strategy9 :=
  forall (v : Z),
    TT &&
    emp **
    ((UndefStructPredveci_t v))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((Veci.shell v))
    ).

Definition vec_qcp_strategy10 :=
  forall (v : Z),
    TT &&
    emp **
    ((Veci.shell v))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UndefStructPredveci_t v))
    ).

Definition vec_qcp_strategy109 :=
  forall (v : Z),
    TT &&
    emp **
    ((UndefStructPredvecp_t v))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((Vecp.shell v))
    ).

Definition vec_qcp_strategy110 :=
  forall (v : Z),
    TT &&
    emp **
    ((Vecp.shell v))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((UndefStructPredvecp_t v))
    ).

Definition vec_qcp_strategy201 :=
  forall (p : Z) (l : (@list Z)) (v : Z),
    TT &&
    emp **
    ((Veci.rep_ptr v p l))
    |--
    EX (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
        ).

Definition vec_qcp_strategy202 :=
  forall (q : Z) (p : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    emp **
    ((Veci.rep_ptr v p l))
    |--
    EX (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((Veci.header v p (@Zlength Z l) cap)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (y : Z) (ll : (@list Z)) (i : Z) (hi : Z) (lo : Z),
        TT &&
        emp **
        ((poly_store FET_int (q + (i * sizeof(INT))) y) || (poly_undef_store FET_int (q + (i * sizeof(INT)))) || (poly_store FET_int (q + (i * sizeof(INT))) y) || (poly_undef_store FET_int (q + (i * sizeof(INT)))) || (IntArray.seg q lo hi ll) || (IntArray.undef_seg q lo hi) || (poly_store FET_int q y) || (poly_undef_store FET_int q)) -*
        TT &&
        emp **
        ((poly_store FET_int (q + (i * sizeof(INT))) y) || (poly_undef_store FET_int (q + (i * sizeof(INT)))) || (poly_store FET_int (q + (i * sizeof(INT))) y) || (poly_undef_store FET_int (q + (i * sizeof(INT)))) || (IntArray.seg q lo hi ll) || (IntArray.undef_seg q lo hi) || (poly_store FET_int q y) || (poly_undef_store FET_int q))
        ).

Definition vec_qcp_strategy203 :=
  forall (y : Z) (v : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
    ) ** (
    ALL (p : Z) (cap : Z) (l : (@list Z)),
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy205 :=
  forall (w : Z) (v : Z) (k : (@list Z)) (q : Z),
    TT &&
    (“ (w = v) ”) &&
    emp **
    ((Veci.rep_ptr w q k))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      emp -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy206 :=
  forall (w : Z) (v : Z) (k : (@list Z)) (q : Z),
    TT &&
    (“ (w = v) ”) &&
    emp **
    ((Veci.rep_ptr w q k))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (k = l) ”) &&
      emp -*
      TT &&
      emp **
      ((Veci.rep v l))
      ).

Definition vec_qcp_strategy301 :=
  forall (p : Z) (l : (@list Z)) (v : Z),
    TT &&
    emp **
    ((Vecp.rep_ptr v p l))
    |--
    EX (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
        ).

Definition vec_qcp_strategy302 :=
  forall (q : Z) (p : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    emp **
    ((Vecp.rep_ptr v p l))
    |--
    EX (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((Vecp.header v p (@Zlength Z l) cap)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (y : Z) (ll : (@list Z)) (i : Z) (hi : Z) (lo : Z),
        TT &&
        emp **
        ((poly_store FET_ptr (q + (i * sizeof(PTR))) y) || (poly_undef_store FET_ptr (q + (i * sizeof(PTR)))) || (poly_store FET_ptr (q + (i * sizeof(PTR))) y) || (poly_undef_store FET_ptr (q + (i * sizeof(PTR)))) || (PtrArray.seg q lo hi ll) || (PtrArray.undef_seg q lo hi) || (poly_store FET_ptr q y) || (poly_undef_store FET_ptr q)) -*
        TT &&
        emp **
        ((poly_store FET_ptr (q + (i * sizeof(PTR))) y) || (poly_undef_store FET_ptr (q + (i * sizeof(PTR)))) || (poly_store FET_ptr (q + (i * sizeof(PTR))) y) || (poly_undef_store FET_ptr (q + (i * sizeof(PTR)))) || (PtrArray.seg q lo hi ll) || (PtrArray.undef_seg q lo hi) || (poly_store FET_ptr q y) || (poly_undef_store FET_ptr q))
        ).

Definition vec_qcp_strategy303 :=
  forall (y : Z) (v : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
    ) ** (
    ALL (p : Z) (cap : Z) (l : (@list Z)),
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy305 :=
  forall (w : Z) (v : Z) (k : (@list Z)) (q : Z),
    TT &&
    (“ (w = v) ”) &&
    emp **
    ((Vecp.rep_ptr w q k))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)) (p : Z),
      TT &&
      (“ (q = p) ”) &&
      (“ (k = l) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy306 :=
  forall (w : Z) (v : Z) (k : (@list Z)) (q : Z),
    TT &&
    (“ (w = v) ”) &&
    emp **
    ((Vecp.rep_ptr w q k))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (k = l) ”) &&
      emp -*
      TT &&
      emp **
      ((Vecp.rep v l))
      ).

Definition vec_qcp_strategy211 :=
  forall (n : Z) (l : (@list Z)) (p : Z) (q : Z) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    (“ (n = (@Zlength Z l)) ”) &&
    emp **
    ((Veci.rep_ptr v p l))
    |--
    EX (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((Veci.header v p (@Zlength Z l) cap)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp **
      ((IntArray.full q n l))
      ).

Definition vec_qcp_strategy214 :=
  forall (v : Z) (n : Z) (cap : Z) (q : Z),
    TT &&
    emp **
    ((Veci.header v q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (p : Z) (l : (@list Z)),
      TT &&
      (“ (q = p) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Veci.rep_ptr v p l))
      ).

Definition vec_qcp_strategy215 :=
  forall (v : Z) (n : Z) (cap : Z) (q : Z),
    TT &&
    emp **
    ((Veci.header v q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp **
      ((IntArray.seg q 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg q (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Veci.rep v l))
      ).

Definition vec_qcp_strategy311 :=
  forall (n : Z) (l : (@list Z)) (p : Z) (q : Z) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    (“ (n = (@Zlength Z l)) ”) &&
    emp **
    ((Vecp.rep_ptr v p l))
    |--
    EX (cap : Z),
      (
      TT &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((Vecp.header v p (@Zlength Z l) cap)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp **
      ((PtrArray.full q n l))
      ).

Definition vec_qcp_strategy314 :=
  forall (v : Z) (n : Z) (cap : Z) (q : Z),
    TT &&
    emp **
    ((Vecp.header v q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (p : Z) (l : (@list Z)),
      TT &&
      (“ (q = p) ”) &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap p) ”) &&
      emp **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Vecp.rep_ptr v p l))
      ).

Definition vec_qcp_strategy315 :=
  forall (v : Z) (n : Z) (cap : Z) (q : Z),
    TT &&
    emp **
    ((Vecp.header v q n cap))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l : (@list Z)),
      TT &&
      (“ (n = (@Zlength Z l)) ”) &&
      (“ (0 <= (@Zlength Z l)) ”) &&
      (“ ((@Zlength Z l) <= cap) ”) &&
      (“ (cap <= (INT_MAX)) ”) &&
      (“ (vec_buf_ok cap q) ”) &&
      emp **
      ((PtrArray.seg q 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg q (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((Vecp.rep v l))
      ).

Definition vec_qcp_strategy412 :=
  forall (n : Z) (ls : (@list (@list Z))) (i : Z) (b : Z) (l : (@list Z)),
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep (Vecp.slot b i) l))
    |--
    (
    TT &&
    emp **
    ((VecpArray.full b n (@replace_Znth (@list Z) i l ls)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition vec_qcp_strategy414 :=
  forall (i : Z) (b : Z) (w : Z) (n : Z) (ls : (@list (@list Z))) (l : (@list Z)),
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep w l))
    |--
    (
    TT &&
    (“ (w = (Vecp.slot b i)) ” || “ ((Vecp.slot b i) = w) ”) &&
    emp **
    ((VecpArray.full b n (@replace_Znth (@list Z) i l ls)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition vec_qcp_strategy416 :=
  forall (n : Z) (ls : (@list (@list Z))) (i : Z) (b : Z) (l : (@list Z)),
    TT &&
    emp **
    ((VecpArray.missing_i b i 0 n ls)) **
    ((Vecp.rep (b + (i * (sizeof_front_end_type (FET_alias ("vecp_t"))))) l))
    |--
    (
    TT &&
    emp **
    ((VecpArray.full b n (@replace_Znth (@list Z) i l ls)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type vec_qcp_Strategy_Correct.

  Axiom vec_qcp_strategy70_correctness : vec_qcp_strategy70.
  Axiom vec_qcp_strategy71_correctness : vec_qcp_strategy71.
  Axiom vec_qcp_strategy208_correctness : vec_qcp_strategy208.
  Axiom vec_qcp_strategy308_correctness : vec_qcp_strategy308.
  Axiom vec_qcp_strategy35_correctness : vec_qcp_strategy35.
  Axiom vec_qcp_strategy207_correctness : vec_qcp_strategy207.
  Axiom vec_qcp_strategy307_correctness : vec_qcp_strategy307.
  Axiom vec_qcp_strategy209_correctness : vec_qcp_strategy209.
  Axiom vec_qcp_strategy210_correctness : vec_qcp_strategy210.
  Axiom vec_qcp_strategy309_correctness : vec_qcp_strategy309.
  Axiom vec_qcp_strategy310_correctness : vec_qcp_strategy310.
  Axiom vec_qcp_strategy212_correctness : vec_qcp_strategy212.
  Axiom vec_qcp_strategy213_correctness : vec_qcp_strategy213.
  Axiom vec_qcp_strategy312_correctness : vec_qcp_strategy312.
  Axiom vec_qcp_strategy313_correctness : vec_qcp_strategy313.
  Axiom vec_qcp_strategy401_correctness : vec_qcp_strategy401.
  Axiom vec_qcp_strategy402_correctness : vec_qcp_strategy402.
  Axiom vec_qcp_strategy403_correctness : vec_qcp_strategy403.
  Axiom vec_qcp_strategy404_correctness : vec_qcp_strategy404.
  Axiom vec_qcp_strategy405_correctness : vec_qcp_strategy405.
  Axiom vec_qcp_strategy406_correctness : vec_qcp_strategy406.
  Axiom vec_qcp_strategy407_correctness : vec_qcp_strategy407.
  Axiom vec_qcp_strategy408_correctness : vec_qcp_strategy408.
  Axiom vec_qcp_strategy409_correctness : vec_qcp_strategy409.
  Axiom vec_qcp_strategy60_correctness : vec_qcp_strategy60.
  Axiom vec_qcp_strategy68_correctness : vec_qcp_strategy68.
  Axiom vec_qcp_strategy411_correctness : vec_qcp_strategy411.
  Axiom vec_qcp_strategy413_correctness : vec_qcp_strategy413.
  Axiom vec_qcp_strategy415_correctness : vec_qcp_strategy415.
  Axiom vec_qcp_strategy2_correctness : vec_qcp_strategy2.
  Axiom vec_qcp_strategy5_correctness : vec_qcp_strategy5.
  Axiom vec_qcp_strategy7_correctness : vec_qcp_strategy7.
  Axiom vec_qcp_strategy8_correctness : vec_qcp_strategy8.
  Axiom vec_qcp_strategy102_correctness : vec_qcp_strategy102.
  Axiom vec_qcp_strategy105_correctness : vec_qcp_strategy105.
  Axiom vec_qcp_strategy116_correctness : vec_qcp_strategy116.
  Axiom vec_qcp_strategy95_correctness : vec_qcp_strategy95.
  Axiom vec_qcp_strategy107_correctness : vec_qcp_strategy107.
  Axiom vec_qcp_strategy108_correctness : vec_qcp_strategy108.
  Axiom vec_qcp_strategy9_correctness : vec_qcp_strategy9.
  Axiom vec_qcp_strategy10_correctness : vec_qcp_strategy10.
  Axiom vec_qcp_strategy109_correctness : vec_qcp_strategy109.
  Axiom vec_qcp_strategy110_correctness : vec_qcp_strategy110.
  Axiom vec_qcp_strategy201_correctness : vec_qcp_strategy201.
  Axiom vec_qcp_strategy202_correctness : vec_qcp_strategy202.
  Axiom vec_qcp_strategy203_correctness : vec_qcp_strategy203.
  Axiom vec_qcp_strategy205_correctness : vec_qcp_strategy205.
  Axiom vec_qcp_strategy206_correctness : vec_qcp_strategy206.
  Axiom vec_qcp_strategy301_correctness : vec_qcp_strategy301.
  Axiom vec_qcp_strategy302_correctness : vec_qcp_strategy302.
  Axiom vec_qcp_strategy303_correctness : vec_qcp_strategy303.
  Axiom vec_qcp_strategy305_correctness : vec_qcp_strategy305.
  Axiom vec_qcp_strategy306_correctness : vec_qcp_strategy306.
  Axiom vec_qcp_strategy211_correctness : vec_qcp_strategy211.
  Axiom vec_qcp_strategy214_correctness : vec_qcp_strategy214.
  Axiom vec_qcp_strategy215_correctness : vec_qcp_strategy215.
  Axiom vec_qcp_strategy311_correctness : vec_qcp_strategy311.
  Axiom vec_qcp_strategy314_correctness : vec_qcp_strategy314.
  Axiom vec_qcp_strategy315_correctness : vec_qcp_strategy315.
  Axiom vec_qcp_strategy412_correctness : vec_qcp_strategy412.
  Axiom vec_qcp_strategy414_correctness : vec_qcp_strategy414.
  Axiom vec_qcp_strategy416_correctness : vec_qcp_strategy416.

End vec_qcp_Strategy_Correct.
