Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition solver_qcp_strategy12 :=
  forall (i : Z) (hi : Z) (lo : Z) (p : Z) (l : (@list fp64)),
    TT &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((DoubleArray.seg p lo hi l))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.missing_i p i lo hi l))
    ) ** (
    ALL (v : fp64),
      TT &&
      (“ (v = ( double_Znth (Z.sub i lo) l)) ”) &&
      emp -*
      TT &&
      emp **
      ((store_double (Z.add p (Z.mul i (@sizeof_front_end_type FET_double))) v))
      ).

Definition solver_qcp_strategy35 :=
  forall (cap : Z) (words : (@list Z)) (actual_cut : Z) (required_cut : Z) (closed_v : Z) (raw_v : Z) (p : Z),
    TT &&
    (“ (raw_v = closed_v) ”) &&
    (“ (actual_cut = required_cut) ”) &&
    (“ (Z.le 0 (@Zlength Z (@sublist Z 0 actual_cut words))) ”) &&
    (“ (Z.le (@Zlength Z (@sublist Z 0 actual_cut words)) cap) ”) &&
    (“ (Z.lt 0 cap) ”) &&
    (“ (Z.le cap ( INT_MAX)) ”) &&
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
    emp -*
    TT &&
    emp **
    ((vecp_rep closed_v (@sublist Z 0 required_cut words) cap))
    ).

Definition solver_qcp_strategy36 :=
  forall (hi : Z) (lo : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (Z.le lo 0) ”) &&
    (“ (Z.lt 0 hi) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    emp **
    ((IntArray.missing_i p 0 lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (Z.sub 0 lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int p v))
      ).

Definition solver_qcp_strategy69 :=
  forall (hi : Z) (q : Z) (p : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    (“ (Z.le lo 0) ”) &&
    (“ (Z.lt 0 hi) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp **
    ((IntArray.missing_i p 0 lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (Z.sub 0 lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int q v))
      ).

Definition solver_qcp_strategy37 :=
  forall (i : Z) (hi : Z) (q : Z) (p : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((IntArray.seg p lo hi l))
    |--
    (
    TT &&
    emp **
    ((IntArray.missing_i p i lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (Z.sub i lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int (Z.add q (Z.mul i (@sizeof_front_end_type FET_int))) v))
      ).

Definition solver_qcp_strategy39 :=
  forall (xp : Z) (xr : Z) (yp : Z) (w : Z) (db : dbmap) (xa : fp32) (xw : (@list Z)) (activities : (@list fp32)),
    TT &&
    (“ (xp = yp) ”) &&
    (“ (xp = xr) ”) &&
    emp **
    ((poly_store FET_int ( clause_hdr_addr xp) w)) **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    |--
    (
    TT &&
    emp **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = w) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int ( clause_hdr_addr yp) v))
      ).

Definition solver_qcp_strategy40 :=
  forall (xp : Z) (xr : Z) (yp : Z) (a : fp32) (db : dbmap) (xa : fp32) (xw : (@list Z)) (activities : (@list fp32)),
    TT &&
    (“ (xp = yp) ”) &&
    (“ (xp = xr) ”) &&
    emp **
    ((store_float ( clause_act_addr xp) a)) **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    |--
    (
    TT &&
    emp **
    ((learnt_sort_alias_remainder db activities xr xw xa))
    ) ** (
    ALL (b : fp32),
      TT &&
      (“ (b = a) ”) &&
      emp -*
      TT &&
      emp **
      ((store_float ( clause_act_addr yp) b))
      ).

Definition solver_qcp_strategy41 :=
  forall (hi : Z) (q : Z) (cp : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = ( clause_lits_addr cp)) ”) &&
    (“ (Z.le lo 0) ”) &&
    (“ (Z.lt 0 hi) ”) &&
    emp **
    ((IntArray.seg ( clause_lits_addr cp) lo hi l))
    |--
    (
    TT &&
    emp **
    ((IntArray.missing_i ( clause_lits_addr cp) 0 lo hi l))
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = (Znth (Z.sub 0 lo) l  0)) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_int q v))
      ).

Definition solver_qcp_strategy60 :=
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

Definition solver_qcp_strategy68 :=
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

Definition solver_qcp_strategy61 :=
  forall (i : Z) (n : Z) (p : Z) (words : (@list Z)),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PtrArray.missing_i p i 0 n (@replace_Znth Z i (@Znth Z i words 0) (@replace_Znth Z i (@Znth Z i words 0) words))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.missing_i p i 0 n words))
    ).

Definition solver_qcp_strategy13 :=
  forall (i : Z) (hi : Z) (lo : Z) (l : (@list fp64)) (p : Z),
    TT &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((DoubleArray.missing_i p i lo hi l)) **
    ((store_double (Z.add p (Z.mul i (@sizeof_front_end_type FET_double))) ( double_Znth (Z.sub i lo) l)))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy67 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((IntArray.missing_i p i lo hi l)) **
    ((poly_store FET_int (Z.add q (Z.mul j (@sizeof_front_end_type FET_int))) (Znth (Z.sub i lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy42 :=
  forall (i : Z) (hi : Z) (cp : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = ( clause_lits_addr cp)) ”) &&
    (“ (i = 0) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((IntArray.missing_i ( clause_lits_addr cp) i lo hi l)) **
    ((poly_store FET_int q (Znth (Z.sub i lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg ( clause_lits_addr cp) lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy58 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((PtrArray.missing_i p i lo hi l)) **
    ((poly_store FET_ptr (Z.add q (Z.mul j (@sizeof_front_end_type FET_ptr))) (Znth (Z.sub i lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((PtrArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy57 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((CharArray.missing_i p i lo hi l)) **
    ((poly_store FET_char (Z.add q (Z.mul j (@sizeof_front_end_type FET_char))) (Znth (Z.sub i lo) l  0)))
    |--
    (
    TT &&
    emp **
    ((CharArray.seg p lo hi l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy2 :=
  forall (cap : Z) (l : (@list Z)) (v : Z),
    TT &&
    emp **
    ((veci_rep v l cap))
    |--
    EX (p : Z),
      (
      TT &&
      (“ (Z.le 0 (@Zlength Z l)) ”) &&
      (“ (Z.le (@Zlength Z l) cap) ”) &&
      (“ (Z.lt 0 cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (target_p : Z) (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (veci_rep_at v target_p l cap) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") y) || (veci_rep_at v target_p l cap) || (poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") y))
        ).

Definition solver_qcp_strategy3 :=
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
    ALL (cap : Z) (l : (@list Z)) (p : Z),
      TT &&
      (“ (Z.le 0 (@Zlength Z l)) ”) &&
      (“ (Z.le (@Zlength Z l) cap) ”) &&
      (“ (Z.lt 0 cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((veci_rep v l cap))
      ).

Definition solver_qcp_strategy4 :=
  forall (cap : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    emp **
    ((veci_rep_at v p l cap))
    |--
    (
    TT &&
    (“ (Z.le 0 (@Zlength Z l)) ”) &&
    (“ (Z.le (@Zlength Z l) cap) ”) &&
    (“ (Z.lt 0 cap) ”) &&
    (“ (Z.le cap ( INT_MAX)) ”) &&
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

Definition solver_qcp_strategy5 :=
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
    ALL (cap : Z) (l : (@list Z)) (p : Z),
      TT &&
      (“ (Z.le 0 (@Zlength Z l)) ”) &&
      (“ (Z.le (@Zlength Z l) cap) ”) &&
      (“ (Z.lt 0 cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "veci_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "veci_t" ->ₛ "ptr") p)) **
      ((IntArray.seg p 0 (@Zlength Z l) l)) **
      ((IntArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((veci_rep_at v p l cap))
      ).

Definition solver_qcp_strategy6 :=
  forall (cap : Z) (l : (@list Z)) (v : Z),
    TT &&
    emp **
    ((vecp_rep v l cap))
    |--
    EX (p : Z),
      (
      TT &&
      (“ (Z.le 0 (@Zlength Z l)) ”) &&
      (“ (Z.le (@Zlength Z l) cap) ”) &&
      (“ (Z.lt 0 cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap))
      ) ** (
      ALL (target_p : Z) (y : Z),
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (vecp_rep_at v target_p l cap) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y)) -*
        TT &&
        emp **
        ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") y) || (vecp_rep_at v target_p l cap) || (poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") y) || (poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") y))
        ).

Definition solver_qcp_strategy7 :=
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
    ALL (cap : Z) (l : (@list Z)) (p : Z),
      TT &&
      (“ (Z.le 0 (@Zlength Z l)) ”) &&
      (“ (Z.le (@Zlength Z l) cap) ”) &&
      (“ (Z.lt 0 cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((vecp_rep v l cap))
      ).

Definition solver_qcp_strategy8 :=
  forall (cap : Z) (l : (@list Z)) (v : Z) (p : Z),
    TT &&
    emp **
    ((vecp_rep_at v p l cap))
    |--
    (
    TT &&
    (“ (Z.le 0 (@Zlength Z l)) ”) &&
    (“ (Z.le (@Zlength Z l) cap) ”) &&
    (“ (Z.lt 0 cap) ”) &&
    (“ (Z.le cap ( INT_MAX)) ”) &&
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

Definition solver_qcp_strategy9 :=
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
    ALL (cap : Z) (l : (@list Z)) (p : Z),
      TT &&
      (“ (Z.le 0 (@Zlength Z l)) ”) &&
      (“ (Z.le (@Zlength Z l) cap) ”) &&
      (“ (Z.lt 0 cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      emp **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "size") (@Zlength Z l))) **
      ((poly_store FET_int &( ((v)) # "vecp_t" ->ₛ "cap") cap)) **
      ((poly_store FET_ptr &( ((v)) # "vecp_t" ->ₛ "ptr") p)) **
      ((PtrArray.seg p 0 (@Zlength Z l) l)) **
      ((PtrArray.undef_seg p (@Zlength Z l) cap)) -*
      TT &&
      emp **
      ((vecp_rep_at v p l cap))
      ).

Definition solver_qcp_strategy16 :=
  forall (y : Z) (s : Z),
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y))
    ) ** (
    ALL (qtail : Z) (cap : Z) (trail : (@list Z)) (levels : (@list Z)) (assigns : (@list Z)) (n : Z) (reasons : (@list Z)) (trl : Z) (rsn : Z) (lvl : Z) (asg : Z) (lim_cap : Z) (lim : (@list Z)),
      TT &&
      (“ (Z.le 0 n) ”) &&
      (“ (Z.le n cap) ”) &&
      (“ (Z.le cap ( INT_MAX)) ”) &&
      (“ ((@Zlength Z assigns) = n) ”) &&
      (“ ((@Zlength Z levels) = n) ”) &&
      (“ ((@Zlength Z reasons) = n) ”) &&
      (“ ((@Zlength Z trail) = qtail) ”) &&
      (“ (Z.le 0 qtail) ”) &&
      (“ (Z.le qtail cap) ”) &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") qtail)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
      ((CharArray.seg asg 0 n assigns)) **
      ((CharArray.undef_seg asg n cap)) **
      ((IntArray.seg lvl 0 n levels)) **
      ((IntArray.undef_seg lvl n cap)) **
      ((PtrArray.seg rsn 0 n reasons)) **
      ((PtrArray.undef_seg rsn n cap)) **
      ((IntArray.seg trl 0 qtail trail)) **
      ((IntArray.undef_seg trl qtail cap)) **
      ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") lim lim_cap)) -*
      TT &&
      emp **
      ((enqueue_state_at s asg lvl n cap qtail assigns levels reasons trail lim lim_cap))
      ).

Definition solver_qcp_strategy23 :=
  forall (s : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_levels_slice_at s M lvl))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (order : (@list Z)) (order_cap : Z) (orderpos : (@list Z)),
      TT &&
      emp -*
      TT &&
      emp **
      ((solver_levels_slice_at s ( msolver_heap_project M orderpos order order_cap) lvl))
      ).

Definition solver_qcp_strategy29 :=
  forall (i : Z) (j : Z) (n : Z) (words : (@list Z)) (p : Z),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    (“ (i = j) ”) &&
    emp **
    ((removable_reason_array_hole p i n words)) **
    ((poly_store FET_ptr (Z.add p (Z.mul j (@sizeof_front_end_type FET_ptr))) (@Znth Z i words 0)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.seg p 0 n words))
    ).

Definition solver_qcp_strategy33 :=
  forall (s : Z) (n : Z),
    TT &&
    emp **
    ((solver_clause_count_cell s n))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((&( ((s)) # "solver_t" ->ₛ "clauses"))) # "vecp_t" ->ₛ "size") n))
    ) ** (
    ALL (value : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((s)) # "solver_t" ->ₛ "clauses"))) # "vecp_t" ->ₛ "size") value)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((s)) # "solver_t" ->ₛ "clauses"))) # "vecp_t" ->ₛ "size") value))
      ).

Definition solver_qcp_strategy34 :=
  forall (value : Z) (s : Z) (cap : Z) (words : (@list Z)),
    TT &&
    emp **
    ((poly_store FET_int &( ((&( ((s)) # "solver_t" ->ₛ "clauses"))) # "vecp_t" ->ₛ "size") value) || (vecp_rep &( ((s)) # "solver_t" ->ₛ "clauses") words cap))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((&( ((s)) # "solver_t" ->ₛ "clauses"))) # "vecp_t" ->ₛ "size") value) || (vecp_rep &( ((s)) # "solver_t" ->ₛ "clauses") words cap))
    ) ** (
    ALL (n : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((&( ((s)) # "solver_t" ->ₛ "clauses"))) # "vecp_t" ->ₛ "size") n)) -*
      TT &&
      emp **
      ((solver_clause_count_cell s n))
      ).

Definition solver_qcp_strategy43 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") ( ms_root_level M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_root_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy44 :=
  forall (lvl : Z) (wl : Z) (s : Z) (M : msolver),
    TT &&
    emp **
    ((solver_search_root_frame_at s M lvl wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") ( ms_root_level M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    ).

Definition solver_qcp_strategy45 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") ( ms_root_level M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 ( ms_size M) ( mt_levels ( ms_core M)))) **
    ((IntArray.undef_seg lvl ( ms_size M) ( ms_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_root_payload s M wl))
    ).

Definition solver_qcp_strategy46 :=
  forall (wl : Z) (s : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_search_root_payload s M wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") ( ms_root_level M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 ( ms_size M) ( mt_levels ( ms_core M)))) **
    ((IntArray.undef_seg lvl ( ms_size M) ( ms_cap M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    ).

Definition solver_qcp_strategy47 :=
  forall (s : Z) (asg : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_assigns_levels_at s M asg lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") ( ms_root_level M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_root_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy48 :=
  forall (s : Z) (asg : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_assigns_levels_at s M asg lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") ( stats_conflicts ( ms_stats M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "root_level") ( ms_root_level M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_conflict_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy49 :=
  forall (s : Z) (asg : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_assigns_levels_at s M asg lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") ( ms_size M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((CharArray.seg asg 0 ( ms_size M) ( mt_assigns ( ms_core M)))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 ( ms_size M) ( mt_levels ( ms_core M)))) **
    ((store_double &( ((s)) # "solver_t" ->ₛ "progress_estimate") ( ms_progress M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_progress_frame_at s M asg lvl wl))
    ).

Definition solver_qcp_strategy50 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") ( stats_starts ( ms_stats M)))) **
    ((store_double &( ((s)) # "solver_t" ->ₛ "var_decay") ( ms_var_decay M))) **
    ((store_float &( ((s)) # "solver_t" ->ₛ "cla_decay") ( ms_cla_decay M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "model") ( ms_model M) ( ms_model_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_init_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy51 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") ( ms_qtail M))) **
    ((vecp_rep &( ((s)) # "solver_t" ->ₛ "learnts") ( db_words ( ms_learnt M)) ( ms_learnt_cap M)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_search_reducedb_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy52 :=
  forall (lvl : Z) (wl : Z) (s : Z) (M : msolver),
    TT &&
    emp **
    ((solver_search_reducedb_frame_at s M lvl wl)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") ( ms_qtail M))) **
    ((vecp_rep &( ((s)) # "solver_t" ->ₛ "learnts") ( db_words ( ms_learnt M)) ( ms_learnt_cap M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    ).

Definition solver_qcp_strategy53 :=
  forall (s : Z) (rsn : Z) (trl : Z) (wl : Z) (tgs : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_analyze_at s M rsn lvl trl tgs wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") ( stats_max_literals ( ms_stats M)))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") ( stats_tot_literals ( ms_stats M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_literal_stats_frame_at s M rsn lvl trl tgs wl))
    ).

Definition solver_qcp_strategy54 :=
  forall (s : Z) (rsn : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_reasons_levels_wl_at s M rsn lvl wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") ( mt_qhead ( ms_core M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_assigns") ( ms_simpdb_assigns M))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") ( ms_simpdb_props M))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") ( stats_clauses_literals ( ms_stats M)))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") ( stats_learnts_literals ( ms_stats M))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_simplify_finish_frame_at s M lvl wl))
    ).

Definition solver_qcp_strategy55 :=
  forall (s : Z) (wl : Z) (lvl : Z) (M : msolver),
    TT &&
    emp **
    ((solver_rep_levels_wl_at s M wl lvl))
    |--
    EX (values_ptr : Z),
      (
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") ( ms_size M))) **
      ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") values_ptr)) **
      ((CharArray.seg values_ptr 0 ( ms_size M) ( mt_assigns ( ms_core M)))) **
      ((CharArray.undef_seg values_ptr ( ms_size M) ( ms_cap M))) **
      ((veci_rep &( ((s)) # "solver_t" ->ₛ "model") ( ms_model M) ( ms_model_cap M)))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp **
      ((solver_model_copy_frame_at s M lvl wl))
      ).

Definition solver_qcp_strategy56 :=
  forall (M : msolver) (rsn : Z) (trl : Z) (wl : Z) (tgs : Z) (s : Z) (lvl : Z) (n : Z),
    TT &&
    (“ (solver_shape M) ”) &&
    emp **
    ((solver_reason_levels_frame_at s M trl tgs wl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((PtrArray.seg rsn 0 n ( ms_reason_words M))) **
    ((PtrArray.undef_seg rsn n ( ms_cap M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((IntArray.seg lvl 0 n ( mt_levels ( ms_core M)))) **
    ((IntArray.undef_seg lvl n ( ms_cap M)))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((solver_rep_analyze_at s M rsn lvl trl tgs wl))
    ).

Definition solver_qcp_strategy62 :=
  forall (s : Z) (sz : Z) (act : Z) (opos : Z) (lvl : Z) (tgs : Z) (trl : Z) (rsn : Z) (asg : Z) (wl : Z) (M : msolver),
    TT &&
    emp **
    ((setnvars_arrays_at s M sz wl act asg opos rsn lvl trl tgs))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") ( ms_qtail M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") wl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") act)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") opos)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") tgs)) **
    ((DoubleArray.seg act 0 sz ( ms_activity M))) **
    ((DoubleArray.undef_seg act sz ( ms_cap M))) **
    ((CharArray.seg asg 0 sz ( mt_assigns ( ms_core M)))) **
    ((CharArray.undef_seg asg sz ( ms_cap M))) **
    ((IntArray.seg opos 0 sz ( ms_orderpos M))) **
    ((IntArray.undef_seg opos sz ( ms_cap M))) **
    ((PtrArray.seg rsn 0 sz ( ms_reason_words M))) **
    ((PtrArray.undef_seg rsn sz ( ms_cap M))) **
    ((IntArray.seg lvl 0 sz ( mt_levels ( ms_core M)))) **
    ((IntArray.undef_seg lvl sz ( ms_cap M))) **
    ((CharArray.seg tgs 0 sz ( ms_tags M))) **
    ((CharArray.undef_seg tgs sz ( ms_cap M))) **
    ((IntArray.seg trl 0 ( ms_qtail M) ( mt_trail ( ms_core M)))) **
    ((IntArray.undef_seg trl ( ms_qtail M) ( ms_cap M))) **
    ((wlists_rep wl sz ( ms_wm M) ( ms_wcaps M))) **
    ((wlists_undef wl (Z.mul 2 sz) (Z.mul 2 ( ms_cap M))))
    ) ** (
    ALL (y : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y))
      ).

Definition solver_qcp_strategy63 :=
  forall (s : Z) (n : Z) (opos : Z) (lvl : Z) (tgs : Z) (wl : Z) (trl : Z) (rsn : Z) (act : Z) (M : msolver),
    TT &&
    emp **
    ((solver_analyze_open_at s M n act opos rsn lvl trl tgs wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") n)) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") ( ms_qtail M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") act)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") opos)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") tgs)) **
    ((DoubleArray.seg act 0 n ( ms_activity M))) **
    ((IntArray.seg opos 0 n ( ms_orderpos M))) **
    ((PtrArray.seg rsn 0 n ( ms_reason_words M))) **
    ((IntArray.seg lvl 0 n ( mt_levels ( ms_core M)))) **
    ((IntArray.seg trl 0 ( ms_qtail M) ( mt_trail ( ms_core M)))) **
    ((CharArray.seg tgs 0 n ( ms_tags M))) **
    ((vecp_rep &( ((s)) # "solver_t" ->ₛ "learnts") ( db_words ( ms_learnt M)) ( ms_learnt_cap M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "tagged") ( ms_tagged M) ( ms_tagged_cap M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "order") ( ms_order M) ( ms_order_cap M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M))) **
    ((store_double &( ((s)) # "solver_t" ->ₛ "var_inc") ( ms_var_inc M))) **
    ((store_float &( ((s)) # "solver_t" ->ₛ "cla_inc") ( ms_cla_inc M))) **
    ((solver_analyze_inert_at s M n act opos rsn lvl trl tgs)) **
    ((solver_analyze_frame s M wl))
    ) ** (
    ALL (dl : (@list fp64)) (yd : fp64) (yf : fp32) (c : Z) (hi : Z) (l : (@list Z)) (lo : Z) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y) || (store_double &( ((s)) # "solver_t" ->ₛ "var_inc") yd) || (store_float &( ((s)) # "solver_t" ->ₛ "cla_inc") yf) || (vecp_rep &( ((s)) # "solver_t" ->ₛ "learnts") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "tagged") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "order") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l c) || (DoubleArray.seg act lo hi dl) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg lvl lo hi l) || (IntArray.seg trl lo hi l) || (CharArray.seg tgs lo hi l) || (poly_store FET_char (Z.add tgs (Z.mul i (@sizeof_front_end_type FET_char))) y) || (poly_store FET_int (Z.add lvl (Z.mul i (@sizeof_front_end_type FET_int))) y) || (poly_store FET_int (Z.add trl (Z.mul i (@sizeof_front_end_type FET_int))) y) || (poly_store FET_ptr (Z.add rsn (Z.mul i (@sizeof_front_end_type FET_ptr))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "tags") y) || (store_double &( ((s)) # "solver_t" ->ₛ "var_inc") yd) || (store_float &( ((s)) # "solver_t" ->ₛ "cla_inc") yf) || (vecp_rep &( ((s)) # "solver_t" ->ₛ "learnts") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "tagged") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "order") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l c) || (DoubleArray.seg act lo hi dl) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg lvl lo hi l) || (IntArray.seg trl lo hi l) || (CharArray.seg tgs lo hi l) || (poly_store FET_char (Z.add tgs (Z.mul i (@sizeof_front_end_type FET_char))) y) || (poly_store FET_int (Z.add lvl (Z.mul i (@sizeof_front_end_type FET_int))) y) || (poly_store FET_int (Z.add trl (Z.mul i (@sizeof_front_end_type FET_int))) y) || (poly_store FET_ptr (Z.add rsn (Z.mul i (@sizeof_front_end_type FET_ptr))) y))
      ).

Definition solver_qcp_strategy64 :=
  forall (s : Z) (act : Z) (opos : Z) (trl : Z) (opos_l : (@list Z)) (ord_l : (@list Z)) (wl : Z) (ord_cap : Z) (rsn_l : (@list Z)) (asg_l : (@list Z)) (rsn : Z) (asg : Z) (M : msolver),
    TT &&
    emp **
    ((solver_cancel_open_at s M act asg opos rsn trl asg_l opos_l rsn_l ord_l ord_cap wl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") ( ms_size M))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") ( mt_qhead ( ms_core M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") ( ms_qtail M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") act)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") opos)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((DoubleArray.seg act 0 ( ms_size M) ( ms_activity M))) **
    ((CharArray.seg asg 0 ( ms_size M) asg_l)) **
    ((IntArray.seg opos 0 ( ms_size M) opos_l)) **
    ((PtrArray.seg rsn 0 ( ms_size M) rsn_l)) **
    ((IntArray.seg trl 0 ( ms_qtail M) ( mt_trail ( ms_core M)))) **
    ((solver_cancel_undef_tail M act asg opos rsn trl)) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "order") ord_l ord_cap)) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M))) **
    ((solver_cancel_frame s M wl))
    ) ** (
    ALL (lo : Z) (l : (@list Z)) (hi : Z) (dl : (@list fp64)) (c : Z) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (veci_rep &( ((s)) # "solver_t" ->ₛ "order") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l c) || (DoubleArray.seg act lo hi dl) || (CharArray.seg asg lo hi l) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg trl lo hi l) || (poly_store FET_int (Z.add trl (Z.mul i (@sizeof_front_end_type FET_int))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "activity") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "orderpos") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (veci_rep &( ((s)) # "solver_t" ->ₛ "order") l c) || (veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l c) || (DoubleArray.seg act lo hi dl) || (CharArray.seg asg lo hi l) || (IntArray.seg opos lo hi l) || (PtrArray.seg rsn lo hi l) || (IntArray.seg trl lo hi l) || (poly_store FET_int (Z.add trl (Z.mul i (@sizeof_front_end_type FET_int))) y))
      ).

Definition solver_qcp_strategy65 :=
  forall (s : Z) (cap : Z) (rsn : Z) (caps : (@list Z)) (reasons0 : (@list Z)) (stats0 : (@list Z)) (wm : (@list (@list Z))) (wl : Z) (n : Z),
    TT &&
    emp **
    ((clause_remove_open_at s n cap wl rsn wm caps stats0 reasons0))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") n)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((PtrArray.seg rsn 0 n reasons0)) **
    ((PtrArray.undef_seg rsn n cap)) **
    ((solver_wlists_handle s wl)) **
    ((wlists_rep wl n wm caps)) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") ( stats_starts stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "decisions") ( stats_decisions stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") ( stats_propagations stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") ( stats_inspects stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") ( stats_conflicts stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses") ( stats_clauses stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") ( stats_clauses_literals stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts") ( stats_learnts stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") ( stats_learnts_literals stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") ( stats_max_literals stats0))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") ( stats_tot_literals stats0)))
    ) ** (
    ALL (lo : Z) (hi : Z) (wn : Z) (wcd : (@list Z)) (wmd : (@list (@list Z))) (l : (@list Z)) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "decisions") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") y) || (wlists_rep wl wn wmd wcd) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (poly_store FET_ptr (Z.add rsn (Z.mul i (@sizeof_front_end_type FET_ptr))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "size") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "starts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "decisions") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "conflicts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "clauses_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "learnts_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "max_literals") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "tot_literals") y) || (wlists_rep wl wn wmd wcd) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (poly_store FET_ptr (Z.add rsn (Z.mul i (@sizeof_front_end_type FET_ptr))) y))
      ).

Definition solver_qcp_strategy66 :=
  forall (s : Z) (wl : Z) (rsn : Z) (trl : Z) (lvl : Z) (asg : Z) (M : msolver),
    TT &&
    emp **
    ((solver_propagate_open_at s M wl asg rsn lvl trl))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") ( mt_qhead ( ms_core M)))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") ( ms_qtail M))) **
    ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") ( ms_simpdb_props M))) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") wl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") asg)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") rsn)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") lvl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") trl)) **
    ((poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "binary") ( ms_binary M))) **
    ((CharArray.seg asg 0 ( ms_size M) ( mt_assigns ( ms_core M)))) **
    ((CharArray.undef_seg asg ( ms_size M) ( ms_cap M))) **
    ((PtrArray.seg rsn 0 ( ms_size M) ( ms_reason_words M))) **
    ((PtrArray.undef_seg rsn ( ms_size M) ( ms_cap M))) **
    ((IntArray.seg lvl 0 ( ms_size M) ( mt_levels ( ms_core M)))) **
    ((IntArray.undef_seg lvl ( ms_size M) ( ms_cap M))) **
    ((IntArray.seg trl 0 ( ms_qtail M) ( mt_trail ( ms_core M)))) **
    ((IntArray.undef_seg trl ( ms_qtail M) ( ms_cap M))) **
    ((veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") ( mt_lim ( ms_core M)) ( ms_lim_cap M))) **
    ((wlists_rep wl ( ms_size M) ( ms_wm M) ( ms_wcaps M))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") ( stats_propagations ( ms_stats M)))) **
    ((poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") ( stats_inspects ( ms_stats M)))) **
    ((solver_propagate_frame s M))
    ) ** (
    ALL (l : (@list Z)) (c : Z) (wmd : (@list (@list Z))) (wcd : (@list Z)) (wn : Z) (hi : Z) (lo : Z) (y : Z) (i : Z),
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "binary") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l c) || (wlists_rep wl wn wmd wcd) || (CharArray.seg asg lo hi l) || (CharArray.undef_seg asg lo hi) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (IntArray.seg lvl lo hi l) || (IntArray.undef_seg lvl lo hi) || (IntArray.seg trl lo hi l) || (IntArray.undef_seg trl lo hi) || (poly_store FET_char (Z.add asg (Z.mul i (@sizeof_front_end_type FET_char))) y) || (poly_store FET_ptr (Z.add rsn (Z.mul i (@sizeof_front_end_type FET_ptr))) y) || (poly_store FET_int (Z.add lvl (Z.mul i (@sizeof_front_end_type FET_int))) y) || (poly_store FET_int (Z.add trl (Z.mul i (@sizeof_front_end_type FET_int))) y)) -*
      TT &&
      emp **
      ((poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qhead") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "qtail") y) || (poly_store FET_int &( ((s)) # "solver_t" ->ₛ "simpdb_props") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "wlists") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "assigns") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "reasons") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "levels") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "trail") y) || (poly_store FET_ptr &( ((s)) # "solver_t" ->ₛ "binary") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "propagations") y) || (poly_store FET_uint64 &( ((&( ((s)) # "solver_t" ->ₛ "stats"))) # "stats_t" ->ₛ "inspects") y) || (veci_rep &( ((s)) # "solver_t" ->ₛ "trail_lim") l c) || (wlists_rep wl wn wmd wcd) || (CharArray.seg asg lo hi l) || (CharArray.undef_seg asg lo hi) || (PtrArray.seg rsn lo hi l) || (PtrArray.undef_seg rsn lo hi) || (IntArray.seg lvl lo hi l) || (IntArray.undef_seg lvl lo hi) || (IntArray.seg trl lo hi l) || (IntArray.undef_seg trl lo hi) || (poly_store FET_char (Z.add asg (Z.mul i (@sizeof_front_end_type FET_char))) y) || (poly_store FET_ptr (Z.add rsn (Z.mul i (@sizeof_front_end_type FET_ptr))) y) || (poly_store FET_int (Z.add lvl (Z.mul i (@sizeof_front_end_type FET_int))) y) || (poly_store FET_int (Z.add trl (Z.mul i (@sizeof_front_end_type FET_int))) y))
      ).

Definition solver_qcp_strategy14 :=
  forall (i : Z) (hi : Z) (lo : Z) (l : (@list fp64)) (v : fp64) (p : Z),
    TT &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((DoubleArray.missing_i p i lo hi l)) **
    ((store_double (Z.add p (Z.mul i (@sizeof_front_end_type FET_double))) v))
    |--
    (
    TT &&
    emp **
    ((DoubleArray.seg p lo hi (@replace_Znth fp64 (Z.sub i lo) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy59 :=
  forall (i : Z) (hi : Z) (j : Z) (p : Z) (q : Z) (lo : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    (“ (i = j) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    emp **
    ((CharArray.missing_i p i lo hi l)) **
    ((poly_store FET_char (Z.add q (Z.mul j (@sizeof_front_end_type FET_char))) v))
    |--
    (
    TT &&
    emp **
    ((CharArray.seg p lo hi (@replace_Znth Z (Z.sub i lo) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition solver_qcp_strategy38 :=
  forall (i : Z) (j : Z) (lo : Z) (p : Z) (q : Z) (hi : Z) (l : (@list Z)) (v : Z),
    TT &&
    (“ (q = p) ”) &&
    (“ (Z.le lo i) ”) &&
    (“ (Z.lt i hi) ”) &&
    (“ (i = j) ”) &&
    emp **
    ((IntArray.missing_i p i lo hi l)) **
    ((poly_store FET_int (Z.add q (Z.mul j (@sizeof_front_end_type FET_int))) v))
    |--
    (
    TT &&
    emp **
    ((IntArray.seg p lo hi (@replace_Znth Z (Z.sub i lo) v l)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type solver_qcp_Strategy_Correct.

  Axiom solver_qcp_strategy12_correctness : solver_qcp_strategy12.
  Axiom solver_qcp_strategy35_correctness : solver_qcp_strategy35.
  Axiom solver_qcp_strategy36_correctness : solver_qcp_strategy36.
  Axiom solver_qcp_strategy69_correctness : solver_qcp_strategy69.
  Axiom solver_qcp_strategy37_correctness : solver_qcp_strategy37.
  Axiom solver_qcp_strategy39_correctness : solver_qcp_strategy39.
  Axiom solver_qcp_strategy40_correctness : solver_qcp_strategy40.
  Axiom solver_qcp_strategy41_correctness : solver_qcp_strategy41.
  Axiom solver_qcp_strategy60_correctness : solver_qcp_strategy60.
  Axiom solver_qcp_strategy68_correctness : solver_qcp_strategy68.
  Axiom solver_qcp_strategy61_correctness : solver_qcp_strategy61.
  Axiom solver_qcp_strategy13_correctness : solver_qcp_strategy13.
  Axiom solver_qcp_strategy67_correctness : solver_qcp_strategy67.
  Axiom solver_qcp_strategy42_correctness : solver_qcp_strategy42.
  Axiom solver_qcp_strategy58_correctness : solver_qcp_strategy58.
  Axiom solver_qcp_strategy57_correctness : solver_qcp_strategy57.
  Axiom solver_qcp_strategy2_correctness : solver_qcp_strategy2.
  Axiom solver_qcp_strategy3_correctness : solver_qcp_strategy3.
  Axiom solver_qcp_strategy4_correctness : solver_qcp_strategy4.
  Axiom solver_qcp_strategy5_correctness : solver_qcp_strategy5.
  Axiom solver_qcp_strategy6_correctness : solver_qcp_strategy6.
  Axiom solver_qcp_strategy7_correctness : solver_qcp_strategy7.
  Axiom solver_qcp_strategy8_correctness : solver_qcp_strategy8.
  Axiom solver_qcp_strategy9_correctness : solver_qcp_strategy9.
  Axiom solver_qcp_strategy16_correctness : solver_qcp_strategy16.
  Axiom solver_qcp_strategy23_correctness : solver_qcp_strategy23.
  Axiom solver_qcp_strategy29_correctness : solver_qcp_strategy29.
  Axiom solver_qcp_strategy33_correctness : solver_qcp_strategy33.
  Axiom solver_qcp_strategy34_correctness : solver_qcp_strategy34.
  Axiom solver_qcp_strategy43_correctness : solver_qcp_strategy43.
  Axiom solver_qcp_strategy44_correctness : solver_qcp_strategy44.
  Axiom solver_qcp_strategy45_correctness : solver_qcp_strategy45.
  Axiom solver_qcp_strategy46_correctness : solver_qcp_strategy46.
  Axiom solver_qcp_strategy47_correctness : solver_qcp_strategy47.
  Axiom solver_qcp_strategy48_correctness : solver_qcp_strategy48.
  Axiom solver_qcp_strategy49_correctness : solver_qcp_strategy49.
  Axiom solver_qcp_strategy50_correctness : solver_qcp_strategy50.
  Axiom solver_qcp_strategy51_correctness : solver_qcp_strategy51.
  Axiom solver_qcp_strategy52_correctness : solver_qcp_strategy52.
  Axiom solver_qcp_strategy53_correctness : solver_qcp_strategy53.
  Axiom solver_qcp_strategy54_correctness : solver_qcp_strategy54.
  Axiom solver_qcp_strategy55_correctness : solver_qcp_strategy55.
  Axiom solver_qcp_strategy56_correctness : solver_qcp_strategy56.
  Axiom solver_qcp_strategy62_correctness : solver_qcp_strategy62.
  Axiom solver_qcp_strategy63_correctness : solver_qcp_strategy63.
  Axiom solver_qcp_strategy64_correctness : solver_qcp_strategy64.
  Axiom solver_qcp_strategy65_correctness : solver_qcp_strategy65.
  Axiom solver_qcp_strategy66_correctness : solver_qcp_strategy66.
  Axiom solver_qcp_strategy14_correctness : solver_qcp_strategy14.
  Axiom solver_qcp_strategy59_correctness : solver_qcp_strategy59.
  Axiom solver_qcp_strategy38_correctness : solver_qcp_strategy38.

End solver_qcp_Strategy_Correct.
