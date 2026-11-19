Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
(* From AUXLib Require Import List_lemma. *)
From AUXLib Require Import ListLib.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Require Import ListLib.General.Presuffix.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.

From MonadLib Require Export MonadLib.
Export StateRelMonadErr.
Export MonadNotation.

Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sets.
Local Open Scope sac_scope.
Import naive_C_Rules.

(* 以下是用于 annotation 中的定义 *)

Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).
Definition applyf {A B : Type} (f : A -> B) (a : A) := f a.

Definition uchar_ptr_option_repr (base ptr : addr) (stride : Z) : option Z :=
  if Z.eq_dec ptr NULL then None
  else Some ((ptr - base) / stride).

Definition memcmp_eq (bytes : list Z) (off1 off2 n : Z) : Prop :=
  sublist off1 (off1 + n) bytes = sublist off2 (off2 + n) bytes.

Definition memcmp_result (bytes : list Z) (off1 off2 n ret : Z) : Prop :=
  ret = 0 <-> memcmp_eq bytes off1 off2 n.

Definition maxsuf_state : Type := (Z * Z * Z * Z)%type.
Definition maxsuf_ret : Type := (Z * Z)%type.

(* MARK : 这里都是新的指标的版本 k = p = 1 开始的 *)
Definition maxsuf_cal_body (cmp_fn: Z -> Z -> Datatypes.comparison) (patn: list Z) (s: maxsuf_state): program unit (CntOrBrk maxsuf_state maxsuf_ret) :=
        let '(i, j, k, p) := s in
        choice 
        (assume!! (j + k = Zlength patn);; break (i, p))
        (assume!! (j + k < Zlength patn);; assume!! (0 <= i + k < Zlength patn);;
        match cmp_fn (Znth (j + k) patn 0) (Znth (i + k) patn 0) with
        | Lt =>
                let new_j := j + k in
                let new_k := 1 in
                let new_p := new_j - i in
                continue (i, new_j, new_k, new_p)
        | Eq =>
                choice
                (assume!! (k = p);; continue (i, j + p, 1, p))
                (assume!! (k <> p);;continue (i, j, k + 1, p))
        | Gt =>
                let new_i := j in
                let new_j := j + 1 in
                let new_k := 1 in
                let new_p := 1 in
                continue (new_i, new_j, new_k, new_p)
        end).

Definition maxsuf_cal (cmp_fn: Z -> Z -> Datatypes.comparison) (patn: list Z) (init: maxsuf_state): program unit maxsuf_ret :=
	repeat_break (maxsuf_cal_body cmp_fn patn) init.

Definition maxsuf_fwd (patn: list Z) : program unit maxsuf_ret :=
	maxsuf_cal Z.compare patn (-1, 0, 1, 1).

Definition maxsuf_rev (patn: list Z) : program unit maxsuf_ret :=
	maxsuf_cal (fun a b => Z.compare b a) patn (-1, 0, 1, 1).

Definition maxsuf_fwd_from_state (patn: list Z) (i j k p: Z) : program unit maxsuf_ret :=
        maxsuf_cal Z.compare patn (i, j, k, p).

Definition maxsuf_rev_from_state (patn: list Z) (i j k p: Z) : program unit maxsuf_ret :=
        maxsuf_cal (fun a b => Z.compare b a) patn (i, j, k, p).

Definition maxsuf_choose_with_ms (ms msr p pr: Z) : program unit maxsuf_ret :=
        choice (assume!! (msr < ms);; return (ms + 1, p))
                (assume!! (ms <= msr);; return (msr + 1, pr)).

Definition maxsuf_rev_from (needle: list Z) (ms p: Z): program unit maxsuf_ret :=
	'(msr, pr) <- maxsuf_rev needle;;
        maxsuf_choose_with_ms ms msr p pr.

Definition critical_factorization_prog (needle: list Z) : program unit maxsuf_ret :=
	'(ms, p) <- maxsuf_fwd needle;;
	'(msr, pr) <- maxsuf_rev needle;;
        maxsuf_choose_with_ms ms msr p pr.

Definition first_loop_bind (patn : list Z) (i j k p: Z): program unit maxsuf_ret:= 
        '(ms, p) <- (maxsuf_fwd_from_state patn i j k p);;
        maxsuf_rev_from patn ms p.

Definition second_loop_bind (patn : list Z) (i j k p ms p1: Z): program unit maxsuf_ret:= 
        '(msr, pr) <- (maxsuf_rev_from_state patn i j k p);;
        maxsuf_choose_with_ms ms msr p1 pr.

(* 以下是 match_phase 相关的定义 *)

Definition repetitive_split (patn : list Z) (l p : Z) : Prop :=
  sublist 0 l patn = sublist p (l + p) patn.

Definition match_cond (text patn : list Z) (pos j : Z) : Prop :=
  Znth j patn 0 = Znth (pos + j) text 0.

Definition match_right_f (text patn : list Z) (pos j : Z)
  : program unit (CntOrBrk Z Z) :=
  choice
    (assume!! (j < Zlength patn /\ match_cond text patn pos j);;
     continue (j + 1))
    (assume!! (j >= Zlength patn \/ ~ match_cond text patn pos j);;
     break j).

Definition match_right (text patn : list Z) (pos start : Z) : program unit Z :=
  repeat_break (match_right_f text patn pos) start.

Definition match_left_f (text patn : list Z) (pos s j : Z)
  : program unit (CntOrBrk Z Z) :=
  choice
    (assume!! (j >= s /\ match_cond text patn pos j);;
     continue (j - 1))
    (assume!! (j < s \/ ~ match_cond text patn pos j);;
     break j).

Definition match_left (text patn : list Z) (pos s start : Z) : program unit Z :=
  repeat_break (match_left_f text patn pos s) start.

Definition match_loop_body (text patn : list Z) (l p pos : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  choice
    (assume!! (pos + Zlength patn <= Zlength text);;
     j <- match_right text patn pos l;;
     choice
       (assume!! (j = Zlength patn);;
        j' <- match_left text patn pos 0 (l - 1);;
        choice
          (assume!! (j' < 0);; break (Some pos))
          (assume!! (j' >= 0);; continue (pos + p)))
       (assume!! (j < Zlength patn);; continue (pos + j - l + 1)))
    (assume!! (pos + Zlength patn > Zlength text);; break None).

Definition match_algo_from (text patn : list Z) (l p pos : Z)
  : program unit (option Z) :=
  repeat_break (match_loop_body text patn l p) pos.

Definition match_after_left (text patn : list Z) (l p pos j : Z)
  : program unit (option Z) :=
  choice
    (assume!! (j < 0);; return (Some pos))
    (assume!! (j >= 0);; match_algo_from text patn l p (pos + p)).

Definition match_algo_from_left (text patn : list Z) (l p pos s start : Z)
  : program unit (option Z) :=
  j <- match_left text patn pos s start;;
  match_after_left text patn l p pos j.

Definition match_after_right (text patn : list Z) (l p pos j : Z)
  : program unit (option Z) :=
  choice
    (assume!! (j = Zlength patn);;
     match_algo_from_left text patn l p pos 0 (l - 1))
    (assume!! (j < Zlength patn);;
     match_algo_from text patn l p (pos + j - l + 1)).

Definition match_algo_from_right (text patn : list Z) (l p pos start : Z)
  : program unit (option Z) :=
  j <- match_right text patn pos start;;
  match_after_right text patn l p pos j.

Definition match_periodic_state : Type := (Z * Z)%type.

Definition match_periodic_after_left (text patn : list Z) (l p pos memory j : Z)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  choice
    (assume!! (j < memory);; break (Some pos))
    (assume!! (j >= memory);; continue (pos + p, Zlength patn - p)).

Definition match_periodic_from_left (text patn : list Z) (l p pos memory start : Z)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  j <- match_left text patn pos memory start;;
  match_periodic_after_left text patn l p pos memory j.

Definition match_periodic_after_right (text patn : list Z) (l p pos memory j : Z)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  choice
    (assume!! (j = Zlength patn);;
     match_periodic_from_left text patn l p pos memory (l - 1))
    (assume!! (j < Zlength patn);;
     continue (pos + j - l + 1, 0)).

Definition match_periodic_from_right (text patn : list Z) (l p pos memory start : Z)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  j <- match_right text patn pos start;;
  match_periodic_after_right text patn l p pos memory j.

Definition match_periodic_loop_body (text patn : list Z) (l p : Z)
    (s : match_periodic_state)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  let '(pos, memory) := s in
  choice
    (assume!! (pos + Zlength patn <= Zlength text);;
     match_periodic_from_right text patn l p pos memory (Z.max l memory))
    (assume!! (pos + Zlength patn > Zlength text);; break None).

Definition match_algo_periodic_from (text patn : list Z) (l p pos memory : Z)
  : program unit (option Z) :=
  repeat_break (match_periodic_loop_body text patn l p) (pos, memory).

Definition match_algo_periodic_from_left (text patn : list Z) (l p pos memory start : Z)
  : program unit (option Z) :=
  r <- match_periodic_from_left text patn l p pos memory start;;
  match r with
  | by_continue (pos', memory') => match_algo_periodic_from text patn l p pos' memory'
  | by_break res => return res
  end.

Definition match_algo_periodic_from_right (text patn : list Z) (l p pos memory start : Z)
  : program unit (option Z) :=
  r <- match_periodic_from_right text patn l p pos memory start;;
  match r with
  | by_continue (pos', memory') => match_algo_periodic_from text patn l p pos' memory'
  | by_break res => return res
  end.

Definition match_algo (text patn : list Z) (l p : Z) : program unit (option Z) :=
  match_algo_from text patn l p 0.

Definition match_phase (text patn : list Z) (l p : Z) : program unit (option Z) :=
  choice
    (assume!! (repetitive_split patn l p);;
     match_algo_periodic_from text patn l p 0 0)
    (assume!! (~ repetitive_split patn l p);;
     match_algo text patn l (Z.max l (Zlength patn - l) + 1)).

Definition two_way_after_factorization (text patn : list Z): (Z * Z) -> program unit (option Z) :=
  fun res =>
    let '(l, p) := res in
    match_phase text patn l p.

Definition two_way_algo_complete (text patn : list Z) : program unit (option Z) :=
  '(l, p) <- critical_factorization_prog patn;;
    match_phase text patn l p.

Definition no_occur_at (text patn : list Z) (pos: Z) :=
  forall j, 0 <= j < pos ->
    sublist j (j + Zlength patn) text <> patn.

Definition no_match_at (text patn : list Z) (pos : Z) : Prop :=
  sublist pos (pos + Zlength patn) text <> patn.

Definition valid_skip (text patn : list Z) (pos n : Z) : Prop :=
  0 < n /\
  pos + n <= Zlength text /\
  forall k, pos <= k < pos + n -> no_match_at text patn k.

Definition pattern_period (patn : list Z) (p : Z) : Prop :=
  0 < p /\
  forall i, 0 <= i -> i + p < Zlength patn ->
    Znth i patn 0 = Znth (i + p) patn 0.

Definition periodic_memory_match
    (text patn : list Z) (pos p memory : Z) : Prop :=
  pattern_period patn p /\
  (memory = 0 \/ memory = Zlength patn - p) /\
  sublist 0 memory patn = sublist pos (pos + memory) text.

Definition critical_factorization_spec
    (patn : list Z) (res : Z * Z) : Prop :=
  let '(l, p) := res in
  repetitive_split patn l p ->
    pattern_period patn p /\ 0 <= l < p.

Definition matched_range
    (text patn : list Z) (pos lo hi : Z) : Prop :=
  forall k, lo <= k < hi -> match_cond text patn pos k.

Definition last_occ_before (patn : list Z) (upto c idx : Z) : Prop :=
  0 <= idx < upto /\
  Znth idx patn 0 = c /\
  forall k, idx < k < upto -> Znth k patn 0 <> c.

Definition shift_table_build_prefix (patn : list Z) (upto : Z)
    (table : list Z) : Prop :=
  0 <= upto <= Zlength patn /\
  Zlength table = 256 /\
  forall c, 0 <= c < 256 ->
    (exists idx,
        last_occ_before patn upto c idx /\
        Znth c table 0 = Zlength patn - idx - 1) \/
    ((forall idx, 0 <= idx < upto -> Znth idx patn 0 <> c) /\
        Znth c table 0 = Zlength patn).

Definition shift_table_sound (text patn table : list Z) : Prop :=
  shift_table_build_prefix patn (Zlength patn) table /\
  forall pos shift,
    0 <= pos /\
    pos + Zlength patn <= Zlength text ->
    shift = Znth (Znth (pos + Zlength patn - 1) text 0) table 0 ->
    (shift = 0 /\ match_cond text patn pos (Zlength patn - 1)) \/
    valid_skip text patn pos shift.

Definition match_right_last_f (text patn : list Z) (pos j : Z)
  : program unit (CntOrBrk Z Z) :=
  choice
    (assume!! (j < Zlength patn - 1 /\ match_cond text patn pos j);;
     continue (j + 1))
    (assume!! (j >= Zlength patn - 1 \/ ~ match_cond text patn pos j);;
     break j).

Definition match_right_last (text patn : list Z) (pos start : Z)
  : program unit Z :=
  repeat_break (match_right_last_f text patn pos) start.

Definition two_way_match_standard (text patn : list Z) (l p pos : Z)
  : program unit (option Z) :=
  match_algo_from text patn l p pos.

Definition two_way_match_periodic_standard
    (text patn : list Z) (l p pos memory : Z)
  : program unit (option Z) :=
  match_algo_periodic_from text patn l p pos memory.

Definition long_needle_after_left (text patn : list Z) (p pos j : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  choice
    (assume!! (j < 0);; break (Some pos))
    (assume!! (j >= 0);; continue (pos + p)).

Definition long_needle_match_from_left
    (text patn : list Z) (p pos s start : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  j <- match_left text patn pos s start;;
  long_needle_after_left text patn p pos j.

Definition long_needle_after_right (text patn : list Z) (l p pos j : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  choice
    (assume!! (j = Zlength patn - 1);;
     long_needle_match_from_left text patn p pos 0 (l - 1))
    (assume!! (j < Zlength patn - 1);;
     continue (pos + j - l + 1)).

Definition long_needle_match_from_right
    (text patn : list Z) (l p pos start : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  j <- match_right_last text patn pos start;;
  long_needle_after_right text patn l p pos j.

Definition long_needle_match_loop_body (text patn : list Z) (l p pos : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  choice
    (assume!! (pos + Zlength patn <= Zlength text);;
     choice
       (n <- any Z;;
        assume!! (valid_skip text patn pos n);;
        continue (pos + n))
       (assume!! (match_cond text patn pos (Zlength patn - 1));;
        long_needle_match_from_right text patn l p pos l))
    (assume!! (pos + Zlength patn > Zlength text);; break None).

Definition long_needle_match_from (text patn : list Z) (l p pos : Z)
  : program unit (option Z) :=
  repeat_break (long_needle_match_loop_body text patn l p) pos.

Definition long_needle_match_from_right_full
    (text patn : list Z) (l p pos start : Z)
  : program unit (option Z) :=
  r <- long_needle_match_from_right text patn l p pos start;;
  match r with
  | by_continue pos' => long_needle_match_from text patn l p pos'
  | by_break res => return res
  end.

Definition long_needle_match_from_left_full
    (text patn : list Z) (l p pos s start : Z)
  : program unit (option Z) :=
  r <- long_needle_match_from_left text patn p pos s start;;
  match r with
  | by_continue pos' => long_needle_match_from text patn l p pos'
  | by_break res => return res
  end.

Definition long_needle_match_periodic_after_right
    (text patn : list Z) (l p pos memory j : Z)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  choice
    (assume!! (j = Zlength patn - 1);;
     match_periodic_from_left text patn l p pos memory (l - 1))
    (assume!! (j < Zlength patn - 1);;
     continue (pos + j - l + 1, 0)).

Definition long_needle_match_periodic_from_right
    (text patn : list Z) (l p pos memory start : Z)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  j <- match_right_last text patn pos start;;
  long_needle_match_periodic_after_right text patn l p pos memory j.

Definition long_needle_match_periodic_loop_body (text patn : list Z) (l p : Z)
    (s : match_periodic_state)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  let '(pos, memory) := s in
  choice
    (assume!! (pos + Zlength patn <= Zlength text);;
     choice
       (n <- any Z;;
        assume!! (valid_skip text patn pos n);;
        continue (pos + n, 0))
       (assume!! (match_cond text patn pos (Zlength patn - 1));;
        long_needle_match_periodic_from_right text patn l p pos memory
          (Z.max l memory)))
    (assume!! (pos + Zlength patn > Zlength text);; break None).

Definition long_needle_match_periodic_from
    (text patn : list Z) (l p pos memory : Z)
  : program unit (option Z) :=
  repeat_break (long_needle_match_periodic_loop_body text patn l p)
    (pos, memory).

Definition long_needle_match_periodic_from_right_full
    (text patn : list Z) (l p pos memory start : Z)
  : program unit (option Z) :=
  r <- long_needle_match_periodic_from_right text patn l p pos memory start;;
  match r with
  | by_continue (pos', memory') =>
      long_needle_match_periodic_from text patn l p pos' memory'
  | by_break res => return res
  end.

Definition long_needle_match_periodic_from_left_full
    (text patn : list Z) (l p pos memory start : Z)
  : program unit (option Z) :=
  r <- match_periodic_from_left text patn l p pos memory start;;
  match r with
  | by_continue (pos', memory') =>
      long_needle_match_periodic_from text patn l p pos' memory'
  | by_break res => return res
  end.

Definition long_needle_match_phase (text patn : list Z) (l p : Z)
  : program unit (option Z) :=
  choice
    (assume!! (repetitive_split patn l p);;
     long_needle_match_periodic_from text patn l p 0 0)
    (assume!! (~ repetitive_split patn l p);;
     long_needle_match_from text patn l
       (Z.max l (Zlength patn - l) + 1) 0).

Definition two_way_long_needle_after_factorization
    (text patn : list Z) : (Z * Z) -> program unit (option Z) :=
  fun res =>
    let '(l, p) := res in
    long_needle_match_phase text patn l p.

Definition two_way_long_needle_prog (text patn : list Z)
  : program unit (option Z) :=
  '(l, p) <- critical_factorization_prog patn;;
  long_needle_match_phase text patn l p.

Section TwoWayAlgoHighSpec.

Context (text patn : list Z).

Definition no_occur (pos: Z) :=
  forall j, 0 <= j < pos -> 
    sublist j (j + Zlength patn) text <> patn.

Definition first_occur (pos: Z) :=
  no_occur pos /\ sublist pos (pos + Zlength patn) text = patn.

Definition match_post (res : option Z): Prop :=
  match res with
  | Some pos => first_occur pos
  | None => no_occur (Zlength text)
  end.

End TwoWayAlgoHighSpec.

(* The optional precheck is the only additional nondeterministic action.
   The other branch keeps the standard Two-Way comparisons and shifts. *)
Definition generic_match_loop_body (text patn : list Z) (l p pos : Z)
  : program unit (CntOrBrk Z (option Z)) :=
  choice
    (assume!! (pos + Zlength patn <= Zlength text);;
     n <- any Z;;
     assume!! (valid_skip text patn pos n);;
     continue (pos + n))
    (match_loop_body text patn l p pos).

Definition generic_match_from (text patn : list Z) (l p pos : Z)
  : program unit (option Z) :=
  repeat_break (generic_match_loop_body text patn l p) pos.

Definition generic_match_after_left (text patn : list Z) (l p pos j : Z)
  : program unit (option Z) :=
  choice
    (assume!! (j < 0);; return (Some pos))
    (assume!! (j >= 0);; generic_match_from text patn l p (pos + p)).

Definition generic_match_from_left
    (text patn : list Z) (l p pos s start : Z)
  : program unit (option Z) :=
  j <- match_left text patn pos s start;;
  generic_match_after_left text patn l p pos j.

Definition generic_match_after_right (text patn : list Z) (l p pos j : Z)
  : program unit (option Z) :=
  choice
    (assume!! (j = Zlength patn);;
     generic_match_from_left text patn l p pos 0 (l - 1))
    (assume!! (j < Zlength patn);;
     generic_match_from text patn l p (pos + j - l + 1)).

Definition generic_match_from_right
    (text patn : list Z) (l p pos start : Z)
  : program unit (option Z) :=
  j <- match_right text patn pos start;;
  generic_match_after_right text patn l p pos j.

Definition generic_match_periodic_loop_body (text patn : list Z) (l p : Z)
    (s : match_periodic_state)
  : program unit (CntOrBrk match_periodic_state (option Z)) :=
  let '(pos, memory) := s in
  choice
    (assume!! (pos + Zlength patn <= Zlength text);;
     n <- any Z;;
     assume!! (valid_skip text patn pos n);;
     continue (pos + n, 0))
    (match_periodic_loop_body text patn l p (pos, memory)).

Definition generic_match_periodic_from
    (text patn : list Z) (l p pos memory : Z)
  : program unit (option Z) :=
  repeat_break (generic_match_periodic_loop_body text patn l p)
    (pos, memory).

Definition generic_match_periodic_from_left
    (text patn : list Z) (l p pos memory start : Z)
  : program unit (option Z) :=
  r <- match_periodic_from_left text patn l p pos memory start;;
  match r with
  | by_continue (pos', memory') =>
      generic_match_periodic_from text patn l p pos' memory'
  | by_break res => return res
  end.

Definition generic_match_periodic_from_right
    (text patn : list Z) (l p pos memory start : Z)
  : program unit (option Z) :=
  r <- match_periodic_from_right text patn l p pos memory start;;
  match r with
  | by_continue (pos', memory') =>
      generic_match_periodic_from text patn l p pos' memory'
  | by_break res => return res
  end.

Definition generic_match_phase (text patn : list Z) (l p : Z)
  : program unit (option Z) :=
  choice
    (assume!! (repetitive_split patn l p);;
     generic_match_periodic_from text patn l p 0 0)
    (assume!! (~ repetitive_split patn l p);;
     generic_match_from text patn l (Z.max l (Zlength patn - l) + 1) 0).

Definition two_way_generic_after_factorization
    (text patn : list Z) : (Z * Z) -> program unit (option Z) :=
  fun res =>
    let '(l, p) := res in
    generic_match_phase text patn l p.

Definition two_way_generic_prog (text patn : list Z)
  : program unit (option Z) :=
  '(l, p) <- critical_factorization_prog patn;;
  generic_match_phase text patn l p.

Lemma Znth_at_Zlength_default : forall (l : list Z) d,
  Znth (Zlength l) l d = d.
Proof.
  intros l d.
  pose proof (app_Znth2 d l nil (Zlength l) ltac:(lia)) as H.
  rewrite app_nil_r in H.
  rewrite Z.sub_diag in H.
  exact H.
Qed.

Lemma UCharArray_full_Znth_range : forall x n l i,
  0 <= i < n ->
  (UCharArray.full x n l |-- “ 0 <= Znth i l 0 < 256 ”)%sac.
Proof.
  intros x n l i Hi.
  sep_apply_l_atomic (UCharArray.full_split_to_missing_i x i n l 0 Hi).
  prop_apply (store_uchar_range (x + i * sizeof(UCHAR)) (Znth i l 0)).
  Intros.
  entailer!.
  change Byte.max_unsigned with 255 in H.
  lia.
Qed.

Lemma UCharArray_full_Znth_range_le : forall x n l i,
  0 <= i <= n ->
  (UCharArray.full x n l |-- “ 0 <= Znth i l 0 < 256 ”)%sac.
Proof.
  intros x n l i Hi.
  destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
  - apply UCharArray_full_Znth_range; lia.
  - assert (i = n) by lia.
    subst i.
    prop_apply (UCharArray.full_Zlength x n l).
    Intros.
    assert (Hz : Znth n l 0 = 0).
    { match goal with
      | Hlen : Zlength l = n |- _ => rewrite <- Hlen
      | Hlen : n = Zlength l |- _ => rewrite Hlen
      end.
      apply Znth_at_Zlength_default. }
    entailer!; rewrite Hz; lia.
Qed.

Lemma shift_table_build_prefix_step : forall patn upto table,
  shift_table_build_prefix patn upto table ->
  0 <= upto < Zlength patn ->
  0 <= Znth upto patn 0 < 256 ->
  shift_table_build_prefix patn (upto + 1)
    (replace_Znth (Znth upto patn 0) (Zlength patn - upto - 1) table).
Proof.
  intros patn upto table Hbuild Hupto Hc.
  unfold shift_table_build_prefix in *.
  destruct Hbuild as [Hup_rng [Hlen Hchars]].
  repeat split; try lia;
  [ rewrite Zlength_replace_Znth; lia
  | intros c Hcrng;
    destruct (Z.eq_dec c (Znth upto patn 0)) as [Heq | Hneq];
    [ left; exists upto; split;
      [ unfold last_occ_before; repeat split; try lia;
        intros k Hk; assert (k = upto) by lia; subst k; lia
      | subst c; rewrite Znth_replace_Znth_Same; try lia; rewrite Hlen; lia ]
    | specialize (Hchars c Hcrng) as Hold;
      destruct Hold as [[idx [Hlast Hval]] | [Hnone Hval]];
      [ left; exists idx; split;
        [ unfold last_occ_before in *;
          destruct Hlast as [Hidx [Hz Hlater]];
          repeat split; try lia;
          intros k Hk;
          destruct (Z.eq_dec k upto) as [Heqk | Hneqk];
          [ subst k; congruence | apply Hlater; lia ]
        | rewrite Znth_replace_Znth_Diff by lia; exact Hval ]
      | right; split;
        [ intros idx Hidx;
          destruct (Z.eq_dec idx upto) as [Heqi | Hneqi];
          [ subst idx; congruence | apply Hnone; lia ]
        | rewrite Znth_replace_Znth_Diff by lia; exact Hval ] ] ] ].
Qed.

Lemma UCharArray_full_all_Znth_range : forall x n l,
  (UCharArray.full x n l |--
   “ (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 < 256) ”)%sac.
Proof.
  intros x n l.
  revert x n.
  induction l as [| a l IH]; intros x n.
  - rewrite UCharArray.full_empty.
    entailer!.
    intros i Hi.
    rewrite Zlength_nil in Hi.
    lia.
  - rewrite UCharArray.full_unfold.
    sep_apply (UCharArray.seg_to_full x 1 n l).
    prop_apply (store_uchar_range (x + 0 * sizeof(UCHAR)) a).
    prop_apply (IH (x + 1 * sizeof(UCHAR)) (n - 1)).
    Intros.
    entailer!.
    intros i Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + change Byte.max_unsigned with 255 in H.
      unfold Znth.
      simpl.
      lia.
    + rewrite Znth_cons by lia.
      apply H0.
      rewrite Zlength_cons in Hi.
      lia.
Qed.
