Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* The statement's own notion: the longest k for which the first k characters
   of the two strings agree. *)
Definition LCP (a b : list Z) (k : Z) : Prop :=
  max_value_of_subset Z.le
    (fun j => 0 <= j <= Z.min (Zlength a) (Zlength b) /\
              forall i, 0 <= i < j -> Znth i a 0 = Znth i b 0)
    (fun x => x) k.

Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P025 solver Require, so dropped here:
       1 <= Zlength a <= 100 /\
       Forall (fun x => 0 <= x <= 50) a  *)
  True.

(* What the output format accepts as one printed string. *)
Definition ValidAnswerString (s : list Z) : Prop :=
  1 <= Zlength s <= 200 /\ Forall (fun c => 97 <= c <= 122) s.

Definition Spec (a : list Z) (out : list (list Z)) : Prop :=
  Zlength out = Zlength a + 1 /\
  Forall ValidAnswerString out /\
  forall i, 0 <= i < Zlength a ->
    LCP (Znth i out []) (Znth (i + 1) out []) (Znth i a 0).

(* The following predicates describe stable partial output states.  They are
   deliberately about the rows already materialised, not about executions of
   the C loops that create them. *)
Definition BinaryAnswerString (s : list Z) : Prop :=
  Zlength s = 200 /\
  forall q, 0 <= q < 200 -> Znth q s 0 = 97 \/ Znth q s 0 = 98.

Definition EncodedRow (s : list Z) : list (option Z) :=
  map (fun z => Some z) (s ++ [0]).

Definition UnwrittenRow : list (option Z) := repeat None 201%nat.

Definition PrefixSpec (a : list Z) (done : Z) (out : list (list Z)) : Prop :=
  Zlength out = done /\
  Forall BinaryAnswerString out /\
  forall i, 0 <= i < done - 1 ->
    LCP (Znth i out []) (Znth (i + 1) out []) (Znth i a 0).

Definition ProducedRows
    (a : list Z) (done : Z) (rows : list (list (option Z))) : Prop :=
  0 <= done <= Zlength a + 1 /\
  exists out,
    PrefixSpec a done out /\
    rows = map EncodedRow out ++
      repeat UnwrittenRow (Z.to_nat (Zlength a + 1 - done)).

Definition InitialRowProgress
    (n j : Z) (rows : list (list (option Z))) : Prop :=
  0 <= j <= 200 /\
  rows =
    (map (fun z => Some z) (repeat 97 (Z.to_nat j)) ++
      repeat None (Z.to_nat (201 - j))) ::
    repeat UnwrittenRow (Z.to_nat n).

Definition CopyRowPrefix (s : list Z) (j : Z) : list (option Z) :=
  map (fun z => Some z) (sublist 0 j (s ++ [0])) ++
  repeat None (Z.to_nat (201 - j)).

Definition CopyProgress
    (a : list Z) (i j : Z) (rows : list (list (option Z))) : Prop :=
  0 <= i < Zlength a /\
  0 <= j <= 201 /\
  exists out,
    PrefixSpec a (i + 1) out /\
    rows = map EncodedRow out ++
      CopyRowPrefix (Znth i out []) j ::
      repeat UnwrittenRow (Z.to_nat (Zlength a - i - 1)).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma map_repeat_some__initialization : forall n : nat,
  map (fun z : Z => Some z) (repeat 97 n) = repeat (Some 97) n.
Proof.
  intro n.
  induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma repeat_snoc__initialization : forall {A : Type} (x : A) n,
  repeat x n ++ [x] = x :: repeat x n.
Proof.
  intros A x n.
  induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma replace_Znth_zero__initialization : forall {A : Type} (x : A) l,
  replace_Znth 0 x l =
    match l with
    | [] => []
    | _ :: tail => x :: tail
    end.
Proof.
  intros A x l.
  unfold replace_Znth.
  rewrite Z2Nat.inj_0.
  destruct l; reflexivity.
Qed.
Lemma undef_to_initial_mixed__initialization : forall n,
  0 <= n ->
  repeat (repeat None (Z.to_nat 201)) (Z.to_nat (n + 1)) =
    repeat None (Z.to_nat 201) :: repeat UnwrittenRow (Z.to_nat n).
Proof.
  intros n Hn.
  unfold UnwrittenRow.
  assert (Hsucc : Z.to_nat (n + 1) = S (Z.to_nat n)) by lia.
  rewrite Hsucc.
  simpl.
  reflexivity.
Qed.
Lemma initial_row_write_step__initialization : forall n j rows default_row,
  0 <= j < 200 ->
  InitialRowProgress n j rows ->
  InitialRowProgress n (j + 1)
    (replace_Znth 0
      (replace_Znth j (Some 97) (Znth 0 rows default_row)) rows).
Proof.
  intros n j rows default_row Hj Hprogress.
  unfold InitialRowProgress in Hprogress |- *.
  destruct Hprogress as [Hbounds Hrows].
  split; [lia |].
  subst rows.
  change
    (replace_Znth j (Some 97)
       (map (fun z : Z => Some z) (repeat 97 (Z.to_nat j)) ++
        repeat None (Z.to_nat (201 - j))) ::
       repeat UnwrittenRow (Z.to_nat n) =
     (map (fun z : Z => Some z) (repeat 97 (Z.to_nat (j + 1))) ++
      repeat None (Z.to_nat (201 - (j + 1)))) ::
       repeat UnwrittenRow (Z.to_nat n)).
  f_equal.
  rewrite !map_repeat_some__initialization.
  replace (201 - (j + 1)) with (200 - j) by lia.
  assert (Hnext : Z.to_nat (j + 1) = S (Z.to_nat j)) by lia.
  assert (Htail : Z.to_nat (201 - j) = S (Z.to_nat (200 - j))) by lia.
  rewrite Htail.
  change
    (replace_Znth j (Some 97)
       (repeat (Some 97) (Z.to_nat j) ++
        (None :: repeat None (Z.to_nat (200 - j)))) =
     repeat (Some 97) (Z.to_nat (j + 1)) ++
      repeat None (Z.to_nat (200 - j))).
  rewrite (replace_Znth_app_r j (Some 97)
    (repeat (Some 97) (Z.to_nat j))
    (None :: repeat None (Z.to_nat (200 - j)))) by
    (rewrite Zlength_correct, repeat_length; lia).
  rewrite (replace_Znth_nothing j (repeat (Some 97) (Z.to_nat j)) (Some 97)) by
    (rewrite Zlength_correct, repeat_length; lia).
  replace (j - Zlength (repeat (Some 97) (Z.to_nat j))) with 0 by
    (rewrite Zlength_correct, repeat_length; lia).
  rewrite replace_Znth_zero__initialization.
  change
    (repeat (Some 97) (Z.to_nat j) ++
      (Some 97 :: repeat None (Z.to_nat (200 - j))) =
     repeat (Some 97) (Z.to_nat (j + 1)) ++
      repeat None (Z.to_nat (200 - j))).
  rewrite Hnext.
  change
    (repeat (Some 97) (Z.to_nat j) ++ [Some 97] ++
      repeat None (Z.to_nat (200 - j)) =
     (Some 97 :: repeat (Some 97) (Z.to_nat j)) ++
      repeat None (Z.to_nat (200 - j))).
  rewrite app_assoc.
  rewrite repeat_snoc__initialization.
  reflexivity.
Qed.
Lemma initial_row_finish__initialization : forall n a rows default_row,
  1 <= n ->
  n = Zlength a ->
  InitialRowProgress n 200 rows ->
  ProducedRows a 1
    (replace_Znth 0
      (replace_Znth 200 (Some 0) (Znth 0 rows default_row)) rows).
Proof.
  intros n a rows default_row Hn Hlength Hprogress.
  unfold InitialRowProgress in Hprogress.
  destruct Hprogress as [_ Hrows].
  unfold ProducedRows, PrefixSpec, BinaryAnswerString.
  split; [lia |].
  exists [repeat 97 200].
  split.
  - split.
    + simpl. reflexivity.
    + split.
      * constructor.
        -- split.
           ++ rewrite Zlength_correct, repeat_length. reflexivity.
           ++ intros q Hq. rewrite Znth_repeat_lt by lia. left. lia.
        -- constructor.
      * intros i Hi. lia.
  - subst rows.
    unfold EncodedRow.
    change
      (replace_Znth 200 (Some 0)
         (map (fun z : Z => Some z) (repeat 97 (Z.to_nat 200)) ++
          repeat None (Z.to_nat (201 - 200))) ::
        repeat UnwrittenRow (Z.to_nat n) =
       map (fun z : Z => Some z) (repeat 97 200 ++ [0]) ::
        repeat UnwrittenRow (Z.to_nat (Zlength a + 1 - 1))).
    replace (Z.to_nat (Zlength a + 1 - 1)) with (Z.to_nat n) by
      (f_equal; lia).
    f_equal.
Qed.
Lemma produced_rows_to_copy_start__copy_progress :
  forall (a : list Z) (i : Z) (rows : list (list (option Z))),
    0 <= i < Zlength a ->
    ProducedRows a (i + 1) rows ->
    CopyProgress a i 0 rows.
Proof.
  intros a i rows Hi HP.
  unfold ProducedRows in HP.
  destruct HP as [Hdone [out [Hspec Hrows]]].
  unfold CopyProgress.
  split; [lia | split; [lia |]].
  exists out; split; [exact Hspec |].
  rewrite Hrows.
  unfold CopyRowPrefix.
  rewrite Zsublist_nil by lia.
  simpl.
  replace (Zlength a + 1 - (i + 1)) with (Zlength a - i) by lia.
  unfold UnwrittenRow.
  assert
    (Hcount : Z.to_nat (Zlength a - i) =
      Datatypes.S (Z.to_nat (Zlength a - i - 1))).
  { rewrite <- Nat.add_1_r.
    change
      (Z.to_nat (Zlength a - i) =
       (Z.to_nat (Zlength a - i - 1) + Z.to_nat 1)%nat).
    rewrite <- Z2Nat.inj_add by lia.
    f_equal; lia. }
  rewrite Hcount.
  simpl.
  reflexivity.
Qed.
Lemma Znth_map_EncodedRow__copy_progress :
  forall (out : list (list Z)) (i : Z),
    0 <= i < Zlength out ->
    Znth i (map EncodedRow out) (EncodedRow []) = EncodedRow (Znth i out []).
Proof.
  intros out i Hi.
  unfold Znth.
  assert
    (Hmap : forall (xs : list (list Z)) (n : nat),
      nth n (map EncodedRow xs) (EncodedRow []) =
      EncodedRow (nth n xs [])).
  { intros xs n.
    revert n.
    induction xs as [|x xs IH]; intros n; destruct n; simpl; auto. }
  exact (Hmap out (Z.to_nat i)).
Qed.
Lemma copy_progress_source_row__copy_progress :
  forall (a : list Z) (i j : Z) (rows : list (list (option Z)))
         (out : list (list Z)) (d : list (option Z)),
    0 <= i < Zlength a ->
    PrefixSpec a (i + 1) out ->
    rows = map EncodedRow out ++
      CopyRowPrefix (Znth i out []) j ::
      repeat UnwrittenRow (Z.to_nat (Zlength a - i - 1)) ->
    Znth i rows d = EncodedRow (Znth i out []).
Proof.
  intros a i j rows out d Hi Hspec Hrows.
  destruct Hspec as [Houtlen _].
  rewrite Hrows.
  rewrite app_Znth1 by
    (rewrite Zlength_correct, length_map, <- Zlength_correct, Houtlen; lia).
  rewrite (Znth_indep (map EncodedRow out) i d (EncodedRow [])) by
    (rewrite Zlength_correct, length_map, <- Zlength_correct, Houtlen; lia).
  apply Znth_map_EncodedRow__copy_progress.
  rewrite Houtlen.
  lia.
Qed.
Lemma Znth_map_Some__copy_progress :
  forall (xs : list Z) (j : Z),
    0 <= j < Zlength xs ->
    Znth j (map (fun z => Some z) xs) None = Some (Znth j xs 0).
Proof.
  intros xs j Hj.
  unfold Znth.
  assert
    (Hmap : forall (ys : list Z) (n : nat),
      (n < length ys)%nat ->
      nth n (map (fun z => Some z) ys) None = Some (nth n ys 0)).
  { intros ys n Hn.
    revert Hn.
    revert n.
    induction ys as [|y ys IH]; intros n Hn.
    - destruct n; simpl in *; lia.
    - destruct n; simpl.
      + reflexivity.
      + apply IH.
        simpl in Hn.
        apply Nat.succ_lt_mono in Hn.
        exact Hn. }
  apply Hmap.
  rewrite Zlength_correct in Hj.
  lia.
Qed.
Lemma CopyRowPrefix_step__copy_progress :
  forall (s : list Z) (j : Z),
    Zlength s = 200 ->
    0 <= j <= 200 ->
    replace_Znth j (Some (Znth j (s ++ [0]) 0)) (CopyRowPrefix s j) =
      CopyRowPrefix s (j + 1).
Proof.
  intros s j Hlen Hj.
  assert
    (Hsub : sublist 0 (j + 1) (s ++ [0]) =
      sublist 0 j (s ++ [0]) ++ [Znth j (s ++ [0]) 0]).
  { rewrite (sublist_split 0 (j + 1) j (s ++ [0])) by
      (try rewrite Zlength_app_cons; try rewrite Hlen; lia).
    rewrite (sublist_single 0) by
      (try rewrite Zlength_app_cons; try rewrite Hlen; lia).
    reflexivity. }
  assert
    (Hp : Zlength (map (fun z => Some z) (sublist 0 j (s ++ [0]))) = j).
  { rewrite Zlength_correct, length_map, <- Zlength_correct.
    rewrite Zlength_sublist0 by
      (try rewrite Zlength_app_cons; try rewrite Hlen; lia).
    reflexivity. }
  assert
    (Hcount : Z.to_nat (201 - j) =
      Datatypes.S (Z.to_nat (201 - (j + 1)))).
  { rewrite <- Nat.add_1_r.
    change
      (Z.to_nat (201 - j) =
       (Z.to_nat (201 - (j + 1)) + Z.to_nat 1)%nat).
    rewrite <- Z2Nat.inj_add by lia.
    f_equal; lia. }
  unfold CopyRowPrefix.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (j - Zlength (map (fun z => Some z) (sublist 0 j (s ++ [0]))))
    with 0 by lia.
  rewrite Hcount.
  simpl.
  rewrite Hsub, map_app.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma BinaryAnswer_Znth__copy_progress :
  forall (out : list (list Z)) (i : Z),
    Forall BinaryAnswerString out ->
    0 <= i < Zlength out ->
    BinaryAnswerString (Znth i out []).
Proof.
  intros out i Hall Hi.
  apply (proj1 (Forall_Znth BinaryAnswerString [] out) Hall).
  exact Hi.
Qed.
Lemma encoded_replace_nat__row_flip : forall (s : list Z) (n : nat) v,
  (n < length s)%nat ->
  map (fun z => Some z) (replace_nth n s v ++ (0 :: nil)) =
  replace_nth n (map (fun z => Some z) (s ++ (0 :: nil))) (Some v).
Proof.
  intros s n v Hn.
  revert n Hn.
  induction s as [|x s IH]; intros n Hn; simpl in *.
  - lia.
  - destruct n as [|n]; simpl.
    + reflexivity.
    + f_equal.
      apply IH. lia.
Qed.
Lemma Zlength_replace_Znth__row_flip : forall {A : Type} (l : list A) n (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  + simpl. do 2 rewrite Zlength_cons. lia.
  + simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma encoded_replace__row_flip : forall (s : list Z) k v,
  0 <= k < Zlength s ->
  EncodedRow (replace_Znth k v s) =
  replace_Znth k (Some v) (EncodedRow s).
Proof.
  intros s k v Hk.
  unfold EncodedRow, replace_Znth.
  apply encoded_replace_nat__row_flip.
  rewrite Zlength_correct in Hk. lia.
Qed.
Lemma map_some_Znth__row_flip : forall (s : list Z) k,
  0 <= k < Zlength s ->
  Znth k (map (fun z => Some z) s) None = Some (Znth k s 0).
Proof.
  intros s k Hk.
  revert k Hk.
  induction s as [|x s IH]; intros k Hk; simpl in *.
  - rewrite Zlength_nil in Hk. lia.
  - destruct (Z.eq_dec k 0) as [H0 | H0].
    + subst k. rewrite Znth0_cons. reflexivity.
    + rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hk. lia.
Qed.
Lemma Znth_map_EncodedRow__row_flip : forall (out : list (list Z)) i d,
  0 <= i < Zlength out ->
  Znth i (map EncodedRow out) d = EncodedRow (Znth i out (nil : list Z)).
Proof.
  intros out i d Hi.
  revert i d Hi.
  induction out as [|row out IH]; intros i d Hi; simpl in *.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [H0 | H0].
    + subst i. rewrite Znth0_cons. reflexivity.
    + rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma encoded_Znth__row_flip : forall (s : list Z) k,
  0 <= k < Zlength s ->
  Znth k (EncodedRow s) None = Some (Znth k s 0).
Proof.
  intros s k Hk.
  unfold EncodedRow.
  rewrite map_some_Znth__row_flip by
    (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite (app_Znth1 0 s (0 :: nil) k) by lia.
  reflexivity.
Qed.
Lemma toggle_binary_row_lcp__row_flip : forall (s : list Z) k v,
  Zlength s = 200 ->
  (forall q, 0 <= q < 200 -> Znth q s 0 = 97 \/ Znth q s 0 = 98) ->
  0 <= k < 200 ->
  (v = 97 \/ v = 98) ->
  v <> Znth k s 0 ->
  BinaryAnswerString (replace_Znth k v s) /\
  LCP s (replace_Znth k v s) k.
Proof.
  intros s k v Hlen Hbin Hk Hv Hneq.
  split.
  - unfold BinaryAnswerString.
    split.
    + rewrite Zlength_replace_Znth__row_flip. exact Hlen.
    + intros q Hq.
      destruct (Z.eq_dec q k) as [Heq | Hdiff].
      * subst q.
        rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
        exact Hv.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
        apply Hbin. lia.
  - unfold LCP, MaxMinLib.MaxMin.max_value_of_subset,
      MaxMinLib.MaxMin.max_object_of_subset.
    exists k.
    split.
    + split.
      * split.
        -- rewrite Zlength_replace_Znth__row_flip, Hlen. lia.
        -- intros q Hq.
           rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
           reflexivity.
      * intros j Hj.
        destruct Hj as [Hjbound Hjagree].
        destruct (Z_le_gt_dec j k) as [Hle | Hgt]; [exact Hle|].
        exfalso.
        specialize (Hjagree k ltac:(lia)).
        rewrite Znth_replace_Znth_Same in Hjagree by (rewrite Hlen; lia).
        apply Hneq.
        symmetry.
        exact Hjagree.
    + reflexivity.
Qed.
Lemma append_toggled_row__row_flip : forall (a : list Z) (out : list (list Z)) i (newrow : list Z),
  0 <= i < Zlength a ->
  PrefixSpec a (i + 1) out ->
  BinaryAnswerString newrow ->
  LCP (Znth i out (nil : list Z)) newrow (Znth i a 0) ->
  ProducedRows a (i + 1 + 1)
    (map EncodedRow out ++ EncodedRow newrow ::
      repeat UnwrittenRow (Z.to_nat (Zlength a - i - 1))).
Proof.
  intros a out i newrow Hi Hprefix Hbinary Hlcp.
  unfold ProducedRows.
  split; [lia|].
  exists (out ++ (newrow :: nil)).
  split.
  - unfold PrefixSpec in *.
    destruct Hprefix as [Houtlen [Houtbin Hold]].
    repeat split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Houtlen. lia.
    + rewrite Forall_app. split; [exact Houtbin|]. constructor; [exact Hbinary|constructor].
    + intros p Hp.
      destruct (Z_lt_dec p i) as [Hpi | Hnpi].
      * specialize (Hold p ltac:(lia)).
        rewrite (app_Znth1 nil out (newrow :: nil) p) by (rewrite Houtlen; lia).
        rewrite (app_Znth1 nil out (newrow :: nil) (p + 1)) by (rewrite Houtlen; lia).
        exact Hold.
      * assert (Hp_i : p = i) by lia. subst p.
        rewrite (app_Znth1 nil out (newrow :: nil) i) by (rewrite Houtlen; lia).
        rewrite (app_Znth2 nil out (newrow :: nil) (i + 1)) by (rewrite Houtlen; lia).
        replace (i + 1 - Zlength out) with 0 by (rewrite Houtlen; lia).
        rewrite Znth0_cons.
        exact Hlcp.
  - rewrite map_app. simpl.
    replace (Zlength a + 1 - (i + 1 + 1)) with (Zlength a - i - 1) by lia.
    change (map EncodedRow out ++ ((EncodedRow newrow :: nil) ++
      repeat UnwrittenRow (Z.to_nat (Zlength a - i - 1))) =
      (map EncodedRow out ++ (EncodedRow newrow :: nil)) ++
        repeat UnwrittenRow (Z.to_nat (Zlength a - i - 1))).
    apply app_assoc.
Qed.
Lemma Znth_map_inbounds__final_return : forall {A B : Type}
    (f : A -> B) (l : list A) (da : A) (db : B) i,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l da db i Hi.
  revert i Hi.
  induction l as [|x l IH].
  - intros i Hi. rewrite Zlength_nil in Hi. lia.
  - intros i Hi. rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite !Znth0_cons. reflexivity.
    + change (Znth i (f x :: map f l) db = f (Znth i (x :: l) da)).
      rewrite !Znth_cons by lia.
      apply IH. lia.
Qed.
Lemma binary_answer_string_valid__final_return : forall s,
  BinaryAnswerString s -> ValidAnswerString s.
Proof.
  intros s [Hlen Hchars].
  unfold ValidAnswerString.
  split.
  - lia.
  - apply (proj2 (Forall_Znth (fun c : Z => 97 <= c <= 122) 0 s)).
    intros q Hq.
    specialize (Hchars q).
    specialize (Hchars ltac:(rewrite <- Hlen; exact Hq)).
    destruct Hchars as [H97 | H98]; lia.
Qed.
Lemma produced_rows_to_spec__final_return : forall a rows,
  ProducedRows a (Zlength a + 1) rows ->
  exists out,
    rows = map (map (fun z : Z => Some z))
      (map (fun s : list Z => s ++ (0 :: nil)) out) /\
    Spec a out /\
    Zlength out = Zlength a + 1 /\
    (forall i, 0 <= i < Zlength a + 1 ->
       Zlength (Znth i out (@nil Z)) = 200) /\
    Zlength (map (fun s : list Z => s ++ (0 :: nil)) out) = Zlength a + 1 /\
    (forall (d : list Z) i, 0 <= i < Zlength a + 1 ->
       Znth i (map (fun s : list Z => s ++ (0 :: nil)) out) d =
       Znth i out d ++ (0 :: nil)).
Proof.
  intros a rows [_ [out [Hprefix Hrows]]].
  destruct Hprefix as [Hlen [Hall Hlcp]].
  exists out.
  assert (Hrows' :
    rows = map (map (fun z : Z => Some z))
      (map (fun s : list Z => s ++ (0 :: nil)) out)).
  {
    unfold EncodedRow in Hrows.
    replace (Zlength a + 1 - (Zlength a + 1)) with 0 in Hrows by lia.
    simpl in Hrows.
    rewrite app_nil_r in Hrows.
    rewrite Hrows.
    rewrite map_map.
    reflexivity.
  }
  refine (conj Hrows' (conj _ (conj Hlen (conj _ (conj _ _))))).
  - unfold Spec.
    split; [exact Hlen |].
    split.
    + eapply Forall_impl.
      * intros s Hs. apply binary_answer_string_valid__final_return. exact Hs.
      * exact Hall.
    + intros i Hi. apply Hlcp. lia.
  - intros i Hi.
    destruct ((proj1 (Forall_Znth BinaryAnswerString (@nil Z) out) Hall) i
      ltac:(rewrite Hlen; exact Hi))
      as [Hrowlen _].
    exact Hrowlen.
  - rewrite Zlength_correct in Hlen.
    rewrite Zlength_correct.
    rewrite List.length_map.
    exact Hlen.
  - intros d i Hi.
    apply (Znth_map_inbounds__final_return
      (fun s : list Z => s ++ (0 :: nil)) out d d i).
    rewrite Hlen. exact Hi.
Qed.
Lemma copy_progress_mixed_defined__mixed_definedness :
  forall (a : list Z) (i j q : Z) (rows : list (list (option Z)))
         (d : list (option Z)),
    CopyProgress a i j rows ->
    0 <= q < 201 ->
    exists v, Znth q (Znth i rows d) None = Some v.
Proof.
  intros a i j q rows d Hprogress Hq.
  unfold CopyProgress in Hprogress.
  destruct Hprogress as [Hi [_ [out [Hprefix Hrows]]]].
  destruct Hprefix as [Houtlen [Hbinary _]].
  assert (Hiout : 0 <= i < Zlength out) by lia.
  assert (Hencoded_index :
      forall (l : list (list Z)) (idx : Z) (d0 : list (option Z)),
        0 <= idx < Zlength l ->
        Znth idx (map EncodedRow l) d0 = EncodedRow (Znth idx l [])).
  {
    intros l.
    induction l as [| x xs IH]; intros idx d0 Hidx.
    - rewrite Zlength_nil in Hidx. lia.
    - destruct (Z.eq_dec idx 0) as [-> | Hidx0].
      + rewrite !Znth0_cons. reflexivity.
      + change
          (Znth idx (EncodedRow x :: map EncodedRow xs) d0 =
           EncodedRow (Znth idx (x :: xs) [])).
        rewrite !Znth_cons by lia.
        apply IH.
        rewrite Zlength_cons in Hidx. lia.
  }
  assert (Hsome_index :
      forall (l : list Z) (idx : Z),
        0 <= idx < Zlength l ->
        Znth idx (map (fun z => Some z) l) None = Some (Znth idx l 0)).
  {
    intros l.
    induction l as [| x xs IH]; intros idx Hidx.
    - rewrite Zlength_nil in Hidx. lia.
    - destruct (Z.eq_dec idx 0) as [-> | Hidx0].
      + rewrite !Znth0_cons. reflexivity.
      + change
          (Znth idx (Some x :: map (fun z => Some z) xs) None =
           Some (Znth idx (x :: xs) 0)).
        rewrite !Znth_cons by lia.
        apply IH.
        rewrite Zlength_cons in Hidx. lia.
  }
  assert (Hbinary_index :
      forall (l : list (list Z)) (idx : Z),
        Forall BinaryAnswerString l ->
        0 <= idx < Zlength l ->
        BinaryAnswerString (Znth idx l [])).
  {
    intros l idx Hall Hidx.
    revert idx Hidx.
    induction Hall as [| x xs Hx Hxs IH]; intros idx Hidx.
    - rewrite Zlength_nil in Hidx. lia.
    - destruct (Z.eq_dec idx 0) as [-> | Hidx0].
      + rewrite Znth0_cons. exact Hx.
      + rewrite Znth_cons by lia.
        apply IH.
        rewrite Zlength_cons in Hidx. lia.
  }
  pose proof (Hbinary_index out i Hbinary Hiout) as Hbinary_i.
  destruct Hbinary_i as [Hrow_length _].
  assert (Hmap_length : Zlength (map EncodedRow out) = Zlength out).
  {
    rewrite !Zlength_correct.
    rewrite length_map.
    reflexivity.
  }
  assert (Hrow : Znth i rows d = EncodedRow (Znth i out [])).
  {
    rewrite Hrows.
    rewrite app_Znth1 by (rewrite Hmap_length; exact Hiout).
    apply Hencoded_index. exact Hiout.
  }
  exists (Znth q (Znth i out [] ++ [0]) 0).
  rewrite Hrow.
  unfold EncodedRow.
  apply Hsome_index.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.
