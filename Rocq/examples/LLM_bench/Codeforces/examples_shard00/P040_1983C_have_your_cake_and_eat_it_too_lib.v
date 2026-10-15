Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition CakeSumboolIf {P Q : Prop} {T : Type}
    (c : {P} + {Q}) (x y : T) : T :=
  match c with left _ => x | right _ => y end.

Local Notation "'if' c 'then' x 'else' y" :=
  (CakeSumboolIf c x y)
  (at level 200, c at level 200, x at level 200, y at level 79).

Definition DisjointIntervals (l1 r1 l2 r2 : Z) : Prop := r1 < l2 \/ r2 < l1.

Definition ValidCakeDivision (a b c bounds : list Z) : Prop :=
  exists la ra lb rb lc rc total,
    bounds = la :: ra :: lb :: rb :: lc :: rc :: nil /\
    total = fold_right Z.add 0 a /\
    0 <= la <= ra /\ ra < Zlength a /\
    0 <= lb <= rb /\ rb < Zlength b /\
    0 <= lc <= rc /\ rc < Zlength c /\
    DisjointIntervals la ra lb rb /\ DisjointIntervals la ra lc rc /\
    DisjointIntervals lb rb lc rc /\
    3 * fold_right Z.add 0 (sublist la (ra + 1) a) >= total /\
    3 * fold_right Z.add 0 (sublist lb (rb + 1) b) >= total /\
    3 * fold_right Z.add 0 (sublist lc (rc + 1) c) >= total.

Definition Pre (a b c : list Z) : Prop :=
  3 <= Zlength a <= 200000 /\ Zlength b = Zlength a /\ Zlength c = Zlength a /\
  Forall (fun x => 1 <= x <= 1000000) a /\ Forall (fun x => 1 <= x <= 1000000) b /\
  Forall (fun x => 1 <= x <= 1000000) c /\
  fold_right Z.add 0 a = fold_right Z.add 0 b /\
  fold_right Z.add 0 a = fold_right Z.add 0 c.

Definition Spec (a b c : list Z) (out : option (list Z)) : Prop :=
  (exists bounds, out = Some bounds /\ ValidCakeDivision a b c bounds) \/
  (out = None /\ forall bounds, ~ ValidCakeDivision a b c bounds).

Import ListNotations.

Definition CakeSum (l : list Z) : Z := fold_right Z.add 0 l.

Definition CakeOrder (ord : list Z) : Prop :=
  ord = [0; 1; 2] \/ ord = [0; 2; 1] \/
  ord = [1; 0; 2] \/ ord = [1; 2; 0] \/
  ord = [2; 0; 1] \/ ord = [2; 1; 0].

Definition BoundLeft (bounds : list Z) (who : Z) : Z :=
  Znth (2 * who) bounds 0.

Definition BoundRight (bounds : list Z) (who : Z) : Z :=
  Znth (2 * who + 1) bounds 0.

Definition OrderedBy (ord bounds : list Z) : Prop :=
  CakeOrder ord /\
  BoundRight bounds (Znth 0 ord 0) < BoundLeft bounds (Znth 1 ord 0) /\
  BoundRight bounds (Znth 1 ord 0) < BoundLeft bounds (Znth 2 ord 0).

Definition TryOrderSpec
    (a b c ord : list Z) (out : option (list Z)) : Prop :=
  match out with
  | Some bounds => ValidCakeDivision a b c bounds /\ OrderedBy ord bounds
  | None => forall bounds, ValidCakeDivision a b c bounds -> ~ OrderedBy ord bounds
  end.

Definition SearchState
    (rows : list (list Z)) (who start pos need acc : Z) : Prop :=
  let row := Znth who rows [] in
  0 <= start /\ start <= pos /\ pos <= Zlength row /\
  acc = CakeSum (sublist start pos row) /\
  (forall q, start <= q < pos -> CakeSum (sublist start (q + 1) row) < need).

Definition SuffixSumState
    (rows : list (list Z)) (who start pos acc : Z) : Prop :=
  let row := Znth who rows [] in
  0 <= start /\ start <= pos /\ pos <= Zlength row /\
  acc = CakeSum (sublist start pos row).

Definition GreedyPrefixState
    (rows : list (list Z)) (ord : list Z) (need part pos : Z)
    (left right : list Z) : Prop :=
  CakeOrder ord /\ Zlength left = 3 /\ Zlength right = 3 /\
  0 <= part <= 2 /\ 0 <= pos <= Zlength (Znth 0 rows []) /\
  (forall k, 0 <= k < part ->
    let who := Znth k ord 0 in
    let lo := Znth who left 0 in
    let hi := Znth who right 0 in
    0 <= who < 3 /\ 0 <= lo /\ lo <= hi /\
    hi < Zlength (Znth who rows []) /\
    lo = if Z.eq_dec k 0 then 0
         else Znth (Znth (k - 1) ord 0) right 0 + 1 /\
    need <= CakeSum (sublist lo (hi + 1) (Znth who rows [])) /\
    (forall q, lo <= q < hi ->
      CakeSum (sublist lo (q + 1) (Znth who rows [])) < need)) /\
  pos = if Z.eq_dec part 0 then 0
        else Znth (Znth (part - 1) ord 0) right 0 + 1.

Definition OutputBounds (left right : list Z) : list Z :=
  [Znth 0 left 0 - 1; Znth 0 right 0 - 1;
   Znth 1 left 0 - 1; Znth 1 right 0 - 1;
   Znth 2 left 0 - 1; Znth 2 right 0 - 1].

Definition OrderAt (z : Z) (ord : list Z) : Prop :=
  (z = 0 /\ ord = [0; 1; 2]) \/
  (z = 1 /\ ord = [0; 2; 1]) \/
  (z = 2 /\ ord = [1; 0; 2]) \/
  (z = 3 /\ ord = [1; 2; 0]) \/
  (z = 4 /\ ord = [2; 0; 1]) \/
  (z = 5 /\ ord = [2; 1; 0]).

Definition OrderTable (table : list Z) : Prop :=
  table = [0; 1; 2; 0; 2; 1; 1; 0; 2; 1; 2; 0; 2; 0; 1; 2; 1; 0].

Definition OrderFor (z : Z) : list Z :=
  if Z.eq_dec z 0 then [0; 1; 2] else
  if Z.eq_dec z 1 then [0; 2; 1] else
  if Z.eq_dec z 2 then [1; 0; 2] else
  if Z.eq_dec z 3 then [1; 2; 0] else
  if Z.eq_dec z 4 then [2; 0; 1] else [2; 1; 0].

Definition FailedOrders (a b c : list Z) (z : Z) : Prop :=
  forall k, 0 <= k < z ->
    exists ord, OrderAt k ord /\ TryOrderSpec a b c ord None.

Definition SearchPrefixState
    (rows : list (list Z)) (who start pos need acc : Z) : Prop :=
  let row := Znth who rows [] in
  0 <= start /\ start <= pos /\ pos <= Zlength row /\
  acc = CakeSum (sublist start pos row) /\
  (forall q, start <= q < pos -> CakeSum (sublist start q row) < need).

Definition GreedyRawState
    (rows : list (list Z)) (ord : list Z) (need part pos : Z)
    (left right : list Z) : Prop :=
  CakeOrder ord /\ Zlength left = 3 /\ Zlength right = 3 /\
  0 <= part <= 2 /\ 0 <= pos <= Zlength (Znth 0 rows []) /\
  (forall k, 0 <= k < part ->
    let who := Znth k ord 0 in
    let lo := Znth who left 0 in
    let hi := Znth who right 0 in
    0 <= who < 3 /\ 1 <= lo /\ lo <= hi /\
    hi <= Zlength (Znth who rows []) /\
    lo = (if Z.eq_dec k 0 then 1
          else Znth (Znth (k - 1) ord 0) right 0 + 1) /\
    need <= CakeSum (sublist (lo - 1) hi (Znth who rows [])) /\
    (forall q, lo - 1 <= q < hi ->
      CakeSum (sublist (lo - 1) q (Znth who rows [])) < need)) /\
  pos = (if Z.eq_dec part 0 then 0
         else Znth (Znth (part - 1) ord 0) right 0).

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma cake_sum_bounds_from_forall__try_initialization :
  forall xs,
    Forall (fun x : Z => 1 <= x <= 1000000) xs ->
    Zlength xs <= CakeSum xs /\
    CakeSum xs <= Zlength xs * 1000000.
Proof.
  intros xs Hxs.
  induction Hxs as [| x xs Hx Hxs IH].
  - unfold CakeSum.
    simpl.
    rewrite Zlength_nil.
    split; lia.
  - destruct IH as [IHlo IHhi].
    unfold CakeSum in *.
    simpl in *.
    rewrite Zlength_cons.
    split; nia.
Qed.
Lemma sum_nonnegative_pointwise__try_terminal_semantics :
  forall xs,
    (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0) ->
    0 <= ListLib.sum xs.
Proof.
  intros xs Hnonneg.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - pose proof (Zlength_nonneg xs) as Hlen.
    assert (Hx : 0 <= x).
    { specialize (Hnonneg 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hnonneg. exact Hnonneg. }
    assert (Htail : forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0).
    { intros k Hk. specialize (Hnonneg (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hnonneg by lia.
      replace (k + 1 - 1) with k in Hnonneg by lia. exact Hnonneg. }
    specialize (IH Htail). lia.
Qed.
Lemma sum_sublist_nonnegative__try_terminal_semantics :
  forall xs lo hi,
    (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0) ->
    0 <= lo <= hi ->
    hi <= Zlength xs ->
    0 <= ListLib.sum (sublist lo hi xs).
Proof.
  intros xs lo hi Hnonneg Hlo Hhi.
  apply sum_nonnegative_pointwise__try_terminal_semantics.
  intros k Hk.
  rewrite Zlength_sublist in Hk by lia.
  rewrite Znth_sublist by lia.
  apply Hnonneg. lia.
Qed.
Lemma sum_sublist_inclusion__try_terminal_semantics :
  forall xs outer_lo inner_lo inner_hi outer_hi,
    (forall k, 0 <= k < Zlength xs -> 0 <= Znth k xs 0) ->
    0 <= outer_lo <= inner_lo ->
    inner_lo <= inner_hi <= outer_hi ->
    outer_hi <= Zlength xs ->
    ListLib.sum (sublist inner_lo inner_hi xs) <=
    ListLib.sum (sublist outer_lo outer_hi xs).
Proof.
  intros xs outer_lo inner_lo inner_hi outer_hi Hnonneg Hleft Hright Hbound.
  rewrite (sublist_split outer_lo outer_hi inner_lo xs) by lia.
  rewrite (sublist_split inner_lo outer_hi inner_hi xs) by lia.
  rewrite !ListLib.sum_app.
  pose proof (sum_sublist_nonnegative__try_terminal_semantics
    xs outer_lo inner_lo Hnonneg ltac:(lia) ltac:(lia)).
  pose proof (sum_sublist_nonnegative__try_terminal_semantics
    xs inner_hi outer_hi Hnonneg ltac:(lia) ltac:(lia)).
  lia.
Qed.
Lemma ceil_third_threshold__try_terminal_semantics :
  forall total need s,
    0 <= total ->
    need = (total + 2) / 3 ->
    (need <= s <-> total <= 3 * s).
Proof.
  intros total need s Htotal ->.
  pose proof (Z.div_mod (total + 2) 3 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (total + 2) 3 ltac:(lia)) as Hmod.
  split; intros; nia.
Qed.
Lemma sublist_full__try_terminal_semantics :
  forall (A : Type) (xs : list A), sublist 0 (Zlength xs) xs = xs.
Proof.
  intros A xs.
  pose proof (@sublist_app_exact1 A xs nil) as H.
  rewrite app_nil_r in H. exact H.
Qed.
Lemma greedy_terminal_success__try_terminal_semantics :
  forall a b c ord need n pos who acc left right,
    Pre a b c ->
    (forall row col,
      ((0 <= row < 3 /\ 0 <= col) /\ col < Zlength a) ->
      1 <= Znth col (Znth row (a :: b :: c :: nil) nil) 0 <= 1000000) ->
    n = Zlength a ->
    need = (ListLib.sum a + 2) / 3 ->
    CakeOrder ord ->
    who = Znth 2 ord 0 ->
    GreedyRawState (a :: b :: c :: nil) ord need 2 pos left right ->
    SuffixSumState (a :: b :: c :: nil) who pos n acc ->
    need <= acc ->
    TryOrderSpec a b c ord
      (Some (OutputBounds (replace_Znth who (pos + 1) left)
                          (replace_Znth who n right))).
Proof.
  intros a b c ord need n pos who acc left right
    Hpre Hvalues Hn Hneed Hord Hwho Hgreedy Hsuffix Hacc.
  destruct Hpre as (Hlen & Hlenb & Hlenc & HFa & HFb & HFc & Hsumab & Hsumac).
  assert (Hnonnega : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
  { intros k Hk. specialize (Hvalues 0 k ltac:(lia)).
    repeat rewrite Znth0_cons in Hvalues. lia. }
  pose proof (sum_nonnegative_pointwise__try_terminal_semantics a Hnonnega) as Htotal.
  pose proof (ceil_third_threshold__try_terminal_semantics
    (ListLib.sum a) need acc Htotal Hneed) as Hceil.
  assert (Htotalpos : 0 < ListLib.sum a).
  { pose proof (sum_sublist_inclusion__try_terminal_semantics
      a 0 0 1 (Zlength a) Hnonnega ltac:(lia) ltac:(lia) ltac:(lia)) as Hinc.
    rewrite sublist_full__try_terminal_semantics in Hinc.
    rewrite (sublist_single 0 0) in Hinc by lia.
    specialize (Hvalues 0 0 ltac:(lia)).
    repeat rewrite Znth0_cons in Hvalues.
    unfold ListLib.sum in Hinc. simpl in Hinc.
    unfold ListLib.sum. lia. }
  assert (Hneedpos : 0 < need).
  { pose proof (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need 0 Htotal Hneed) as Hceil0.
    destruct (Z_le_gt_dec need 0); [pose proof (proj1 Hceil0 l); lia | lia]. }
  destruct Hord as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  all: repeat rewrite Znth_cons in Hwho by lia.
  all: repeat rewrite Znth0_cons in Hwho.
  all: subst who.
  all: unfold GreedyRawState in Hgreedy.
  all: repeat rewrite Znth_cons in Hgreedy by lia.
  all: repeat rewrite Znth0_cons in Hgreedy.
  all: destruct Hgreedy as
    (Hcake & Hleftlen & Hrightlen & Hpart & Hposbound & Hdone & Hposeq).
  all: pose proof (Hdone 0 ltac:(lia)) as Hfirst.
  all: pose proof (Hdone 1 ltac:(lia)) as Hsecond.
  all: clear Hdone.
  all: repeat rewrite Znth_cons in Hfirst, Hsecond, Hposeq by lia.
  all: repeat rewrite Znth0_cons in Hfirst, Hsecond, Hposeq.
  all: cbn [CakeSumboolIf] in Hfirst, Hsecond, Hposeq.
  all: unfold Znth, CakeSumboolIf in Hfirst, Hsecond, Hposeq;
       simpl in Hfirst, Hsecond, Hposeq.
  all: destruct Hfirst as
    (Hfwho & Hflo & Hflr & Hfrlen & Hfstart & Hfsum & Hfmin).
  all: destruct Hsecond as
    (Hswho & Hslo & Hslr & Hsrlen & Hsstart & Hssum & Hsmin).
  all: unfold SuffixSumState, CakeSum in Hsuffix.
  all: repeat rewrite Znth_cons in Hsuffix by lia.
  all: repeat rewrite Znth0_cons in Hsuffix.
  all: destruct Hsuffix as (Hs0 & Hspos & Hsend & Hsum).
  all: assert (Hposlt : pos < n) by
    (destruct (Z.eq_dec pos n) as [-> | Hneq];
     [rewrite Zsublist_nil in Hsum by lia;
      unfold CakeSum, ListLib.sum in Hsum; simpl in Hsum; lia | lia]).
  all: lazymatch type of Hfsum with ?nn <= ?sf =>
    pose proof (proj1 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need sf Htotal Hneed) Hfsum) as Hfvalid
    end.
  all: lazymatch type of Hssum with ?nn <= ?ss =>
    pose proof (proj1 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need ss Htotal Hneed) Hssum) as Hsvalid
    end.
  all: pose proof (proj1 Hceil Hacc) as Htvalid.
  all: unfold CakeSum, ListLib.sum in Hfvalid, Hsvalid, Htvalid.
  all: unfold TryOrderSpec.
  all: split.
  all: tryif match goal with |- ValidCakeDivision _ _ _ _ => idtac end
    then
      (unfold ValidCakeDivision, OutputBounds;
       eexists; eexists; eexists; eexists; eexists; eexists; eexists;
       repeat rewrite Zlength_replace_Znth;
       repeat first
         [ rewrite Znth_replace_Znth_Same by lia
         | rewrite Znth_replace_Znth_Diff by lia ];
       repeat first [ rewrite Znth_cons by lia | rewrite Znth0_cons ];
       unfold Znth in *; simpl in *;
       unfold DisjointIntervals;
       cbn [CakeSumboolIf] in *;
       repeat rewrite Z.sub_add;
       repeat split; try reflexivity; try lia;
       try (apply (proj1 Hceil); lia))
    else
      (unfold OrderedBy, BoundLeft, BoundRight, CakeOrder, OutputBounds;
       repeat rewrite Zlength_replace_Znth;
       repeat first
         [ rewrite Znth_replace_Znth_Same by lia
         | rewrite Znth_replace_Znth_Diff by lia ];
       repeat first [ rewrite Znth_cons by lia | rewrite Znth0_cons ];
       unfold Znth in *; simpl in *;
       cbn [CakeSumboolIf] in *;
       repeat split; try tauto; try lia;
       match goal with |- ?G => fail 1 "ORDER_GOAL:" G end).
  all: try lia.
  all: try (replace (pos + 1 - 1) with pos by lia).
  all: rewrite Hsum in Htvalid.
  all: lia.
  all: match goal with |- ?G => fail 1 "REMAIN_GOAL:" G end.
Qed.
Lemma greedy_terminal_exclusion_chain__try_terminal_semantics :
  forall x y z need n g1 g2 acc l1 u1 l2 u2 l3 u3,
    Zlength x = n -> Zlength y = n -> Zlength z = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k x 0) ->
    (forall k, 0 <= k < n -> 0 <= Znth k y 0) ->
    (forall k, 0 <= k < n -> 0 <= Znth k z 0) ->
    0 <= g1 <= g2 -> g2 <= n ->
    (forall q, 0 <= q < g1 -> CakeSum (sublist 0 q x) < need) ->
    (forall q, g1 <= q < g2 -> CakeSum (sublist g1 q y) < need) ->
    acc = CakeSum (sublist g2 n z) -> acc < need ->
    0 <= l1 <= u1 -> u1 < n ->
    0 <= l2 <= u2 -> u2 < n ->
    0 <= l3 <= u3 -> u3 < n ->
    u1 < l2 -> u2 < l3 ->
    need <= CakeSum (sublist l1 (u1 + 1) x) ->
    need <= CakeSum (sublist l2 (u2 + 1) y) ->
    need <= CakeSum (sublist l3 (u3 + 1) z) -> False.
Proof.
  intros x y z need n g1 g2 acc l1 u1 l2 u2 l3 u3
    Hxlen Hylen Hzlen Hxnon HyNon Hznon Hg Hg2n Hmin1 Hmin2 Haccsum Hacc
    Hb1 Hu1 Hb2 Hu2 Hb3 Hu3 Hord12 Hord23 Hv1 Hv2 Hv3.
  assert (Hg1 : g1 <= u1 + 1).
  { destruct (Z_le_gt_dec g1 (u1 + 1)); [lia|].
    pose proof (Hmin1 (u1 + 1) ltac:(lia)) as Hsmall.
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      x 0 l1 (u1 + 1) (u1 + 1)
      ltac:(intros; apply Hxnon; lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Hxlen; lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia. }
  assert (Hg1l2 : g1 <= l2) by lia.
  assert (Hg2 : g2 <= u2 + 1).
  { destruct (Z_le_gt_dec g2 (u2 + 1)); [lia|].
    pose proof (Hmin2 (u2 + 1) ltac:(lia)) as Hsmall.
    pose proof (sum_sublist_inclusion__try_terminal_semantics
      y g1 l2 (u2 + 1) (u2 + 1)
      ltac:(intros; apply HyNon; lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite Hylen; lia)) as Hinc.
    unfold CakeSum, ListLib.sum in *. lia. }
  assert (Hg2l3 : g2 <= l3) by lia.
  pose proof (sum_sublist_inclusion__try_terminal_semantics
    z g2 l3 (u3 + 1) n
    ltac:(intros; apply Hznon; lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite Hzlen; lia)) as Hinc.
  unfold CakeSum, ListLib.sum in *. lia.
Qed.
Lemma greedy_terminal_failure__try_terminal_semantics :
  forall a b c ord need n pos who acc left right,
    Pre a b c ->
    (forall row col,
      ((0 <= row < 3 /\ 0 <= col) /\ col < Zlength a) ->
      1 <= Znth col (Znth row (a :: b :: c :: nil) nil) 0 <= 1000000) ->
    n = Zlength a ->
    need = (ListLib.sum a + 2) / 3 ->
    CakeOrder ord ->
    who = Znth 2 ord 0 ->
    GreedyRawState (a :: b :: c :: nil) ord need 2 pos left right ->
    SuffixSumState (a :: b :: c :: nil) who pos n acc ->
    acc < need -> TryOrderSpec a b c ord None.
Proof.
  intros a b c ord need n pos who acc left right
    Hpre Hvalues Hn Hneed Hord Hwho Hgreedy Hsuffix Hacc.
  destruct Hpre as (Hlen & Hlenb & Hlenc & HFa & HFb & HFc & Hsumab & Hsumac).
  assert (Hna : forall k, 0 <= k < Zlength a -> 0 <= Znth k a 0).
  { intros; specialize (Hvalues 0 k ltac:(lia)); repeat rewrite Znth0_cons in Hvalues; lia. }
  assert (Hnb : forall k, 0 <= k < Zlength b -> 0 <= Znth k b 0).
  { intros; specialize (Hvalues 1 k ltac:(lia)); rewrite Znth_cons in Hvalues by lia;
    repeat rewrite Znth0_cons in Hvalues; lia. }
  assert (Hnc : forall k, 0 <= k < Zlength c -> 0 <= Znth k c 0).
  { intros; specialize (Hvalues 2 k ltac:(lia)); repeat rewrite Znth_cons in Hvalues by lia;
    repeat rewrite Znth0_cons in Hvalues; lia. }
  pose proof (sum_nonnegative_pointwise__try_terminal_semantics a Hna) as Htotal.
  destruct Hord as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  all: repeat rewrite Znth_cons in Hwho by lia.
  all: repeat rewrite Znth0_cons in Hwho.
  all: subst who.
  all: unfold GreedyRawState in Hgreedy.
  all: repeat rewrite Znth_cons in Hgreedy by lia.
  all: repeat rewrite Znth0_cons in Hgreedy.
  all: destruct Hgreedy as
    (Hcake & Hleftlen & Hrightlen & Hpart & Hposbound & Hdone & Hposeq).
  all: pose proof (Hdone 0 ltac:(lia)) as Hfirst.
  all: pose proof (Hdone 1 ltac:(lia)) as Hsecond.
  all: clear Hdone.
  all: repeat rewrite Znth_cons in Hfirst, Hsecond, Hposeq by lia.
  all: repeat rewrite Znth0_cons in Hfirst, Hsecond, Hposeq.
  all: unfold Znth, CakeSumboolIf in Hfirst, Hsecond, Hposeq;
       simpl in Hfirst, Hsecond, Hposeq.
  all: destruct Hfirst as
    (Hfwho & Hflo & Hflr & Hfrlen & Hfstart & Hfsum & Hfmin).
  all: destruct Hsecond as
    (Hswho & Hslo & Hslr & Hsrlen & Hsstart & Hssum & Hsmin).
  all: unfold SuffixSumState, CakeSum in Hsuffix.
  all: repeat rewrite Znth_cons in Hsuffix by lia.
  all: repeat rewrite Znth0_cons in Hsuffix.
  all: destruct Hsuffix as (Hs0 & Hspos & Hsend & Haccsum).
  all: unfold TryOrderSpec; intros bounds Hvalid Hordered.
  all: unfold ValidCakeDivision in Hvalid.
  all: destruct Hvalid as
    (la & ra & lb & rb & lc & rc & total & Hbeq & Htot &
     Hba & Hra & Hbb & Hrb & Hbc & Hrc & Hdab & Hdac & Hdbc & Hva & Hvb & Hvc).
  all: subst bounds; subst total.
  all: assert (HvaNeed : need <= CakeSum (sublist la (ra + 1) a)) by
    (apply (proj2 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need (CakeSum (sublist la (ra + 1) a)) Htotal Hneed));
     unfold CakeSum, ListLib.sum in *; lia).
  all: assert (HvbNeed : need <= CakeSum (sublist lb (rb + 1) b)) by
    (apply (proj2 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need (CakeSum (sublist lb (rb + 1) b)) Htotal Hneed));
     unfold CakeSum, ListLib.sum in *; lia).
  all: assert (HvcNeed : need <= CakeSum (sublist lc (rc + 1) c)) by
    (apply (proj2 (ceil_third_threshold__try_terminal_semantics
      (ListLib.sum a) need (CakeSum (sublist lc (rc + 1) c)) Htotal Hneed));
     unfold CakeSum, ListLib.sum in *; lia).
  all: unfold OrderedBy, BoundLeft, BoundRight, CakeOrder in Hordered.
  all: destruct Hordered as (_ & Ho12 & Ho23).
  all: unfold Znth in Ho12, Ho23; simpl in Ho12, Ho23.
  all: cbn [Pos.to_nat] in *.
  - eapply (greedy_terminal_exclusion_chain__try_terminal_semantics
      a b c need n (nth 0 right 0) pos acc la ra lb rb lc rc); try eassumption; try lia;
      try (intros k Hk; first [apply Hna | apply Hnb | apply Hnc]; lia).
    + intros q Hq. specialize (Hfmin q ltac:(lia)). replace (nth 0 left 0 - 1) with 0 in Hfmin by lia. exact Hfmin.
    + intros q Hq. specialize (Hsmin q ltac:(lia)). replace (nth (Pos.to_nat 1) left 0 - 1) with (nth 0 right 0) in Hsmin by lia. exact Hsmin.
  - eapply (greedy_terminal_exclusion_chain__try_terminal_semantics
      a c b need n (nth 0 right 0) pos acc la ra lc rc lb rb); try eassumption; try lia;
      try (intros k Hk; first [apply Hna | apply Hnb | apply Hnc]; lia).
    + intros q Hq. specialize (Hfmin q ltac:(lia)). replace (nth 0 left 0 - 1) with 0 in Hfmin by lia. exact Hfmin.
    + intros q Hq. specialize (Hsmin q ltac:(lia)). replace (nth (Pos.to_nat 2) left 0 - 1) with (nth 0 right 0) in Hsmin by lia. exact Hsmin.
  - eapply (greedy_terminal_exclusion_chain__try_terminal_semantics
      b a c need n (nth (Pos.to_nat 1) right 0) pos acc lb rb la ra lc rc); try eassumption; try lia;
      try (intros k Hk; first [apply Hna | apply Hnb | apply Hnc]; lia).
    + intros q Hq. specialize (Hfmin q ltac:(lia)). replace (nth (Pos.to_nat 1) left 0 - 1) with 0 in Hfmin by lia. exact Hfmin.
    + intros q Hq. specialize (Hsmin q ltac:(lia)). replace (nth 0 left 0 - 1) with (nth (Pos.to_nat 1) right 0) in Hsmin by lia. exact Hsmin.
  - eapply (greedy_terminal_exclusion_chain__try_terminal_semantics
      b c a need n (nth (Pos.to_nat 1) right 0) pos acc lb rb lc rc la ra); try eassumption; try lia;
      try (intros k Hk; first [apply Hna | apply Hnb | apply Hnc]; lia).
    + intros q Hq. specialize (Hfmin q ltac:(lia)). replace (nth (Pos.to_nat 1) left 0 - 1) with 0 in Hfmin by lia. exact Hfmin.
    + intros q Hq. specialize (Hsmin q ltac:(lia)). replace (nth (Pos.to_nat 2) left 0 - 1) with (nth (Pos.to_nat 1) right 0) in Hsmin by lia. exact Hsmin.
  - eapply (greedy_terminal_exclusion_chain__try_terminal_semantics
      c a b need n (nth (Pos.to_nat 2) right 0) pos acc lc rc la ra lb rb); try eassumption; try lia;
      try (intros k Hk; first [apply Hna | apply Hnb | apply Hnc]; lia).
    + intros q Hq. specialize (Hfmin q ltac:(lia)). replace (nth (Pos.to_nat 2) left 0 - 1) with 0 in Hfmin by lia. exact Hfmin.
    + intros q Hq. specialize (Hsmin q ltac:(lia)). replace (nth 0 left 0 - 1) with (nth (Pos.to_nat 2) right 0) in Hsmin by lia. exact Hsmin.
  - eapply (greedy_terminal_exclusion_chain__try_terminal_semantics
      c b a need n (nth (Pos.to_nat 2) right 0) pos acc lc rc lb rb la ra); try eassumption; try lia;
      try (intros k Hk; first [apply Hna | apply Hnb | apply Hnc]; lia).
    + intros q Hq. specialize (Hfmin q ltac:(lia)). replace (nth (Pos.to_nat 2) left 0 - 1) with 0 in Hfmin by lia. exact Hfmin.
    + intros q Hq. specialize (Hsmin q ltac:(lia)). replace (nth (Pos.to_nat 1) left 0 - 1) with (nth (Pos.to_nat 2) right 0) in Hsmin by lia. exact Hsmin.
Qed.
Lemma greedy_terminal_try_order__try_terminal_semantics :
  forall a b c ord need n pos who acc left right,
    Pre a b c ->
    (forall row col,
      ((0 <= row < 3 /\ 0 <= col) /\ col < Zlength a) ->
      1 <= Znth col (Znth row (a :: b :: c :: nil) nil) 0 <= 1000000) ->
    n = Zlength a ->
    need = (ListLib.sum a + 2) / 3 ->
    CakeOrder ord ->
    who = Znth 2 ord 0 ->
    GreedyRawState (a :: b :: c :: nil) ord need 2 pos left right ->
    SuffixSumState (a :: b :: c :: nil) who pos n acc ->
    (acc < need -> TryOrderSpec a b c ord None) /\
    (need <= acc ->
      TryOrderSpec a b c ord
        (Some (OutputBounds (replace_Znth who (pos + 1) left)
                            (replace_Znth who n right)))).
Proof.
  intros a b c ord need n pos who acc left right
    Hpre Hvalues Hn Hneed Hord Hwho Hgreedy Hsuffix.
  split; intro Hcmp.
  - eapply greedy_terminal_failure__try_terminal_semantics; eauto.
  - eapply greedy_terminal_success__try_terminal_semantics; eauto.
Qed.
Lemma suffix_sum_empty__try_terminal_semantics :
  forall rows who pos,
    0 <= pos ->
    pos <= Zlength (Znth who rows nil) ->
    SuffixSumState rows who pos pos 0.
Proof.
  intros rows who pos Hpos Hlen.
  unfold SuffixSumState, CakeSum.
  rewrite Zsublist_nil by lia.
  repeat split; simpl; lia.
Qed.
Lemma selected_row_length__try_terminal_semantics :
  forall (a b c ord : list Z) (who : Z),
    CakeOrder ord ->
    who = Znth 2 ord 0 ->
    Zlength b = Zlength a ->
    Zlength c = Zlength a ->
    Zlength (Znth who (a :: b :: c :: nil) nil) = Zlength a.
Proof.
  intros a b c ord who Hord Hwho Hlenb Hlenc.
  destruct Hord as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  all: repeat rewrite Znth_cons in Hwho by lia.
  all: repeat rewrite Znth0_cons in Hwho.
  all: subst who.
  - change (Zlength c = Zlength a). lia.
  - change (Zlength b = Zlength a). lia.
  - change (Zlength c = Zlength a). lia.
  - change (Zlength a = Zlength a). lia.
  - change (Zlength b = Zlength a). lia.
  - change (Zlength a = Zlength a). lia.
Qed.
Lemma suffix_sum_extend__try_terminal_semantics :
  forall rows who start i acc,
    SuffixSumState rows who start i acc ->
    i < Zlength (Znth who rows nil) ->
    SuffixSumState rows who start (i + 1)
      (acc + Znth i (Znth who rows nil) 0).
Proof.
  intros rows who start i acc Hstate Hi.
  unfold SuffixSumState in *.
  destruct Hstate as (Hstart & Hsi & Hibound & Hacc).
  repeat split; try lia.
  unfold CakeSum in *.
  rewrite (sublist_split start (i + 1) i) by lia.
  rewrite ListLib.sum_app.
  rewrite (sublist_single i i) by lia.
  simpl.
  rewrite (Znth_indep (Znth who rows nil) i i 0) by lia.
  unfold ListLib.sum.
  rewrite <- Hacc. lia.
Qed.
Lemma sum_upper_pointwise__try_terminal_semantics :
  forall xs b,
    (forall k, 0 <= k < Zlength xs -> Znth k xs 0 <= b) ->
    ListLib.sum xs <= Zlength xs * b.
Proof.
  intros xs b Hupper.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - pose proof (Zlength_nonneg xs) as Hlen.
    assert (Hx : x <= b).
    { specialize (Hupper 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Hupper. exact Hupper. }
    assert (Htail : forall k, 0 <= k < Zlength xs -> Znth k xs 0 <= b).
    { intros k Hk. specialize (Hupper (k + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Hupper by lia.
      replace (k + 1 - 1) with k in Hupper by lia. exact Hupper. }
    specialize (IH Htail).
    rewrite Zlength_cons. lia.
Qed.
Lemma suffix_sum_upper__try_terminal_semantics :
  forall rows who start i acc,
    SuffixSumState rows who start i acc ->
    let row := Znth who rows nil in
    i < Zlength row ->
    (forall k, 0 <= k < Zlength row -> 0 <= Znth k row 0 <= 1000000) ->
    Zlength row <= 200000 ->
    acc + Znth i row 0 <= 200000000000.
Proof.
  intros rows who start i acc Hstate.
  cbn zeta.
  intros Hi Hvalues Hlen.
  set (row := Znth who rows nil) in *.
  unfold SuffixSumState in Hstate.
  destruct Hstate as (Hstart & Hsi & Hibound & Hacc).
  pose proof (sum_sublist_inclusion__try_terminal_semantics
    row 0 start (i + 1) (Zlength row)
    ltac:(intros; specialize (Hvalues k H); lia)
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hinclusion.
  rewrite sublist_full__try_terminal_semantics in Hinclusion.
  pose proof (sum_upper_pointwise__try_terminal_semantics row 1000000
    ltac:(intros; specialize (Hvalues k H); lia)) as Htotal.
  unfold CakeSum in Hacc.
  rewrite (sublist_split start (i + 1) i) in Hinclusion by lia.
  rewrite ListLib.sum_app in Hinclusion.
  rewrite (sublist_single i i) in Hinclusion by lia.
  simpl in Hinclusion.
  rewrite (Znth_indep row i i 0) in Hinclusion by lia.
  subst acc.
  unfold ListLib.sum in Hinclusion, Htotal.
  change (fold_right Z.add 0 (sublist start i row) + Znth i row 0 <=
          200000000000).
  nia.
Qed.
Lemma Znth_app_left__try_output_materialization :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__try_output_materialization :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma bounded_values_sum_lower__solver_order_setup :
  forall xs,
    Forall (fun x => 1 <= x <= 1000000) xs ->
    Zlength xs <= CakeSum xs.
Proof.
  intros xs Hxs.
  induction Hxs as [|x xs Hx Hxs IH].
  - reflexivity.
  - unfold CakeSum in *.
    rewrite Zlength_cons.
    simpl.
    lia.
Qed.
Lemma order_table_decomposition__solver_order_setup :
  forall table z,
    OrderTable table ->
    0 <= z < 6 ->
    table = sublist 0 (3 * z) table ++
            OrderFor z ++ sublist (3 * (z + 1)) 18 table /\
    Zlength (sublist 0 (3 * z) table) = 3 * z /\
    Zlength (OrderFor z) = 3 /\
    Zlength (sublist (3 * (z + 1)) 18 table) = 18 - 3 * (z + 1) /\
    OrderAt z (OrderFor z) /\
    CakeOrder (OrderFor z) /\
    sublist (3 * z) (3 * (z + 1)) table = OrderFor z /\
    sublist 0 (3 * (z + 1) - 3 * z) (sublist (3 * z) 18 table) =
      OrderFor z /\
    sublist (3 * (z + 1) - 3 * z) (18 - 3 * z)
      (sublist (3 * z) 18 table) =
      sublist (3 * (z + 1)) 18 table.
Proof.
  intros table z Htable Hz.
  unfold OrderTable in Htable.
  subst table.
  assert (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5) as
      [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia.
  all: cbv; tauto.
Qed.
Lemma Forall_Znth__solver_order_iteration {A : Type}
    (P : A -> Prop) (d : A) (l : list A) :
  Forall P l <-> (forall i, 0 <= i < Zlength l -> P (Znth i l d)).
Proof.
  apply Forall_Znth.
Qed.
Lemma failed_six_orders_spec_none__solver_final_results :
  forall a b c,
    FailedOrders a b c 6 ->
    Spec a b c None.
Proof.
  intros a b c Hfailed.
  unfold Spec.
  right.
  split; [reflexivity |].
  intros bounds Hvalid.
  pose proof Hvalid as Hvalid_copy.
  destruct Hvalid as
      (la & ra & lb & rb & lc & rc & total & Hbounds & Htotal &
       Hla & Hra & Hlb & Hrb & Hlc & Hrc & Hab & Hac & Hbc &
       Hsa & Hsb & Hsc).
  subst bounds.
  unfold DisjointIntervals in Hab, Hac, Hbc.
  destruct Hab as [Hab | Hab];
    destruct Hac as [Hac | Hac];
    destruct Hbc as [Hbc | Hbc].
  - destruct (Hfailed 0 ltac:(lia)) as (ord & Hord & Hno).
    assert (ord = [0; 1; 2]) as -> by
        (unfold OrderAt in Hord; intuition lia).
    cbn [TryOrderSpec] in Hno.
    apply (Hno [la; ra; lb; rb; lc; rc] Hvalid_copy).
    unfold OrderedBy.
    split.
    + unfold CakeOrder; tauto.
    + cbn [BoundRight BoundLeft Znth]; tauto.
  - destruct (Hfailed 1 ltac:(lia)) as (ord & Hord & Hno).
    assert (ord = [0; 2; 1]) as -> by
        (unfold OrderAt in Hord; intuition lia).
    cbn [TryOrderSpec] in Hno.
    apply (Hno [la; ra; lb; rb; lc; rc] Hvalid_copy).
    unfold OrderedBy.
    split.
    + unfold CakeOrder; tauto.
    + cbn [BoundRight BoundLeft Znth]; tauto.
  - lia.
  - destruct (Hfailed 4 ltac:(lia)) as (ord & Hord & Hno).
    assert (ord = [2; 0; 1]) as -> by
        (unfold OrderAt in Hord; intuition lia).
    cbn [TryOrderSpec] in Hno.
    apply (Hno [la; ra; lb; rb; lc; rc] Hvalid_copy).
    unfold OrderedBy.
    split.
    + unfold CakeOrder; tauto.
    + cbn [BoundRight BoundLeft Znth]; tauto.
  - destruct (Hfailed 2 ltac:(lia)) as (ord & Hord & Hno).
    assert (ord = [1; 0; 2]) as -> by
        (unfold OrderAt in Hord; intuition lia).
    cbn [TryOrderSpec] in Hno.
    apply (Hno [la; ra; lb; rb; lc; rc] Hvalid_copy).
    unfold OrderedBy.
    split.
    + unfold CakeOrder; tauto.
    + cbn [BoundRight BoundLeft Znth]; tauto.
  - lia.
  - destruct (Hfailed 3 ltac:(lia)) as (ord & Hord & Hno).
    assert (ord = [1; 2; 0]) as -> by
        (unfold OrderAt in Hord; intuition lia).
    cbn [TryOrderSpec] in Hno.
    apply (Hno [la; ra; lb; rb; lc; rc] Hvalid_copy).
    unfold OrderedBy.
    split.
    + unfold CakeOrder; tauto.
    + cbn [BoundRight BoundLeft Znth]; tauto.
  - destruct (Hfailed 5 ltac:(lia)) as (ord & Hord & Hno).
    assert (ord = [2; 1; 0]) as -> by
        (unfold OrderAt in Hord; intuition lia).
    cbn [TryOrderSpec] in Hno.
    apply (Hno [la; ra; lb; rb; lc; rc] Hvalid_copy).
    unfold OrderedBy.
    split.
    + unfold CakeOrder; tauto.
    + cbn [BoundRight BoundLeft Znth]; tauto.
Qed.
