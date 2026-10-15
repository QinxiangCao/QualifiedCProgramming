Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.Presuffix.

Import ListNotations.
Local Open Scope Z_scope.

Definition AdjacentSwap (a b:list Z) : Prop :=
  exists i,0 <= i < Zlength a - 1 /\
    b=replace_Znth(i+1)(Znth i a 0)(replace_Znth i (Znth(i+1)a 0)a).
Definition SwapReach (a b:list Z) (k:Z) : Prop :=
  exists st:list(list Z),1 <= Zlength st <= k + 1 /\ Znth 0 st[] = a /\
    Znth(Zlength st - 1) st[] = b /\
    forall i,0 <= i < Zlength st - 1 -> AdjacentSwap(Znth i st[])(Znth(i + 1) st[]).
Definition Pre (digits:list Z) (k:Z) : Prop :=
  (* This legacy Pre is unused; the P039 solver Require states its byte-level
     input constraints directly.  The original clauses are preserved here:
       1 <= Zlength digits <= 19 /\ 0 <= k <= 100 /\
       Znth 0 digits 0 <> 0 /\ Forall (fun d => 0 <= d <= 9) digits. *)
  True.
Definition Spec (digits:list Z) (k:Z) (out:list Z) : Prop :=
  SwapReach digits out k /\ forall q,SwapReach digits q k->(q = out \/ ((exists i, 0 <= i < Z.min (Zlength q) (Zlength out) /\
    (forall j, 0 <= j < i -> Znth j q 0 = Znth j out 0) /\
    Znth i q 0 < Znth i out 0) \/
  (Zlength q < Zlength out /\ is_prefix q out))).

(* Lexicographic comparison, stated independently of any implementation. *)
Definition LexLe (a b : list Z) : Prop :=
  a = b \/
  (exists i,
      0 <= i < Z.min (Zlength a) (Zlength b) /\
      (forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0) /\
      Znth i a 0 < Znth i b 0) \/
  (Zlength a < Zlength b /\ is_prefix a b).

Definition PrefixEq (a b : list Z) (i : Z) : Prop :=
  Zlength a = Zlength b /\
  0 <= i <= Zlength a /\
  forall j, 0 <= j < i -> Znth j a 0 = Znth j b 0.

(* The first [pos] digits are already globally optimal.  Every competitor is
   either lexicographically no larger, or agrees on that prefix and remains
   attainable from the current suffix using the unspent budget. *)
Definition GreedyProgress
    (input : list Z) (budget : Z) (current : list Z)
    (pos remaining : Z) : Prop :=
  Zlength current = Zlength input /\
  0 <= pos <= Zlength input /\
  0 <= remaining <= budget /\
  SwapReach input current (budget - remaining) /\
  forall q, SwapReach input q budget ->
    LexLe q current \/
    (PrefixEq q current pos /\ SwapReach current q remaining).

(* [best] is the leftmost maximum of the inspected interval [lo, hi). *)
Definition FirstMaximumPrefix
    (l : list Z) (lo hi best : Z) : Prop :=
  0 <= lo < hi /\ hi <= Zlength l /\ lo <= best < hi /\
  (forall p, lo <= p < hi -> Znth p l 0 <= Znth best l 0) /\
  (forall p, lo <= p < best -> Znth p l 0 < Znth best l 0).

(* The final scan interval consists precisely of positions reachable with the
   remaining adjacent-swap budget. *)
Definition ReachableFirstMaximum
    (l : list Z) (pos remaining best : Z) : Prop :=
  FirstMaximumPrefix l pos (Z.min (Zlength l) (pos + remaining + 1)) best.

(* Move one list element left while preserving the relative order of all
   other elements.  This is the mathematical effect of any implementation of
   that rearrangement, not an encoding of the C loop. *)
Definition move_left (l : list Z) (from to : Z) : list Z :=
  sublist 0 to l ++
  [Znth from l 0] ++
  sublist to from l ++
  sublist (from + 1) (Zlength l) l.

(* A selected leftmost maximum is an exchange point when moving it to [pos]
   cannot make an already smaller competitor larger, and every competitor
   still tied on the processed prefix has a residual path after the movement
   cost is subtracted.  This is the semantic fact needed between selection
   and the concrete bubbling implementation. *)
Definition GreedyExchangeClosure
    (current : list Z) (pos remaining best : Z) : Prop :=
  let moved := move_left current best pos in
  let residual := remaining - (best - pos) in
  (forall q, LexLe q current -> LexLe q moved) /\
  (forall q,
      PrefixEq q current pos ->
      SwapReach current q remaining ->
      LexLe q moved \/
      (PrefixEq q moved (pos + 1) /\ SwapReach moved q residual)).

Require Import Coq.micromega.Lia.

Lemma GreedyExchangeClosure_preserves_smaller :
  forall current pos remaining best q,
    GreedyExchangeClosure current pos remaining best ->
    LexLe q current ->
    LexLe q (move_left current best pos).
Proof.
  intros current pos remaining best q Hclosure Hle.
  unfold GreedyExchangeClosure in Hclosure.
  destruct Hclosure as [Hsmaller _].
  exact (Hsmaller q Hle).
Qed.

Lemma GreedyExchangeClosure_residual_path :
  forall current pos remaining best q,
    GreedyExchangeClosure current pos remaining best ->
    PrefixEq q current pos ->
    SwapReach current q remaining ->
    LexLe q (move_left current best pos) \/
    (PrefixEq q (move_left current best pos) (pos + 1) /\
     SwapReach (move_left current best pos) q
       (remaining - (best - pos))).
Proof.
  intros current pos remaining best q Hclosure Hprefix Hreach.
  unfold GreedyExchangeClosure in Hclosure.
  destruct Hclosure as [_ Hresidual].
  exact (Hresidual q Hprefix Hreach).
Qed.

(* The closure is deliberately separate from [GreedyProgress]: the former is
   the budget-subtractive exchange principle at one selected position, while
   the latter remains the stable outer-loop invariant. *)
Lemma GreedyExchangeClosure_preserves_progress :
  forall input budget current pos remaining best,
    ReachableFirstMaximum current pos remaining best ->
    GreedyProgress input budget current pos remaining ->
    GreedyExchangeClosure current pos remaining best ->
    Zlength (move_left current best pos) = Zlength current ->
    SwapReach input (move_left current best pos)
      (budget - (remaining - (best - pos))) ->
    GreedyProgress input budget (move_left current best pos) (pos + 1)
      (remaining - (best - pos)).
Proof.
  intros input budget current pos remaining best Hmax Hprogress Hexchange
    Hlength Hreach.
  unfold ReachableFirstMaximum, FirstMaximumPrefix in Hmax.
  destruct Hmax as [[Hpos0 Hposhi] [Hhile [Hbest_bounds _]]].
  unfold GreedyProgress in Hprogress.
  destruct Hprogress as
    [Hcurrent_length [Hpos_bounds [Hremaining_bounds [_ Hcompetitors]]]].
  unfold GreedyExchangeClosure in Hexchange.
  destruct Hexchange as [Hsmaller Hresidual].
  destruct Hbest_bounds as [Hposbest Hbesthi].
  apply Z.min_glb_lt_iff in Hbesthi.
  destruct Hbesthi as [Hbestlen Hbestbudget].
  unfold GreedyProgress.
  repeat split.
  - rewrite Hlength. exact Hcurrent_length.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hreach.
  - intros q Hq.
    specialize (Hcompetitors q Hq).
    destruct Hcompetitors as [Hqsmaller | [Hqprefix Hqreach]].
    + left. apply Hsmaller. exact Hqsmaller.
    + exact (Hresidual q Hqprefix Hqreach).
Qed.

(* Exchange readiness belongs to the state at the start of a greedy phase,
   rather than being manufactured by either scan-exit branch.  It quantifies
   over the mathematical result of the bounded maximum selection, so the
   concrete scan may refine [best] without changing this fact. *)
Definition GreedySelectionReady
    (current : list Z) (pos remaining : Z) : Prop :=
  forall best,
    ReachableFirstMaximum current pos remaining best ->
    GreedyExchangeClosure current pos remaining best.

Lemma GreedySelectionReady_specialize :
  forall current pos remaining best,
    GreedySelectionReady current pos remaining ->
    ReachableFirstMaximum current pos remaining best ->
    GreedyExchangeClosure current pos remaining best.
Proof.
  intros current pos remaining best Hready Hbest.
  exact (Hready best Hbest).
Qed.

Lemma GreedySelectionReady_scan_stable :
  forall current pos remaining scanned best,
    GreedySelectionReady current pos remaining ->
    FirstMaximumPrefix current pos scanned best ->
    GreedySelectionReady current pos remaining.
Proof.
  intros current pos remaining scanned best Hready _.
  exact Hready.
Qed.

(* A duplicate-safe, implementation-independent account of adjacent
   transpositions.  [FirstRemove x source p rest] selects the first occurrence
   of [x], records its zero-based position [p], and removes it.  Repeating this
   operation in target order gives the canonical stable-occurrence matching. *)
Inductive AdjacentSwapList : list Z -> list Z -> Prop :=
| ASL_here : forall x y tail,
    AdjacentSwapList (x :: y :: tail) (y :: x :: tail)
| ASL_cons : forall h left right,
    AdjacentSwapList left right ->
    AdjacentSwapList (h :: left) (h :: right).

Lemma AdjacentSwapList_symmetric :
  forall left right,
    AdjacentSwapList left right -> AdjacentSwapList right left.
Proof.
  intros left right Hswap.
  induction Hswap.
  - constructor.
  - constructor. exact IHHswap.
Qed.

Inductive FirstRemove (x : Z) : list Z -> nat -> list Z -> Prop :=
| FirstRemove_here : forall tail,
    FirstRemove x (x :: tail) 0%nat tail
| FirstRemove_later : forall y tail p rest,
    x <> y ->
    FirstRemove x tail p rest ->
    FirstRemove x (y :: tail) (S p) (y :: rest).

(* A single adjacent transposition has exactly one of two effects on stable
   first removal: it crosses the selected occurrence (changing its position
   by at most one and leaving the residual list fixed), or it remains as one
   adjacent transposition in the residual list. *)
Lemma FirstRemove_adjacent_transport :
  forall left right,
    AdjacentSwapList left right ->
    forall x p rest,
      FirstRemove x left p rest ->
      exists p' rest',
        FirstRemove x right p' rest' /\
        ((rest' = rest /\ (p' <= S p)%nat) \/
         (p' = p /\ AdjacentSwapList rest rest')).
Proof.
  intros left right Hswap.
  induction Hswap as [u v tail | h left right Hswap IH];
    intros x p rest Hremove.
  - inversion Hremove as [tail0 | y tail0 p0 rest0 Hxy Htail]; subst.
    + destruct (Z.eq_dec u v) as [Hxv | Hxv].
      * subst v.
        exists 0%nat, (u :: tail).
        split; [constructor |].
        left. split; [reflexivity | lia].
      * exists 1%nat, (v :: tail).
        split.
        -- constructor; [exact Hxv | constructor].
        -- left. split; [reflexivity | lia].
    + inversion Htail as [tail1 | y1 tail1 p1 rest1 Hxy1 Htail1]; subst.
      * exists 0%nat, (u :: rest0).
        split; [constructor |].
        left. split; [reflexivity | lia].
      * exists (S (S p1)), (v :: u :: rest1).
        split.
        -- constructor; [exact Hxy1 |].
           constructor; [exact Hxy | exact Htail1].
        -- right. split; [reflexivity | constructor].
  - inversion Hremove as [tail0 | y tail0 p0 rest0 Hxy Htail]; subst.
    + exists 0%nat, right.
      split; [constructor |].
      right. split; [reflexivity | exact Hswap].
    + destruct (IH x p0 rest0 Htail) as
          [p' [rest' [Hremove' [[Hrest Hbound] | [Hp Hrestswap]]]]].
      * exists (S p'), (h :: rest0).
        split.
        -- constructor; [exact Hxy |].
           rewrite <- Hrest. exact Hremove'.
        -- left. split; [reflexivity | lia].
      * exists (S p'), (h :: rest').
        split.
        -- constructor; [exact Hxy | exact Hremove'].
        -- right. split; [now f_equal | constructor; exact Hrestswap].
Qed.

Fixpoint CanonicalRemovalCost
    (source target : list Z) (cost : nat) : Prop :=
  match target with
  | [] => source = [] /\ cost = 0%nat
  | x :: target_tail =>
      exists p source_rest tail_cost,
        FirstRemove x source p source_rest /\
        CanonicalRemovalCost source_rest target_tail tail_cost /\
        cost = (p + tail_cost)%nat
  end.

Lemma CanonicalRemovalCost_refl :
  forall values, CanonicalRemovalCost values values 0%nat.
Proof.
  induction values as [|x tail IH]; simpl.
  - auto.
  - exists 0%nat, tail, 0%nat.
    repeat split; auto using FirstRemove_here.
Qed.

(* The key duplicate-safe one-step estimate.  Stable occurrence ranks make an
   equal-value swap observationally free; an unequal swap changes the
   canonical removal cost by at most one. *)
Lemma CanonicalRemovalCost_adjacent_lipschitz :
  forall target left right cost,
    AdjacentSwapList left right ->
    CanonicalRemovalCost left target cost ->
    exists cost',
      CanonicalRemovalCost right target cost' /\
      (cost' <= S cost)%nat.
Proof.
  induction target as [|x target_tail IH];
    intros left right cost Hswap Hcost.
  - simpl in Hcost.
    destruct Hcost as [Hleft _]. subst left. inversion Hswap.
  - simpl in Hcost.
    destruct Hcost as
      [p [source_rest [tail_cost [Hremove [Htailcost Hcost]]]]].
    destruct (FirstRemove_adjacent_transport
                left right Hswap x p source_rest Hremove) as
      [p' [rest' [Hremove' [[Hrest Hbound] | [Hp Hrestswap]]]]].
    + subst rest'.
      exists (p' + tail_cost)%nat.
      split.
      * simpl. exists p', source_rest, tail_cost. auto.
      * lia.
    + subst p'.
      destruct (IH source_rest rest' tail_cost Hrestswap Htailcost)
        as [tail_cost' [Htailcost' Htailbound]].
      exists (p + tail_cost')%nat.
      split.
      * simpl. exists p, rest', tail_cost'. auto.
      * lia.
Qed.

Lemma AdjacentSwapList_context :
  forall prefix x y suffix,
    AdjacentSwapList
      (prefix ++ x :: y :: suffix)
      (prefix ++ y :: x :: suffix).
Proof.
  induction prefix as [|h prefix IH]; intros x y suffix; simpl.
  - constructor.
  - constructor. apply IH.
Qed.

Lemma replace_Znth_adjacent_form :
  forall (prefix : list Z) x y suffix,
    replace_Znth (Zlength prefix + 1) x
      (replace_Znth (Zlength prefix) y
        (prefix ++ x :: y :: suffix)) =
    prefix ++ y :: x :: suffix.
Proof.
  intros prefix x y suffix.
  rewrite replace_Znth_app_r with
      (l1 := prefix) (l2 := (x :: y :: suffix)) by lia.
  rewrite (replace_Znth_nothing (A := Z)
      (Zlength prefix) prefix y) by lia.
  replace (Zlength prefix - Zlength prefix) with 0 by lia.
  simpl.
  rewrite replace_Znth_app_r with
      (l1 := prefix) (l2 := (y :: y :: suffix)) by lia.
  rewrite (replace_Znth_nothing (A := Z)
      (Zlength prefix + 1) prefix x) by lia.
  replace (Zlength prefix + 1 - Zlength prefix) with 1 by lia.
  simpl. reflexivity.
Qed.

Lemma AdjacentSwap_to_AdjacentSwapList :
  forall left right,
    AdjacentSwap left right -> AdjacentSwapList left right.
Proof.
  intros left right [i [[Hi Hnext] Hright]].
  remember (Znth i left 0) as x.
  remember (Znth (i + 1) left 0) as y.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat ((i + 1) - i - 1)).
  set (prefix := firstn ni left).
  set (after_i := skipn (S ni) left).
  set (middle := firstn nj after_i).
  set (suffix := skipn (S nj) after_i).
  assert (Hsplit_i : left = prefix ++ x :: after_i).
  {
    subst prefix after_i ni.
    rewrite (firstn_skipSn 0 (Z.to_nat i) left) at 1.
    2:{ rewrite Zlength_correct in Hnext. lia. }
    rewrite Heqx. reflexivity.
  }
  assert (Hnext_after : (nj < length after_i)%nat).
  {
    subst nj after_i ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hnext.
    lia.
  }
  assert (Hsplit_next : after_i = middle ++ y :: suffix).
  {
    subst middle suffix.
    rewrite (firstn_skipSn 0 nj after_i) at 1 by exact Hnext_after.
    replace y with (nth nj after_i 0).
    2:{
      subst nj after_i ni.
      rewrite Heqy.
      unfold Znth.
      rewrite nth_skipn.
      replace
        (S (Z.to_nat i) + Z.to_nat ((i + 1) - i - 1))%nat
        with (Z.to_nat (i + 1)) by lia.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hmiddle : middle = []).
  {
    subst middle nj.
    replace (Z.to_nat (i + 1 - i - 1)) with 0%nat by lia.
    reflexivity.
  }
  rewrite Hsplit_next in Hsplit_i.
  rewrite Hmiddle in Hsplit_i.
  simpl in Hsplit_i.
  assert (Hi_prefix : i = Zlength prefix).
  {
    subst prefix ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hnext.
    rewrite Nat.min_l by lia.
    lia.
  }
  rewrite Hsplit_i in Hright.
  rewrite Hi_prefix in Hright.
  rewrite replace_Znth_adjacent_form in Hright.
  subst right.
  rewrite Hsplit_i.
  apply AdjacentSwapList_context.
Qed.

Inductive AdjacentSwapChain : list (list Z) -> Prop :=
| ASC_one : forall state,
    AdjacentSwapChain [state]
| ASC_cons : forall left right tail,
    AdjacentSwap left right ->
    AdjacentSwapChain (right :: tail) ->
    AdjacentSwapChain (left :: right :: tail).

Lemma AdjacentSwapChain_canonical_cost :
  forall states,
    AdjacentSwapChain states ->
    exists cost,
      CanonicalRemovalCost (hd [] states) (last states []) cost /\
      (cost <= length states - 1)%nat.
Proof.
  intros states Hchain.
  induction Hchain as [state | left right tail Hswap Hchain IH].
  - exists 0%nat. simpl.
    split; [apply CanonicalRemovalCost_refl | lia].
  - destruct IH as [cost [Hcost Hbound]].
    pose proof (AdjacentSwap_to_AdjacentSwapList _ _ Hswap) as Hclean.
    pose proof (AdjacentSwapList_symmetric _ _ Hclean) as Hclean_rev.
    destruct (CanonicalRemovalCost_adjacent_lipschitz
                (last (right :: tail) []) right left cost
                Hclean_rev Hcost) as [cost' [Hcost' Hstep]].
    exists cost'.
    split.
    + change (CanonicalRemovalCost left (last (right :: tail) []) cost').
      exact Hcost'.
    + simpl in *. lia.
Qed.

Lemma indexed_adjacent_steps_form_chain :
  forall states,
    1 <= Zlength states ->
    (forall i,
      0 <= i < Zlength states - 1 ->
      AdjacentSwap (Znth i states []) (Znth (i + 1) states [])) ->
    AdjacentSwapChain states.
Proof.
  induction states as [|a states IH]; intros Hlength Hsteps.
  - rewrite Zlength_nil in Hlength. lia.
  - destruct states as [|b tail].
    + constructor.
    + apply ASC_cons.
      * specialize (Hsteps 0).
        assert (Hrange : 0 <= 0 < Zlength (a :: b :: tail) - 1).
        { repeat rewrite Zlength_cons. pose proof (Zlength_nonneg tail). lia. }
        specialize (Hsteps Hrange).
        simpl in Hsteps.
        exact Hsteps.
      * apply IH.
        -- rewrite Zlength_cons. pose proof (Zlength_nonneg tail). lia.
        -- intros i Hi.
           specialize (Hsteps (i + 1)).
           assert (Hrange :
             0 <= i + 1 < Zlength (a :: b :: tail) - 1).
           {
             repeat rewrite Zlength_cons.
             rewrite Zlength_cons in Hi.
             lia.
           }
           specialize (Hsteps Hrange).
           unfold Znth in Hsteps |- *.
           replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hsteps
             by lia.
           replace (Z.to_nat (i + 1 + 1)) with
               (S (Z.to_nat (i + 1))) in Hsteps by lia.
           simpl in Hsteps.
           exact Hsteps.
Qed.

Lemma nth_last_default_local :
  forall (A : Type) (values : list A) i d,
    values <> [] ->
    i = (length values - 1)%nat ->
    nth i values d = last values d.
Proof.
  intros A values.
  induction values as [|x tail IH]; intros i d Hnonempty Hi.
  - contradiction.
  - destruct tail as [|y tail].
    + simpl in *. subst i. reflexivity.
    + simpl in *.
      destruct i as [|i].
      * lia.
      * apply IH; [discriminate | lia].
Qed.

Lemma SwapReach_canonical_lower_bound :
  forall source target budget,
    SwapReach source target budget ->
    exists cost,
      CanonicalRemovalCost source target cost /\
      Z.of_nat cost <= budget.
Proof.
  intros source target budget
    [states [Hlength [Hfirst [Hlast Hsteps]]]].
  assert (Hnonempty : states <> []).
  { intro Hnil. subst states. rewrite Zlength_nil in Hlength. lia. }
  pose proof (indexed_adjacent_steps_form_chain states
                ltac:(lia) Hsteps) as Hchain.
  destruct (AdjacentSwapChain_canonical_cost states Hchain)
    as [cost [Hcost Hcost_bound]].
  assert (Hhd : hd [] states = source).
  {
    destruct states as [|head tail]; [contradiction |].
    simpl in Hfirst |- *.
    exact Hfirst.
  }
  assert (Hlast' : last states [] = target).
  {
    unfold Znth in Hlast.
    rewrite Zlength_correct in Hlast.
    replace (Z.to_nat (Z.of_nat (length states) - 1)) with
        (length states - 1)%nat in Hlast by lia.
    rewrite nth_last_default_local in Hlast by auto.
    exact Hlast.
  }
  exists cost.
  split.
  - rewrite <- Hhd, <- Hlast'. exact Hcost.
  - rewrite Zlength_correct in Hlength.
    lia.
Qed.

Lemma AdjacentSwapList_to_AdjacentSwap :
  forall left right,
    AdjacentSwapList left right -> AdjacentSwap left right.
Proof.
  intros left right Hswap.
  induction Hswap as [x y tail | h left right Hswap IH].
  - exists 0.
    split.
    + rewrite !Zlength_cons. pose proof (Zlength_nonneg tail). lia.
    + reflexivity.
  - destruct IH as [i [[Hi Hbound] Hright]].
    exists (i + 1).
    split.
    + rewrite !Zlength_cons. lia.
    + rewrite !Znth_cons by lia.
      rewrite !replace_Znth_cons by lia.
      repeat replace (i + 1 - 1) with i by lia.
      repeat replace (i + 1 + 1 - 1) with (i + 1) by lia.
      f_equal. exact Hright.
Qed.

Inductive CanonicalSwapPath : list Z -> list Z -> nat -> Prop :=
| CSP_refl : forall state,
    CanonicalSwapPath state state 0%nat
| CSP_step : forall left middle right steps,
    AdjacentSwapList left middle ->
    CanonicalSwapPath middle right steps ->
    CanonicalSwapPath left right (S steps).

Lemma CanonicalSwapPath_trans :
  forall left middle right n m,
    CanonicalSwapPath left middle n ->
    CanonicalSwapPath middle right m ->
    CanonicalSwapPath left right (n + m)%nat.
Proof.
  intros left middle right n m Hfirst Hsecond.
  induction Hfirst.
  - simpl. exact Hsecond.
  - simpl. eapply CSP_step; eauto.
Qed.

Lemma CanonicalSwapPath_cons :
  forall h left right steps,
    CanonicalSwapPath left right steps ->
    CanonicalSwapPath (h :: left) (h :: right) steps.
Proof.
  intros h left right steps Hpath.
  induction Hpath.
  - constructor.
  - eapply CSP_step.
    + apply ASL_cons. exact H.
    + exact IHHpath.
Qed.

Lemma FirstRemove_construct_path :
  forall x source position rest,
    FirstRemove x source position rest ->
    CanonicalSwapPath source (x :: rest) position.
Proof.
  intros x source position rest Hremove.
  induction Hremove as
      [tail | y tail position rest Hxy Hremove IH].
  - constructor.
  - pose proof (CanonicalSwapPath_cons y _ _ _ IH) as Hlift.
    assert (Hcross :
      CanonicalSwapPath (y :: x :: rest) (x :: y :: rest) 1%nat).
    {
      eapply CSP_step with (middle := x :: y :: rest).
      - constructor.
      - constructor.
    }
    pose proof (CanonicalSwapPath_trans _ _ _ _ _ Hlift Hcross) as Hjoined.
    simpl in Hjoined.
    replace (position + 1)%nat with (S position) in Hjoined by lia.
    exact Hjoined.
Qed.

Lemma CanonicalRemovalCost_construct_path :
  forall target source cost,
    CanonicalRemovalCost source target cost ->
    CanonicalSwapPath source target cost.
Proof.
  induction target as [|x target_tail IH];
    intros source cost Hcost.
  - simpl in Hcost. destruct Hcost as [-> ->]. constructor.
  - simpl in Hcost.
    destruct Hcost as
      [position [rest [tail_cost [Hremove [Htailcost ->]]]]].
    pose proof (FirstRemove_construct_path _ _ _ _ Hremove) as Hfront.
    pose proof (IH _ _ Htailcost) as Htail.
    pose proof (CanonicalSwapPath_cons x _ _ _ Htail) as Hlift.
    exact (CanonicalSwapPath_trans _ _ _ _ _ Hfront Hlift).
Qed.

Lemma CanonicalSwapPath_states :
  forall source target steps,
    CanonicalSwapPath source target steps ->
    exists states,
      length states = S steps /\
      hd [] states = source /\
      last states [] = target /\
      forall i,
        0 <= i < Z.of_nat steps ->
        AdjacentSwap (Znth i states []) (Znth (i + 1) states []).
Proof.
  intros source target steps Hpath.
  induction Hpath as
      [state | left middle right steps Hswap Hpath IH].
  - exists [state]. simpl.
    repeat split; auto. intros i Hi. lia.
  - destruct IH as [states [Hlength [Hhead [Hlast Hsteps]]]].
    destruct states as [|head states].
    + simpl in Hlength. lia.
    + simpl in Hhead.
      exists (left :: head :: states).
      split.
      * simpl in Hlength |- *. lia.
      * split.
        -- reflexivity.
        -- split.
           ++ simpl. exact Hlast.
           ++ intros i Hi.
              destruct (Z.eq_dec i 0) as [-> | Hine].
              ** simpl. rewrite Hhead.
                 apply AdjacentSwapList_to_AdjacentSwap. exact Hswap.
              ** specialize (Hsteps (i - 1) ltac:(lia)).
                 unfold Znth in Hsteps |- *.
                 replace (Z.to_nat (i - 1 + 1)) with (Z.to_nat i) in Hsteps
                   by (f_equal; lia).
                 replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
                 replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
                 simpl.
                 exact Hsteps.
Qed.

Lemma CanonicalRemovalCost_sound :
  forall source target cost,
    CanonicalRemovalCost source target cost ->
    SwapReach source target (Z.of_nat cost).
Proof.
  intros source target cost Hcost.
  pose proof (CanonicalRemovalCost_construct_path _ _ _ Hcost) as Hpath.
  destruct (CanonicalSwapPath_states _ _ _ Hpath)
    as [states [Hlength [Hfirst [Hlast Hsteps]]]].
  exists states.
  repeat split.
  - rewrite Zlength_correct, Hlength. lia.
  - rewrite Zlength_correct, Hlength. lia.
  - destruct states as [|head tail]; [simpl in Hlength; lia |].
    simpl in Hfirst |- *. exact Hfirst.
  - unfold Znth.
    rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length states) - 1)) with
        (length states - 1)%nat by lia.
    rewrite nth_last_default_local.
    + exact Hlast.
    + intro Hnil. subst states. simpl in Hlength. lia.
    + reflexivity.
  - intros i Hi.
    apply Hsteps.
    rewrite Zlength_correct, Hlength in Hi.
    lia.
Qed.

(* Structural facts used to expose the compositional content of the stable
   removal cost.  They deliberately sit below the greedy predicates: the
   facts are about lists and stable occurrence matching, not about the C
   control flow. *)
Lemma FirstRemove_length :
  forall x source position rest,
    FirstRemove x source position rest ->
    length source = S (length rest).
Proof.
  intros x source position rest Hremove.
  induction Hremove; simpl; lia.
Qed.

Lemma FirstRemove_position_bound :
  forall x source position rest,
    FirstRemove x source position rest ->
    (position < length source)%nat.
Proof.
  intros x source position rest Hremove.
  induction Hremove; simpl; lia.
Qed.

Lemma FirstRemove_decompose :
  forall x source position rest,
    FirstRemove x source position rest ->
    exists prefix suffix,
      source = prefix ++ x :: suffix /\
      rest = prefix ++ suffix /\
      length prefix = position /\
      Forall (fun y => x <> y) prefix.
Proof.
  intros x source position rest Hremove.
  induction Hremove as
      [tail | y tail position rest Hxy Hremove IH].
  - exists [], tail. simpl. auto.
  - destruct IH as
        [prefix [suffix [Hsource [Hrest [Hlength Habsent]]]]].
    exists (y :: prefix), suffix. simpl.
    split.
    + rewrite Hsource. reflexivity.
    + split.
      * rewrite Hrest. reflexivity.
      * split.
        -- f_equal. exact Hlength.
        -- constructor; assumption.
Qed.

Lemma FirstRemove_app_absent :
  forall x prefix suffix,
    Forall (fun y => x <> y) prefix ->
    FirstRemove x (prefix ++ x :: suffix) (length prefix)
      (prefix ++ suffix).
Proof.
  intros x prefix.
  induction prefix as [|y prefix IH]; intros suffix Habsent; simpl.
  - constructor.
  - inversion Habsent; subst.
    constructor; auto.
Qed.

Lemma FirstRemove_functional :
  forall x source p1 rest1,
    FirstRemove x source p1 rest1 ->
    forall p2 rest2,
      FirstRemove x source p2 rest2 ->
      p1 = p2 /\ rest1 = rest2.
Proof.
  intros x source p1 rest1 Hfirst.
  induction Hfirst as
      [tail | y tail p1 rest1 Hxy Hfirst IH];
    intros p2 rest2 Hsecond.
  - inversion Hsecond; subst; auto; contradiction.
  - inversion Hsecond; subst; try contradiction.
    destruct (IH _ _ H4) as [-> ->]. auto.
Qed.

Lemma CanonicalRemovalCost_length :
  forall source target cost,
    CanonicalRemovalCost source target cost ->
    length source = length target.
Proof.
  intros source target. revert source.
  induction target as [|x target_tail IH];
    intros source cost Hcost.
  - simpl in Hcost. destruct Hcost as [-> _]. reflexivity.
  - simpl in Hcost.
    destruct Hcost as
      [position [rest [tail_cost [Hremove [Htail _]]]]].
    pose proof (FirstRemove_length _ _ _ _ Hremove) as Hsource.
    specialize (IH _ _ Htail). simpl. lia.
Qed.

Lemma CanonicalRemovalCost_cons_iff :
  forall x source target cost,
    CanonicalRemovalCost (x :: source) (x :: target) cost <->
    CanonicalRemovalCost source target cost.
Proof.
  intros x source target cost. split.
  - simpl. intros Hcost.
    destruct Hcost as
      [position [rest [tail_cost [Hremove [Htail Hsum]]]]].
    inversion Hremove; subst; try contradiction.
    exact Htail.
  - intros Htail. simpl.
    exists 0%nat, source, cost.
    repeat split; auto using FirstRemove_here.
Qed.

Lemma CanonicalRemovalCost_common_prefix :
  forall prefix source target cost,
    CanonicalRemovalCost (prefix ++ source) (prefix ++ target) cost <->
    CanonicalRemovalCost source target cost.
Proof.
  induction prefix as [|x prefix IH]; intros source target cost.
  - simpl. tauto.
  - change
      (CanonicalRemovalCost (x :: prefix ++ source)
         (x :: prefix ++ target) cost <->
       CanonicalRemovalCost source target cost).
    rewrite CanonicalRemovalCost_cons_iff. apply IH.
Qed.

Lemma SwapReach_monotone :
  forall source target small large,
    SwapReach source target small ->
    small <= large ->
    SwapReach source target large.
Proof.
  intros source target small large
    [states [Hlength [Hfirst [Hlast Hsteps]]]] Hbound.
  exists states. repeat split; try assumption; lia.
Qed.

Lemma PrefixEq_common_prefix :
  forall prefix left right,
    Zlength left = Zlength right ->
    PrefixEq (prefix ++ left) (prefix ++ right) (Zlength prefix).
Proof.
  intros prefix left right Hlength.
  unfold PrefixEq.
  split.
  - rewrite !Zlength_app. lia.
  - split.
    + rewrite Zlength_app.
      pose proof (Zlength_nonneg prefix).
      pose proof (Zlength_nonneg left). lia.
    + intros j Hj. rewrite !app_Znth1 by lia. reflexivity.
Qed.

Lemma PrefixEq_decompose :
  forall left right position,
    PrefixEq left right position ->
    exists prefix left_tail right_tail,
      left = prefix ++ left_tail /\
      right = prefix ++ right_tail /\
      Zlength prefix = position /\
      Zlength left_tail = Zlength right_tail.
Proof.
  intros left right position Hprefix.
  unfold PrefixEq in Hprefix.
  destruct Hprefix as [Hlength [Hposition Hequal]].
  set (prefix := sublist 0 position left).
  set (left_tail := sublist position (Zlength left) left).
  set (right_tail := sublist position (Zlength right) right).
  exists prefix, left_tail, right_tail.
  assert (Hprefix_right : prefix = sublist 0 position right).
  {
    subst prefix.
    apply (proj2 (list_eq_ext _ _ 0)).
    split.
    - rewrite !Zlength_sublist by lia. lia.
    - intros j Hj.
      rewrite Zlength_sublist in Hj by lia.
      rewrite !Znth_sublist by lia.
      apply Hequal. lia.
  }
  repeat split.
  - subst prefix left_tail.
    rewrite <- sublist_split with
        (lo := 0) (mid := position) (hi := Zlength left) by lia.
    rewrite sublist_self by reflexivity. reflexivity.
  - subst right_tail. rewrite Hprefix_right.
    rewrite <- sublist_split with
        (lo := 0) (mid := position) (hi := Zlength right) by lia.
    rewrite sublist_self by reflexivity. reflexivity.
  - subst prefix. rewrite Zlength_sublist by lia. lia.
  - subst left_tail right_tail.
    rewrite !Zlength_sublist by lia. lia.
Qed.

Lemma move_left_app_middle :
  forall prefix middle x suffix,
    move_left (prefix ++ middle ++ x :: suffix)
      (Zlength prefix + Zlength middle) (Zlength prefix) =
    prefix ++ x :: middle ++ suffix.
Proof.
  intros prefix middle x suffix.
  pose proof (Zlength_nonneg prefix) as Hprefix_nonneg.
  pose proof (Zlength_nonneg middle) as Hmiddle_nonneg.
  pose proof (Zlength_nonneg suffix) as Hsuffix_nonneg.
  unfold move_left.
  rewrite sublist_app_exact1.
  rewrite app_Znth2 by lia.
  replace (Zlength prefix + Zlength middle - Zlength prefix)
    with (Zlength middle) by lia.
  rewrite app_Znth2 by lia.
  replace (Zlength middle - Zlength middle) with 0 by lia.
  simpl.
  rewrite sublist_split_app_r with
      (l1 := prefix) (l2 := middle ++ x :: suffix)
      (len := Zlength prefix) by (try reflexivity; lia).
  replace (Zlength prefix - Zlength prefix) with 0 by lia.
  replace (Zlength prefix + Zlength middle - Zlength prefix)
    with (Zlength middle) by lia.
  rewrite sublist_app_exact1.
  rewrite !Zlength_app, !Zlength_cons.
  rewrite sublist_split_app_r with
      (l1 := prefix) (l2 := middle ++ x :: suffix)
      (len := Zlength prefix) by (try reflexivity; lia).
  replace (Zlength prefix + Zlength middle + 1 - Zlength prefix)
    with (Zlength middle + 1) by lia.
  replace
    (Zlength prefix + Zlength middle + 1 + Zlength suffix -
       Zlength prefix)
    with (Zlength middle + 1 + Zlength suffix) by lia.
  rewrite sublist_split_app_r with
      (l1 := middle) (l2 := x :: suffix)
      (len := Zlength middle) by (try reflexivity; lia).
  replace (Zlength middle + 1 - Zlength middle) with 1 by lia.
  replace
    (Zlength middle + 1 + Zlength suffix - Zlength middle)
    with (1 + Zlength suffix) by lia.
  rewrite sublist_cons2 by (try rewrite Zlength_cons; lia).
  replace (1 - 1) with 0 by lia.
  replace (1 + Zlength suffix - 1) with (Zlength suffix) by lia.
  rewrite sublist_self by lia.
  simpl. reflexivity.
Qed.

(* A structural presentation of the same lexicographic preorder as [LexLe].
   This avoids repeating index arithmetic when composing the two greedy
   comparisons. *)
Inductive StructuralLexLe : list Z -> list Z -> Prop :=
| SLL_nil : forall right,
    StructuralLexLe [] right
| SLL_lt : forall x y left right,
    x < y -> StructuralLexLe (x :: left) (y :: right)
| SLL_eq : forall x left right,
    StructuralLexLe left right ->
    StructuralLexLe (x :: left) (x :: right).

Lemma StructuralLexLe_refl :
  forall values, StructuralLexLe values values.
Proof.
  induction values as [|x values IH].
  - constructor.
  - apply SLL_eq. exact IH.
Qed.

Lemma StructuralLexLe_app :
  forall prefix left right,
    StructuralLexLe left right ->
    StructuralLexLe (prefix ++ left) (prefix ++ right).
Proof.
  induction prefix as [|x prefix IH]; intros left right Hle; simpl.
  - exact Hle.
  - apply SLL_eq. apply IH. exact Hle.
Qed.

Lemma StructuralLexLe_trans :
  forall left middle,
    StructuralLexLe left middle ->
    forall right,
      StructuralLexLe middle right ->
      StructuralLexLe left right.
Proof.
  intros left middle Hfirst.
  induction Hfirst as
      [middle | x y left middle Hxy | x left middle Hfirst IH];
    intros right Hsecond.
  - apply SLL_nil.
  - inversion Hsecond; subst.
    + apply SLL_lt. lia.
    + apply SLL_lt. lia.
  - inversion Hsecond; subst.
    + apply SLL_lt. assumption.
    + apply SLL_eq. apply IH. assumption.
Qed.

Lemma StructuralLexLe_to_LexLe :
  forall left right,
    StructuralLexLe left right -> LexLe left right.
Proof.
  intros left right Hle.
  induction Hle as
      [right | x y left right Hxy | x left right Htail IH].
  - destruct right as [|y right].
    + left. reflexivity.
    + right. right. split.
      * rewrite Zlength_nil, Zlength_cons.
        pose proof (Zlength_nonneg right). lia.
      * exists (y :: right). reflexivity.
  - right. left. exists 0.
    rewrite !Zlength_cons.
    pose proof (Zlength_nonneg left).
    pose proof (Zlength_nonneg right).
    split; [lia |]. split.
    + intros j Hj. lia.
    + rewrite !Znth0_cons. exact Hxy.
  - unfold LexLe in IH |- *.
    destruct IH as [Heq | [Hstrict | Hprefix]].
    + left. subst right. reflexivity.
    + right. left.
      destruct Hstrict as [i [Hi [Heqprefix Hlt]]].
      exists (i + 1).
      rewrite !Zlength_cons in *.
      split; [lia |]. split.
      * intros j Hj.
        destruct (Z.eq_dec j 0) as [-> | Hj0].
        -- rewrite !Znth0_cons. reflexivity.
        -- specialize (Heqprefix (j - 1) ltac:(lia)).
           rewrite !Znth_cons by lia.
           exact Heqprefix.
      * rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with i by lia. exact Hlt.
    + right. right.
      destruct Hprefix as [Hlength [suffix Hsuffix]].
      split.
      * rewrite !Zlength_cons. lia.
      * exists suffix. subst right. reflexivity.
Qed.

Lemma LexLe_to_StructuralLexLe :
  forall left right,
    LexLe left right -> StructuralLexLe left right.
Proof.
  induction left as [|x left IH]; intros right Hle.
  - constructor.
  - destruct right as [|y right].
    + unfold LexLe in Hle.
      destruct Hle as [Heq | [[i [Hi _]] | [Hlength _]]].
      * discriminate.
      * rewrite Zlength_nil in Hi. lia.
      * rewrite Zlength_nil in Hlength.
        pose proof (Zlength_nonneg (x :: left)). lia.
    + unfold LexLe in Hle.
      destruct Hle as [Heq | [Hstrict | Hprefix]].
      * inversion Heq; subst. apply StructuralLexLe_refl.
      * destruct Hstrict as [i [Hi [Heqprefix Hlt]]].
        destruct (Z.eq_dec i 0) as [-> | Hi0].
        -- apply SLL_lt. rewrite !Znth0_cons in Hlt. exact Hlt.
        -- assert (Hxy : x = y).
           { specialize (Heqprefix 0 ltac:(lia)).
             rewrite !Znth0_cons in Heqprefix. exact Heqprefix. }
           subst y. apply SLL_eq. apply IH.
           unfold LexLe. right. left. exists (i - 1).
           rewrite !Zlength_cons in Hi.
           split; [lia |]. split.
           ++ intros j Hj.
              specialize (Heqprefix (j + 1) ltac:(lia)).
              rewrite !Znth_cons in Heqprefix by lia.
              replace (j + 1 - 1) with j in Heqprefix by lia.
              exact Heqprefix.
           ++ rewrite !Znth_cons in Hlt by lia. exact Hlt.
      * destruct Hprefix as [Hlength [suffix Hsuffix]].
        simpl in Hsuffix. inversion Hsuffix; subst y right.
        apply SLL_eq. apply IH.
        unfold LexLe. right. right. split.
        -- rewrite !Zlength_cons in Hlength. lia.
        -- exists suffix. reflexivity.
Qed.

Lemma LexLe_trans :
  forall left middle right,
    LexLe left middle -> LexLe middle right -> LexLe left right.
Proof.
  intros left middle right Hfirst Hsecond.
  apply StructuralLexLe_to_LexLe.
  eapply StructuralLexLe_trans.
  - apply LexLe_to_StructuralLexLe. exact Hfirst.
  - apply LexLe_to_StructuralLexLe. exact Hsecond.
Qed.

Lemma LexLe_common_prefix_lt :
  forall prefix x left y right,
    x < y ->
    LexLe (prefix ++ x :: left) (prefix ++ y :: right).
Proof.
  intros prefix x left y right Hlt.
  apply StructuralLexLe_to_LexLe.
  apply StructuralLexLe_app. constructor. exact Hlt.
Qed.

Lemma ReachableFirstMaximum_decompose :
  forall current pos remaining best,
    ReachableFirstMaximum current pos remaining best ->
    exists prefix middle x suffix,
      current = prefix ++ middle ++ x :: suffix /\
      Zlength prefix = pos /\
      Zlength middle = best - pos /\
      Forall (fun y => y < x) middle /\
      best - pos <= remaining /\
      FirstRemove x (middle ++ x :: suffix) (length middle)
        (middle ++ suffix) /\
      move_left current best pos = prefix ++ x :: middle ++ suffix.
Proof.
  intros current pos remaining best Hmaximum.
  unfold ReachableFirstMaximum, FirstMaximumPrefix in Hmaximum.
  destruct Hmaximum as
    [[Hpos0 Hposhi] [Hhilength [[Hposbest Hbesthi]
      [Hgreatest Hfirst]]]].
  apply Z.min_glb_lt_iff in Hbesthi.
  destruct Hbesthi as [Hbestlength Hbestbudget].
  set (prefix := sublist 0 pos current).
  set (middle := sublist pos best current).
  set (x := Znth best current 0).
  set (suffix := sublist (best + 1) (Zlength current) current).
  exists prefix, middle, x, suffix.
  assert (Hprefix_length : Zlength prefix = pos).
  { subst prefix. rewrite Zlength_sublist by lia. lia. }
  assert (Hmiddle_length : Zlength middle = best - pos).
  { subst middle. rewrite Zlength_sublist by lia. lia. }
  assert (Hdecompose : current = prefix ++ middle ++ x :: suffix).
  {
    subst prefix middle x suffix.
    rewrite <- sublist_self with
        (l1 := current) (x := Zlength current) at 1 by reflexivity.
    rewrite sublist_split with
        (lo := 0) (mid := pos) (hi := Zlength current) by lia.
    rewrite sublist_split with
        (lo := pos) (mid := best) (hi := Zlength current) by lia.
    rewrite sublist_split with
        (lo := best) (mid := best + 1) (hi := Zlength current) by lia.
    rewrite (sublist_single 0 best current) by lia.
    reflexivity.
  }
  assert (Hmiddle_small : Forall (fun y => y < x) middle).
  {
    apply Forall_forall. intros y Hy.
    destruct (In_nth middle y 0 Hy) as [n [Hn Hnth]].
    assert (HnZ : 0 <= Z.of_nat n < Zlength middle).
    { rewrite Zlength_correct. lia. }
    specialize (Hfirst (pos + Z.of_nat n) ltac:(lia)).
    subst middle x.
    replace (pos + Z.of_nat n) with (Z.of_nat n + pos) in Hfirst by lia.
    rewrite <- (Znth_sublist 0 pos (Z.of_nat n) best current)
      in Hfirst by lia.
    unfold Znth in Hfirst.
    rewrite Nat2Z.id in Hfirst.
    rewrite Hnth in Hfirst. exact Hfirst.
  }
  assert (Hremove :
    FirstRemove x (middle ++ x :: suffix) (length middle)
      (middle ++ suffix)).
  {
    apply FirstRemove_app_absent.
    rewrite Forall_forall in Hmiddle_small |- *.
    intros y Hy.
    specialize (Hmiddle_small y Hy). lia.
  }
  split; [exact Hdecompose |].
  split; [exact Hprefix_length |].
  split; [exact Hmiddle_length |].
  split; [exact Hmiddle_small |].
  split; [lia |].
  split; [exact Hremove |].
  rewrite Hdecompose.
  replace best with (Zlength prefix + Zlength middle) by lia.
  replace pos with (Zlength prefix) by lia.
  apply move_left_app_middle.
Qed.

Lemma app_cancel_equal_Zlength :
  forall (left_prefix left_tail right_prefix right_tail : list Z),
    Zlength left_prefix = Zlength right_prefix ->
    left_prefix ++ left_tail = right_prefix ++ right_tail ->
    left_prefix = right_prefix /\ left_tail = right_tail.
Proof.
  intros left_prefix left_tail right_prefix right_tail Hlength Happ.
  apply app_eq_app in Happ.
  destruct Happ as
      [[middle [Hleft Hright]] | [middle [Hright Hleft]]].
  - assert (Hmiddle : middle = []).
    {
      rewrite Hleft, Zlength_app in Hlength.
      destruct middle as [|x middle]; [reflexivity |].
      rewrite Zlength_cons in Hlength.
      pose proof (Zlength_nonneg middle). lia.
    }
    subst middle. rewrite app_nil_r in Hleft. simpl in Hright.
    auto.
  - assert (Hmiddle : middle = []).
    {
      rewrite Hright, Zlength_app in Hlength.
      destruct middle as [|x middle]; [reflexivity |].
      rewrite Zlength_cons in Hlength.
      pose proof (Zlength_nonneg middle). lia.
    }
    subst middle. rewrite app_nil_r in Hright. simpl in Hleft.
    auto.
Qed.

Lemma FirstRemove_Znth :
  forall x source position rest,
    FirstRemove x source position rest ->
    Znth (Z.of_nat position) source 0 = x.
Proof.
  intros x source position rest Hremove.
  destruct (FirstRemove_decompose _ _ _ _ Hremove) as
    [prefix [suffix [Hsource [Hrest [Hlength Habsent]]]]].
  rewrite Hsource.
  rewrite app_Znth2.
  - rewrite Zlength_correct, Hlength.
    replace (Z.of_nat position - Z.of_nat position) with 0 by lia.
    reflexivity.
  - rewrite Zlength_correct, Hlength. lia.
Qed.

Lemma ReachableFirstMaximum_exchange :
  forall current pos remaining best,
    ReachableFirstMaximum current pos remaining best ->
    GreedyExchangeClosure current pos remaining best.
Proof.
  intros current pos remaining best Hmaximum.
  pose proof Hmaximum as Hmaximum_fields.
  unfold ReachableFirstMaximum, FirstMaximumPrefix in Hmaximum_fields.
  destruct Hmaximum_fields as
    [[Hpos0 Hposhi] [Hhilength [[Hposbest Hbesthi]
      [Hgreatest Hfirst]]]].
  apply Z.min_glb_lt_iff in Hbesthi.
  destruct Hbesthi as [Hbestlength Hbestbudget].
  destruct (ReachableFirstMaximum_decompose
              _ _ _ _ Hmaximum) as
    [selected_prefix [middle [x [suffix
      [Hcurrent [Hselected_length [Hmiddle_length
        [Hmiddle_small [Hcost_bound [Hselected_remove Hmoved]]]]]]]]]].
  assert (Hcurrent_le_moved :
    LexLe current (move_left current best pos)).
  {
    rewrite Hmoved, Hcurrent.
    destruct middle as [|head middle_tail].
    - simpl. left. reflexivity.
    - inversion Hmiddle_small; subst.
      simpl.
      apply LexLe_common_prefix_lt. assumption.
  }
  unfold GreedyExchangeClosure.
  split.
  - intros q Hq. eapply LexLe_trans; eauto.
  - intros q Hprefix Hreach.
    destruct (SwapReach_canonical_lower_bound _ _ _ Hreach) as
      [cost [Hcanonical Hcanonical_bound]].
    destruct (PrefixEq_decompose _ _ _ Hprefix) as
      [prefix [qtail [current_tail
        [Hq [Hcurrent_prefix [Hprefix_length Htail_length]]]]]].
    assert (Hprefix_same : prefix = selected_prefix /\
      current_tail = middle ++ x :: suffix).
    {
      apply app_cancel_equal_Zlength.
      - lia.
      - rewrite <- Hcurrent_prefix. exact Hcurrent.
    }
    destruct Hprefix_same as [-> Hcurrent_tail].
    subst current_tail.
    assert (Htail_canonical :
      CanonicalRemovalCost (middle ++ x :: suffix) qtail cost).
    {
      apply (proj1 (CanonicalRemovalCost_common_prefix
        selected_prefix (middle ++ x :: suffix) qtail cost)).
      rewrite <- Hcurrent, <- Hq. exact Hcanonical.
    }
    destruct qtail as [|y qrest].
    {
      rewrite Zlength_nil in Htail_length.
      rewrite Zlength_app, Zlength_cons in Htail_length.
      pose proof (Zlength_nonneg middle).
      pose proof (Zlength_nonneg suffix). lia.
    }
    simpl in Htail_canonical.
    destruct Htail_canonical as
      [position [source_rest [tail_cost
        [Hremove [Hrest_cost Hsum]]]]].
    assert (Hy_le_x : y <= x).
    {
      pose proof (FirstRemove_position_bound _ _ _ _ Hremove)
        as Hposition_bound.
      apply Nat2Z.inj_lt in Hposition_bound.
      rewrite <- Zlength_correct in Hposition_bound.
      pose proof (FirstRemove_Znth _ _ _ _ Hremove) as Hposition_value.
      assert (Habsolute_range :
        pos <= pos + Z.of_nat position <
          Z.min (Zlength current) (pos + remaining + 1)).
      {
        split; [lia |].
        apply Z.min_glb_lt_iff. split.
        + rewrite Hcurrent, Zlength_app.
          lia.
        + lia.
      }
      assert (Hbest_value : Znth best current 0 = x).
      {
        rewrite Hcurrent.
        rewrite app_Znth2 by lia.
        replace (best - Zlength selected_prefix)
          with (Zlength middle) by lia.
        rewrite app_Znth2 by lia.
        replace (Zlength middle - Zlength middle) with 0 by lia.
        reflexivity.
      }
      assert (Hposition_absolute_value :
        Znth (pos + Z.of_nat position) current 0 = y).
      {
        rewrite Hcurrent.
        rewrite app_Znth2 by lia.
        replace
          (pos + Z.of_nat position - Zlength selected_prefix)
          with (Z.of_nat position) by lia.
        exact Hposition_value.
      }
      specialize (Hgreatest (pos + Z.of_nat position) Habsolute_range).
      rewrite Hposition_absolute_value, Hbest_value in Hgreatest.
      exact Hgreatest.
    }
    destruct (Z_lt_ge_dec y x) as [Hy_lt_x | Hy_eq_x].
    + left. rewrite Hmoved, Hq.
      apply LexLe_common_prefix_lt. exact Hy_lt_x.
    + assert (Hyx : y = x) by lia. subst y.
      destruct (FirstRemove_functional
                  _ _ _ _ Hremove _ _ Hselected_remove) as
        [Hposition Hsource_rest].
      subst position source_rest.
      assert (Htail_budget :
        Z.of_nat tail_cost <= remaining - (best - pos)).
      {
        rewrite Zlength_correct in Hmiddle_length.
        lia.
      }
      assert (Hreconstructed :
        CanonicalRemovalCost
          ((selected_prefix ++ [x]) ++ middle ++ suffix)
          ((selected_prefix ++ [x]) ++ qrest) tail_cost).
      {
        apply (proj2 (CanonicalRemovalCost_common_prefix
          (selected_prefix ++ [x]) (middle ++ suffix) qrest tail_cost)).
        exact Hrest_cost.
      }
      pose proof (CanonicalRemovalCost_sound _ _ _ Hreconstructed)
        as Htail_reach.
      pose proof (SwapReach_monotone _ _ _ _ Htail_reach Htail_budget)
        as Htail_reach_budget.
      right. split.
      * rewrite Hmoved, Hq.
        replace (selected_prefix ++ x :: qrest)
          with ((selected_prefix ++ [x]) ++ qrest)
          by (rewrite <- app_assoc; reflexivity).
        replace (selected_prefix ++ x :: middle ++ suffix)
          with ((selected_prefix ++ [x]) ++ middle ++ suffix)
          by (rewrite <- app_assoc; reflexivity).
        replace (pos + 1) with (Zlength (selected_prefix ++ [x])).
        2:{ rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
        apply PrefixEq_common_prefix.
        pose proof (CanonicalRemovalCost_length _ _ _ Hrest_cost)
          as Hrest_length.
        rewrite !Zlength_correct. lia.
      * rewrite Hmoved, Hq.
        replace (selected_prefix ++ x :: qrest)
          with ((selected_prefix ++ [x]) ++ qrest)
          by (rewrite <- app_assoc; reflexivity).
        replace (selected_prefix ++ x :: middle ++ suffix)
          with ((selected_prefix ++ [x]) ++ middle ++ suffix)
          by (rewrite <- app_assoc; reflexivity).
        exact Htail_reach_budget.
Qed.

Lemma GreedySelectionReady_universal :
  forall current pos remaining,
    GreedySelectionReady current pos remaining.
Proof.
  intros current pos remaining best Hmaximum.
  apply ReachableFirstMaximum_exchange. exact Hmaximum.
Qed.

Lemma swap_reach_refl__initialization :
  forall a k, 0 <= k -> SwapReach a a k.
Proof.
  intros a k Hk.
  unfold SwapReach.
  exists [a].
  split.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - split.
    + reflexivity.
    + split.
      * rewrite Zlength_cons, Zlength_nil.
        replace (1 - 1) with 0 by lia.
        reflexivity.
      * intros i Hi.
        rewrite Zlength_cons, Zlength_nil in Hi.
        lia.
Qed.
Lemma greedy_progress_initial__initialization :
  forall input budget,
    0 <= budget ->
    GreedyProgress input budget input 0 budget.
Proof.
  intros input budget Hbudget.
  unfold GreedyProgress.
  repeat split.
  - reflexivity.
  - pose proof (Zlength_nonneg input). lia.
  - lia.
  - lia.
  - replace (budget - budget) with 0 by lia.
    apply swap_reach_refl__initialization. lia.
  - intros q Hreach.
    right. split.
    + unfold PrefixEq.
      destruct (SwapReach_canonical_lower_bound input q budget Hreach)
        as [cost [Hcost _]].
      pose proof (CanonicalRemovalCost_length _ _ _ Hcost) as Hlength.
      repeat split.
      * rewrite !Zlength_correct. lia.
      * lia.
      * pose proof (Zlength_nonneg q). lia.
      * intros j Hj. lia.
    + exact Hreach.
Qed.
Lemma first_maximum_prefix_singleton__selection_scan :
  forall l i,
    0 <= i < Zlength l ->
    FirstMaximumPrefix l i (i + 1) i.
Proof.
  intros l i Hi.
  unfold FirstMaximumPrefix.
  repeat split; try lia.
  intros p Hp.
  replace p with i by lia.
  lia.
Qed.
Lemma first_maximum_prefix_extend_strict__selection_scan :
  forall l lo hi best,
    FirstMaximumPrefix l lo hi best ->
    hi < Zlength l ->
    Znth best l 0 < Znth hi l 0 ->
    FirstMaximumPrefix l lo (hi + 1) hi.
Proof.
  intros l lo hi best Hmax Hhi Hstrict.
  unfold FirstMaximumPrefix in *.
  destruct Hmax as [Hlo [Hhilen [Hbest [Hub Hleft]]]].
  repeat split; try lia.
  - intros p Hp.
    destruct (Z_lt_ge_dec p hi) as [Hplt | Hphi].
    + specialize (Hub p). lia.
    + replace p with hi by lia. lia.
  - intros p Hp.
    destruct (Z_lt_ge_dec p hi) as [Hplt | Hphi].
    + specialize (Hub p). lia.
    + lia.
Qed.
Lemma first_maximum_prefix_extend_nonstrict__selection_scan :
  forall l lo hi best,
    FirstMaximumPrefix l lo hi best ->
    hi < Zlength l ->
    Znth hi l 0 <= Znth best l 0 ->
    FirstMaximumPrefix l lo (hi + 1) best.
Proof.
  intros l lo hi best Hmax Hhi Hnew.
  unfold FirstMaximumPrefix in *.
  destruct Hmax as [Hlo [Hhilen [Hbest [Hub Hleft]]]].
  repeat split; try lia.
  - intros p Hp.
    destruct (Z_lt_ge_dec p hi) as [Hplt | Hphi].
    + apply Hub. lia.
    + replace p with hi by lia. exact Hnew.
  - intros p Hp.
    apply Hleft. lia.
Qed.
Lemma first_maximum_prefix_extend_strict_app_zero__selection_scan :
  forall l lo hi best,
    FirstMaximumPrefix l lo hi best ->
    hi < Zlength l ->
    Znth best (l ++ [0]) 0 < Znth hi (l ++ [0]) 0 ->
    FirstMaximumPrefix l lo (hi + 1) hi.
Proof.
  intros l lo hi best Hmax Hhi Hstrict.
  apply first_maximum_prefix_extend_strict__selection_scan with (best := best);
    try assumption.
  unfold FirstMaximumPrefix in Hmax.
  destruct Hmax as
    [[Hlo0 Hlohi] [Hhilen [[Hlobest Hbesthi] [Hub Hleft]]]].
  rewrite !app_Znth1 in Hstrict by lia.
  exact Hstrict.
Qed.
Lemma first_maximum_prefix_extend_nonstrict_app_zero__selection_scan :
  forall l lo hi best,
    FirstMaximumPrefix l lo hi best ->
    hi < Zlength l ->
    Znth hi (l ++ [0]) 0 <= Znth best (l ++ [0]) 0 ->
    FirstMaximumPrefix l lo (hi + 1) best.
Proof.
  intros l lo hi best Hmax Hhi Hnew.
  apply first_maximum_prefix_extend_nonstrict__selection_scan;
    try assumption.
  unfold FirstMaximumPrefix in Hmax.
  destruct Hmax as
    [[Hlo0 Hlohi] [Hhilen [[Hlobest Hbesthi] [Hub Hleft]]]].
  rewrite !app_Znth1 in Hnew by lia.
  exact Hnew.
Qed.
Lemma move_left_same__selection_exchange :
  forall l i,
    0 <= i < Zlength l ->
    move_left l i i = l.
Proof.
  intros l i Hi.
  unfold move_left.
  rewrite (Zsublist_nil l i i) by lia.
  rewrite app_nil_l.
  rewrite <- sublist_single by lia.
  rewrite <- sublist_split by lia.
  rewrite <- sublist_split by lia.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.
Lemma move_left_same__bubble_transition :
  forall l i,
    0 <= i < Zlength l ->
    move_left l i i = l.
Proof.
  intros l i Hi.
  unfold move_left.
  rewrite (Zsublist_nil l i i) by lia.
  rewrite app_nil_l.
  rewrite <- sublist_single by lia.
  rewrite <- sublist_split by lia.
  rewrite <- sublist_split by lia.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.
Lemma move_left_permutation__bubble_transition :
  forall l from to,
    0 <= to /\ to <= from /\ from < Zlength l ->
    Permutation l (move_left l from to).
Proof.
  intros l from to Hbounds.
  unfold move_left.
  assert (Hdecomp :
      l = sublist 0 to l ++ sublist to from l ++
          [Znth from l 0] ++ sublist (from + 1) (Zlength l) l).
  {
    rewrite <- sublist_single by lia.
    rewrite <- sublist_split by lia.
    rewrite <- sublist_split by lia.
    rewrite <- sublist_split by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  rewrite Hdecomp at 1.
  apply Permutation_app_head.
  rewrite !app_assoc.
  apply Permutation_app_tail.
  apply Permutation_app_comm.
Qed.
Lemma move_left_Zlength__bubble_transition :
  forall l from to,
    0 <= to /\ to <= from /\ from < Zlength l ->
    Zlength (move_left l from to) = Zlength l.
Proof.
  intros l from to Hbounds.
  rewrite !Zlength_correct.
  f_equal.
  eapply Permutation_length.
  symmetry.
  apply move_left_permutation__bubble_transition.
  exact Hbounds.
Qed.
Lemma move_left_preserves_range__bubble_transition :
  forall l from to,
    0 <= to /\ to <= from /\ from < Zlength l ->
    (forall p, 0 <= p < Zlength l -> 48 <= Znth p l 0 <= 57) ->
    forall p, 0 <= p < Zlength l ->
      48 <= Znth p (move_left l from to) 0 <= 57.
Proof.
  intros l from to Hbounds Hrange.
  assert (Hforall : Forall (fun x => 48 <= x <= 57) l).
  {
    apply Forall_forall.
    intros x Hx.
    apply In_nth with (d := 0) in Hx.
    destruct Hx as [n [Hn <-]].
    specialize (Hrange (Z.of_nat n)).
    unfold Znth in Hrange.
    replace (Z.to_nat (Z.of_nat n)) with n in Hrange by lia.
    apply Hrange.
    rewrite Zlength_correct.
    lia.
  }
  assert (Hmoved : Forall (fun x => 48 <= x <= 57)
      (move_left l from to)).
  {
    eapply Permutation_Forall.
    - apply move_left_permutation__bubble_transition. exact Hbounds.
    - exact Hforall.
  }
  intros p Hp.
  apply (proj1 (Forall_forall _ _) Hmoved).
  unfold Znth.
  apply nth_In.
  assert (Hlen : length (move_left l from to) = length l).
  {
    eapply Permutation_length.
    symmetry.
    apply move_left_permutation__bubble_transition.
    exact Hbounds.
  }
  rewrite Hlen.
  rewrite Zlength_correct in Hp.
  lia.
Qed.
Lemma move_left_current_form__bubble_transition :
  forall l from to,
    0 < to /\ to <= from /\ from < Zlength l ->
    move_left l from to =
      sublist 0 (to - 1) l ++
      Znth (to - 1) l 0 :: Znth from l 0 ::
      (sublist to from l ++ sublist (from + 1) (Zlength l) l).
Proof.
  intros l from to Hbounds.
  unfold move_left.
  rewrite (sublist_split 0 to (to - 1) l) by lia.
  assert (Hsingle : sublist (to - 1) to l = [Znth (to - 1) l 0]).
  { pose proof (sublist_single 0 (to - 1) l ltac:(lia)) as H.
    replace (to - 1 + 1) with to in H by lia.
    exact H. }
  rewrite Hsingle.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma move_left_previous_form__bubble_transition :
  forall l from to,
    0 < to /\ to <= from /\ from < Zlength l ->
    move_left l from (to - 1) =
      sublist 0 (to - 1) l ++
      Znth from l 0 :: Znth (to - 1) l 0 ::
      (sublist to from l ++ sublist (from + 1) (Zlength l) l).
Proof.
  intros l from to Hbounds.
  unfold move_left.
  rewrite (sublist_split (to - 1) from to l) by lia.
  assert (Hsingle : sublist (to - 1) to l = [Znth (to - 1) l 0]).
  { pose proof (sublist_single 0 (to - 1) l ltac:(lia)) as H.
    replace (to - 1 + 1) with to in H by lia.
    exact H. }
  rewrite Hsingle.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma adjacent_swap_prefix_standard__bubble_transition :
  forall p x y s,
    replace_Znth (Zlength p + 1)
      (Znth (Zlength p) (p ++ x :: y :: s) 0)
      (replace_Znth (Zlength p)
        (Znth (Zlength p + 1) (p ++ x :: y :: s) 0)
        (p ++ x :: y :: s)) =
    p ++ y :: x :: s.
Proof.
  intros p x y s.
  rewrite !app_Znth2 by lia.
  replace (Zlength p - Zlength p) with 0 by lia.
  replace (Zlength p + 1 - Zlength p) with 1 by lia.
  rewrite Znth0_cons.
  rewrite Znth_cons by lia.
  rewrite Znth0_cons.
  rewrite replace_Znth_app_r by lia.
  rewrite (replace_Znth_nothing (Zlength p) p y) by lia.
  rewrite replace_Znth_app_r by lia.
  rewrite (replace_Znth_nothing (Zlength p + 1) p x) by lia.
  replace (Zlength p - Zlength p) with 0 by lia.
  replace (Zlength p + 1 - Zlength p) with 1 by lia.
  simpl.
  reflexivity.
Qed.
Lemma move_left_step_standard__bubble_transition :
  forall l from to,
    0 < to /\ to <= from /\ from < Zlength l ->
    replace_Znth to
      (Znth (to - 1) (move_left l from to) 0)
      (replace_Znth (to - 1)
        (Znth to (move_left l from to) 0)
        (move_left l from to)) =
    move_left l from (to - 1).
Proof.
  intros l from to Hbounds.
  rewrite move_left_current_form__bubble_transition by exact Hbounds.
  rewrite move_left_previous_form__bubble_transition by exact Hbounds.
  assert (Hprefix : Zlength (sublist 0 (to - 1) l) = to - 1).
  { rewrite Zlength_sublist by lia. lia. }
  set (p := sublist 0 (to - 1) l) in *.
  assert (Hto : to = Zlength p + 1) by lia.
  rewrite Hto.
  replace (Zlength p + 1 - 1) with (Zlength p) by lia.
  apply adjacent_swap_prefix_standard__bubble_transition.
Qed.
Lemma adjacent_swap_prefix_reverse__bubble_transition :
  forall p x y s,
    replace_Znth (Zlength p)
      (Znth (Zlength p + 1) (p ++ x :: y :: s) 0)
      (replace_Znth (Zlength p + 1)
        (Znth (Zlength p) (p ++ x :: y :: s) 0)
        (p ++ x :: y :: s)) =
    p ++ y :: x :: s.
Proof.
  intros p x y s.
  rewrite !app_Znth2 by lia.
  replace (Zlength p - Zlength p) with 0 by lia.
  replace (Zlength p + 1 - Zlength p) with 1 by lia.
  rewrite Znth0_cons.
  rewrite Znth_cons by lia.
  rewrite Znth0_cons.
  rewrite (replace_Znth_app_r (Zlength p + 1) x p (x :: y :: s))
    by lia.
  rewrite (replace_Znth_nothing (Zlength p + 1) p x) by lia.
  replace (Zlength p + 1 - Zlength p) with 1 by lia.
  assert (Hinner : replace_Znth 1 x (x :: y :: s) = x :: x :: s)
    by reflexivity.
  rewrite Hinner.
  rewrite (replace_Znth_app_r (Zlength p) y p (x :: x :: s))
    by lia.
  rewrite (replace_Znth_nothing (Zlength p) p y) by lia.
  replace (Zlength p - Zlength p) with 0 by lia.
  simpl.
  reflexivity.
Qed.
Lemma move_left_step_standard_reverse__bubble_transition :
  forall l from to,
    0 < to /\ to <= from /\ from < Zlength l ->
    replace_Znth (to - 1)
      (Znth to (move_left l from to) 0)
      (replace_Znth to
        (Znth (to - 1) (move_left l from to) 0)
        (move_left l from to)) =
    move_left l from (to - 1).
Proof.
  intros l from to Hbounds.
  rewrite move_left_current_form__bubble_transition by exact Hbounds.
  rewrite move_left_previous_form__bubble_transition by exact Hbounds.
  assert (Hprefix : Zlength (sublist 0 (to - 1) l) = to - 1).
  { rewrite Zlength_sublist by lia. lia. }
  set (p := sublist 0 (to - 1) l) in *.
  assert (Hto : to = Zlength p + 1) by lia.
  rewrite Hto.
  replace (Zlength p + 1 - 1) with (Zlength p) by lia.
  apply adjacent_swap_prefix_reverse__bubble_transition.
Qed.
Lemma replace_Znth_preserves_Zlength__bubble_transition :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l.
  induction l as [|x l IH]; intros n v; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|m].
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat m) v).
    replace (Z.to_nat (Z.of_nat m)) with m in IH by lia.
    rewrite IH. lia.
Qed.
Lemma move_left_step_padded__bubble_transition :
  forall l from to,
    0 < to /\ to <= from /\ from < Zlength l ->
    replace_Znth (to - 1)
      (Znth to (move_left l from to ++ [0]) 0)
      (replace_Znth to
        (Znth (to - 1) (move_left l from to ++ [0]) 0)
        (move_left l from to ++ [0])) =
    move_left l from (to - 1) ++ [0].
Proof.
  intros l from to Hbounds.
  assert (Hlen : Zlength (move_left l from to) = Zlength l).
  { apply move_left_Zlength__bubble_transition. lia. }
  rewrite !app_Znth1 by lia.
  rewrite (replace_Znth_app_l to
    (Znth (to - 1) (move_left l from to) 0) (move_left l from to) [0]) by lia.
  rewrite (replace_Znth_app_l (to - 1)
    (Znth to (move_left l from to) 0)
    (replace_Znth to (Znth (to - 1) (move_left l from to) 0)
      (move_left l from to)) [0]).
  2: lia.
  2: rewrite replace_Znth_preserves_Zlength__bubble_transition; lia.
  f_equal.
  apply move_left_step_standard_reverse__bubble_transition.
  exact Hbounds.
Qed.
Lemma adjacent_swap_move_left_step__bubble_transition :
  forall l from to,
    0 < to /\ to <= from /\ from < Zlength l ->
    AdjacentSwap (move_left l from to) (move_left l from (to - 1)).
Proof.
  intros l from to Hbounds.
  unfold AdjacentSwap.
  exists (to - 1).
  split.
  - rewrite move_left_Zlength__bubble_transition by lia.
    lia.
  - replace (to - 1 + 1) with to by lia.
    symmetry.
    apply move_left_step_standard__bubble_transition.
    exact Hbounds.
Qed.
Lemma extend_swap_history_first__bubble_transition :
  forall (h : list (list Z)) b,
    h <> [] -> Znth 0 (h ++ [b]) [] = Znth 0 h [].
Proof.
  intros h b Hne.
  rewrite app_Znth1; auto.
  destruct h; [contradiction|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg h). lia.
Qed.
Lemma extend_swap_history_last__bubble_transition :
  forall (h : list (list Z)) b,
    Znth (Zlength (h ++ [b]) - 1) (h ++ [b]) [] = b.
Proof.
  intros h b.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength h + (1 + 0) - 1) with (Zlength h) by lia.
  rewrite app_Znth2 by lia.
  replace (Zlength h + Z.succ 0 - 1 - Zlength h) with 0 by lia.
  reflexivity.
Qed.
Lemma extend_swap_history_steps__bubble_transition :
  forall h b,
    h <> [] ->
    (forall i, 0 <= i < Zlength h - 1 ->
      AdjacentSwap (Znth i h []) (Znth (i + 1) h [])) ->
    AdjacentSwap (Znth (Zlength h - 1) h []) b ->
    forall i, 0 <= i < Zlength (h ++ [b]) - 1 ->
      AdjacentSwap (Znth i (h ++ [b]) [])
        (Znth (i + 1) (h ++ [b]) []).
Proof.
  intros h b Hne Hsteps Hlast i Hi.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z_lt_ge_dec i (Zlength h - 1)) as [Hold | Hnew].
  - rewrite !app_Znth1 by lia.
    apply Hsteps. lia.
  - assert (i = Zlength h - 1) by lia. subst i.
    rewrite app_Znth1 by (destruct h; [contradiction|]; rewrite Zlength_cons;
      pose proof (Zlength_nonneg h); lia).
    replace (Zlength h - 1 + 1) with (Zlength h) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength h - Zlength h) with 0 by lia.
    exact Hlast.
Qed.
Lemma swap_reach_extend__bubble_transition :
  forall a b c k,
    SwapReach a b k ->
    AdjacentSwap b c ->
    SwapReach a c (k + 1).
Proof.
  intros a b c k Hreach Hstep.
  unfold SwapReach in *.
  destruct Hreach as [h [Hbounds [Hfirst [Hlast Hsteps]]]].
  assert (Hne : h <> []).
  { intro Heq. subst h. rewrite Zlength_nil in Hbounds. lia. }
  exists (h ++ [c]).
  repeat split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite extend_swap_history_first__bubble_transition by exact Hne.
    exact Hfirst.
  - apply extend_swap_history_last__bubble_transition.
  - apply extend_swap_history_steps__bubble_transition; try assumption.
    rewrite Hlast. exact Hstep.
Qed.
Lemma swap_reach_move_left_after__bubble_transition :
  forall input l k from to,
    0 <= to /\ to <= from /\ from < Zlength l ->
    SwapReach input l k ->
    SwapReach input (move_left l from to) (k + (from - to)).
Proof.
  intros input l k from to Hbounds Hreach.
  remember (Z.to_nat (from - to)) as n eqn:Hn.
  revert to Hbounds Hn.
  induction n as [|n IH]; intros to Hbounds Hn.
  - assert (Hdiff : from - to = 0).
    { rewrite <- (Z2Nat.id (from - to)) by lia.
      rewrite <- Hn. reflexivity. }
    assert (Hsame : from = to) by lia. subst to.
    replace (k + (from - from)) with k by lia.
    rewrite move_left_same__bubble_transition by lia.
    exact Hreach.
  - assert (Hdiff : from - to = Z.of_nat (S n)).
    { rewrite <- (Z2Nat.id (from - to)) by lia.
      rewrite <- Hn. reflexivity. }
    assert (Hchild : Z.to_nat (from - (to + 1)) = n).
    { assert (Hz : from - (to + 1) = Z.of_nat n) by lia.
      rewrite Hz. lia. }
    specialize (IH (to + 1) ltac:(lia) ltac:(symmetry; exact Hchild)).
    replace (k + (from - to)) with
      ((k + (from - (to + 1))) + 1) by lia.
    eapply swap_reach_extend__bubble_transition.
    + exact IH.
    + pose proof (adjacent_swap_move_left_step__bubble_transition
        l from (to + 1) ltac:(lia)) as Hstep.
      replace (to + 1 - 1) with to in Hstep by lia.
      exact Hstep.
Qed.
Lemma greedy_progress_terminal_spec__final_result :
  forall input budget current pos remaining,
    GreedyProgress input budget current pos remaining ->
    (pos = Zlength input \/ remaining = 0) ->
    Spec input budget current.
Proof.
  intros input budget current pos remaining Hprogress Hterminal.
  unfold GreedyProgress in Hprogress.
  destruct Hprogress as
      [Hcurrent_len [Hpos [Hremaining [Hinput_current Hmaximal]]]].
  unfold Spec.
  split.
  - unfold SwapReach in *.
    destruct Hinput_current as
        [states [Hstates_len [Hfirst [Hlast Hadjacent]]]].
    exists states.
    repeat split; try assumption; lia.
  - intros competitor Hinput_competitor.
    specialize (Hmaximal competitor Hinput_competitor).
    destruct Hmaximal as [Hlex | [Hprefix Hcurrent_competitor]].
    + unfold LexLe in Hlex.
      exact Hlex.
    + left.
      destruct Hterminal as [Hpos_full | Hremaining_zero].
      * apply (proj2 (list_eq_ext competitor current 0)).
        unfold PrefixEq in Hprefix.
        destruct Hprefix as [Hsame_len [Hprefix_bounds Hprefix_eq]].
        split; [exact Hsame_len |].
        intros j Hj.
        apply Hprefix_eq.
        rewrite Hpos_full, <- Hcurrent_len, <- Hsame_len.
        exact Hj.
      * unfold SwapReach in Hcurrent_competitor.
        destruct Hcurrent_competitor as
            [states [Hstates_len [Hfirst [Hlast Hadjacent]]]].
        assert (Hone : Zlength states = 1) by lia.
        replace (Zlength states - 1) with 0 in Hlast by lia.
        congruence.
Qed.
