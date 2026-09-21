Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.stock_trading Require Import stock_trading_goal.
From SimpleC.EE.LLM_bench.Algorithms.stock_trading Require Import stock_trading_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib.
Local Open Scope sac.

Lemma scratch_flat_to_rows_rec : forall (k : nat) x lo m l,
  0 <= m ->
  IntArray.seg x (lo * m) ((lo + Z.of_nat k) * m) l |--
  EX rows, “ Zlength rows = Z.of_nat k /\ Forall (fun row => Zlength row = m) rows ” &&
    store_array_rec (IntArray2.row_store m) x lo (lo + Z.of_nat k) rows.
Proof.
  induction k as [|k IH]; intros x lo m l Hm.
  - simpl. replace (lo + 0) with lo by lia.
    prop_apply (IntArray.seg_Zlength x (lo*m) (lo*m) l). Intros.
    assert (l = nil) by (apply Zlength_nil_inv; lia). subst l.
    rewrite IntArray.seg_empty.
    Exists (@nil (list Z)). simpl. entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (lo + Z.succ (Z.of_nat k)) with ((lo + 1) + Z.of_nat k) by lia.
    sep_apply (IntArray.seg_split_to_seg x (lo*m) ((lo+1)*m)
      (((lo+1)+Z.of_nat k)*m) l); [|nia].
    sep_apply (IH x (lo+1) m (sublist ((lo+1)*m-lo*m)
      (((lo+1)+Z.of_nat k)*m-lo*m) l) Hm).
    Intros rows.
    sep_apply (IntArray.seg_to_full x (lo*m) ((lo+1)*m)
      (sublist 0 ((lo+1)*m-lo*m) l)).
    replace ((lo+1)*m-lo*m) with m by ring.
    prop_apply IntArray.full_Zlength. Intros.
    Exists ((sublist 0 m l) :: rows).
    rewrite Zlength_cons. simpl store_array_rec.
    unfold IntArray2.row_store, IntArray2.row_addr.
    entailer!.
Qed.

Lemma scratch_flat_to_rows : forall x n m l,
  0 <= n -> 0 <= m ->
  IntArray.full x (n*m) l |--
  EX rows, “ Zlength rows = n /\ Forall (fun row => Zlength row = m) rows ” &&
    IntArray2.full x n m rows.
Proof.
  intros x n m l Hn Hm.
  sep_apply IntArray.full_to_seg.
  replace 0 with (0*m) at 1 by ring.
  replace (n*m) with ((0+Z.of_nat (Z.to_nat n))*m) by (rewrite Z2Nat.id by lia; ring).
  sep_apply (scratch_flat_to_rows_rec (Z.to_nat n) x 0 m l Hm).
  Intros rows. Exists rows.
  unfold IntArray2.full, store_array.
  rewrite Z2Nat.id by lia. replace (0+n) with n by lia.
  entailer!.
Qed.

Lemma scratch_row_to_undef_seg : forall x lo m row,
  IntArray2.row_store m x lo row |--
  IntArray.undef_seg x (lo*m) ((lo+1)*m).
Proof.
  intros. unfold IntArray2.row_store, IntArray2.row_addr.
  change (IntArray.full (x+lo*m*sizeof(INT)) m row |-- IntArray.undef_seg x (lo*m) ((lo+1)*m)).
  sep_apply IntArray.full_to_undef_full.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite <- IntArray.undef_seg_shift.
  replace (lo*m+0) with (lo*m) by ring.
  replace (lo*m+m) with ((lo+1)*m) by ring.
  entailer!.
Qed.

Lemma scratch_rows_rec_to_undef_seg : forall rows x lo hi m,
  0 <= m ->
  store_array_rec (IntArray2.row_store m) x lo hi rows |--
  IntArray.undef_seg x (lo*m) (hi*m).
Proof.
  induction rows as [|row rows IH]; intros x lo hi m Hm.
  - simpl. Intros. subst hi. rewrite IntArray.undef_seg_empty. entailer!.
  - simpl store_array_rec.
    prop_apply (store_array_rec_valid (list Z) (IntArray2.row_store m) x (lo+1) hi rows).
    Intros.
    sep_apply (IH x (lo+1) hi m Hm).
    sep_apply (scratch_row_to_undef_seg x lo m row).
    sep_apply (IntArray.undef_seg_merge_to_undef_seg x (lo*m) ((lo+1)*m) (hi*m)); [|nia].
    entailer!.
Qed.

Lemma scratch_rows_to_flat_undef : forall x n m rows,
  0 <= m ->
  IntArray2.full x n m rows |-- IntArray.undef_full x (n*m).
Proof.
  intros x n m rows Hm. unfold IntArray2.full, store_array.
  sep_apply (scratch_rows_rec_to_undef_seg rows x 0 n m Hm).
  replace (0*m) with 0 by ring.
  sep_apply IntArray.undef_seg_to_undef_full.
  replace (x+0*sizeof(INT)) with x by lia.
  replace (n*m-0) with (n*m) by ring.
  entailer!.
Qed.

Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg IntArray2.full.

Require Import AUXLib.MonotonicList.
Ltac stock_arith :=
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in *;
  try rewrite ?Zlength_replace_Znth, ?Zlength_app, ?Zlength_cons, ?Zlength_nil;
  lia.
Ltac stock_restore :=
  first [assumption | solve [stock_arith] |
  match goal with
  | |- Legacy.StockInputsBounded ?a ?b ?u ?s ?d ?m =>
      apply (Modern.stock_inputs_from_explicit a b u s d m); stock_restore
  | |- Legacy.StockTableShape ?t ?d ?m =>
      apply (proj2 (Modern.stock_shape_explicit t d m)); split; stock_restore
  | |- Legacy.StockTableValuesBounded ?t ?d ?m =>
      let Hs := fresh "Hshape" in
      assert (Hs : Legacy.StockTableShape t d m) by stock_restore;
      apply (proj2 (Modern.stock_bounds_explicit t d m Hs)); split; stock_restore
  | |- Legacy.StockDaysDone ?a ?b ?u ?s ?t ?m ?w ?n =>
      apply (proj2 (Modern.stock_days_facts a b u s t m w n)); stock_restore
  | |- Legacy.StockFillRows ?t ?d ?m ?r =>
      apply (proj2 (Modern.stock_fill_rows_facts t d m r)); stock_restore
  | |- Legacy.StockFillCells ?r ?m ?d ?c =>
      apply (proj2 (Modern.stock_fill_cells_facts r m d c)); stock_restore
  | |- Legacy.StockCopyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?c =>
      apply (proj2 (Modern.stock_copy_facts a b u s t m w d c ltac:(stock_arith))); stock_restore
  | |- Legacy.StockEarlyBuyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?n =>
      apply (proj2 (Modern.stock_early_facts a b u s t m w d n)); stock_restore
  | |- Legacy.StockSellProgress ?a ?b ?u ?s ?t ?m ?w ?d ?src ?n =>
      apply (proj2 (Modern.stock_sell_progress_facts a b u s t m w d src n)); stock_restore
  | |- Legacy.StockBuyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?src ?n =>
      apply (proj2 (Modern.stock_buy_progress_facts a b u s t m w d src n)); stock_restore
  | |- Legacy.StockAnswerProgress ?a ?b ?u ?s ?t ?d ?m ?w ?n ?ans =>
      apply (proj2 (Modern.stock_answer_facts a b u s t d m w n ans)); stock_restore
  | |- Legacy.StockSellQueue ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_sell_queue_ready_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockSellQueueExpiring ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_sell_queue_expiring_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockSellQueuePopping ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_sell_queue_popping_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockSellQueuePending ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_sell_queue_pending_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockBuyQueue ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_buy_queue_ready_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockBuyQueueExpiring ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_buy_queue_expiring_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockBuyQueuePopping ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_buy_queue_popping_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  | |- Legacy.StockBuyQueuePending ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (proj2 (Modern.stock_buy_queue_pending_facts t q src p l u h tail ltac:(stock_arith))); split; stock_restore
  end | (split; stock_restore)].
Ltac stock_weaken :=
  match goal with
  | |- Modern.StockMaximumProfit ?a ?b ?u ?s ?d ?m ?w ?ans =>
      apply (proj2 (Modern.stock_maximum_legacy a b u s d m w ans))
  | |- Modern.StockPortfolioValue ?a ?b ?u ?s ?m ?w ?d ?st ?v =>
      apply (proj2 (Modern.stock_portfolio_legacy a b u s m w d st v))
  | |- Modern.StockDaysDone ?a ?b ?u ?s ?t ?m ?w ?n =>
      apply (Modern.stock_days_math a b u s t m w n)
  | |- Modern.StockFillRows ?t ?d ?m ?r => apply (Modern.stock_fill_rows_math t d m r)
  | |- Modern.StockFillCells ?r ?m ?d ?c => apply (Modern.stock_fill_cells_math r m d c)
  | |- Modern.StockCopyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?c =>
      apply (Modern.stock_copy_math a b u s t m w d c ltac:(stock_arith))
  | |- Modern.StockEarlyBuyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?n =>
      apply (Modern.stock_early_math a b u s t m w d n)
  | |- Modern.StockSellProgress ?a ?b ?u ?s ?t ?m ?w ?d ?src ?n =>
      apply (Modern.stock_sell_progress_math a b u s t m w d src n)
  | |- Modern.StockBuyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?src ?n =>
      apply (Modern.stock_buy_progress_math a b u s t m w d src n)
  | |- Modern.StockAnswerProgress ?a ?b ?u ?s ?t ?d ?m ?w ?n ?ans =>
      apply (Modern.stock_answer_math a b u s t d m w n ans)
  | |- Modern.StockSellQueue ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_sell_queue_ready_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockSellQueueExpiring ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_sell_queue_expiring_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockSellQueuePopping ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_sell_queue_popping_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockSellQueuePending ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_sell_queue_pending_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockBuyQueue ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_buy_queue_ready_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockBuyQueueExpiring ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_buy_queue_expiring_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockBuyQueuePopping ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_buy_queue_popping_math t q src p l u h tail ltac:(stock_arith))
  | |- Modern.StockBuyQueuePending ?t ?q ?src ?p ?l ?u ?h ?tail =>
      apply (Modern.stock_buy_queue_pending_math t q src p l u h tail ltac:(stock_arith))
  end.
Ltac stock_finish :=
  first [assumption | solve [stock_arith] |
  match goal with
  | |- Forall ?P (sublist ?h ?t ?q) =>
      solve [apply (proj2 (Modern.stock_Forall_sublist P q h t ltac:(stock_arith) ltac:(stock_arith)));
             intros; stock_arith]
  end | solve [stock_weaken; assumption] |
  match goal with
  | H : Legacy.StockTableValuesBounded ?t ?d ?m |- _ =>
      let Hs := fresh "Hshape" in
      assert (Hs : Legacy.StockTableShape t d m) by stock_restore;
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_bounds_explicit t d m Hs) H) as HF;
      solve [tauto]
  | H : Legacy.StockTableShape ?t ?d ?m |- _ =>
      let HF := fresh "HF" in pose proof (proj1 (Modern.stock_shape_explicit t d m) H) as HF;
      solve [tauto | stock_arith]
  | H : Legacy.StockDaysDone ?a ?b ?u ?s ?t ?m ?w ?n |- _ =>
      let HB := fresh "HB" in
      pose proof (proj1 (Modern.stock_days_facts a b u s t m w n) H) as HB;
      clear H; destruct HB as [? [? [? ?]]]; stock_finish
  | H : Legacy.StockFillRows ?t ?d ?m ?r |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_fill_rows_facts t d m r) H) as HF;
      clear H; decompose [and] HF; stock_finish
  | H : Legacy.StockFillCells ?r ?m ?d ?c |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_fill_cells_facts r m d c) H) as HF;
      clear H; decompose [and] HF; stock_finish
  | H : Legacy.StockCopyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?c |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_copy_facts a b u s t m w d c ltac:(stock_arith)) H) as HF;
      clear H; decompose [and] HF; stock_finish
  | H : Legacy.StockEarlyBuyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?n |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_early_facts a b u s t m w d n) H) as HF;
      clear H; decompose [and] HF; stock_finish
  | H : Legacy.StockSellProgress ?a ?b ?u ?s ?t ?m ?w ?d ?src ?n |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_sell_progress_facts a b u s t m w d src n) H) as HF;
      clear H; decompose [and] HF; stock_finish
  | H : Legacy.StockBuyProgress ?a ?b ?u ?s ?t ?m ?w ?d ?src ?n |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_buy_progress_facts a b u s t m w d src n) H) as HF;
      clear H; decompose [and] HF; stock_finish
  | H : Legacy.StockAnswerProgress ?a ?b ?u ?s ?t ?d ?m ?w ?n ?ans |- _ =>
      let HF := fresh "HF" in
      pose proof (proj1 (Modern.stock_answer_facts a b u s t d m w n ans) H) as HF;
      clear H; decompose [and] HF; stock_finish
  end].

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 



Lemma proof_of_stock_init_storage_entail_wit_1 : stock_init_storage_entail_wit_1.
Proof. right. intros. rewrite Zlength_nil. entailer!. Qed.

Lemma proof_of_stock_init_storage_entail_wit_2 : stock_init_storage_entail_wit_2.
Proof. right. intros. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!. Qed.

Lemma proof_of_maximum_profit_safety_wit_70_split_goal_1 : maximum_profit_safety_wit_70_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueueExpiring dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockSellQueueExpiring, Legacy.StockSellQueue,
    Legacy.StockFiniteIndexInWindow in ReusePreH29.
  destruct ReusePreH29 as [Hqueue | Hqueue];
    destruct Hqueue as [_ [Hentries _]];
    specialize (Hentries head ltac:(lia));
    destruct Hentries as [_ [_ [_ Hindex]]];
    split_pures; dump_pre_spatial; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_70_split_goal_2 : maximum_profit_safety_wit_70_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueueExpiring dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockSellQueueExpiring, Legacy.StockSellQueue,
    Legacy.StockFiniteIndexInWindow in ReusePreH29.
  destruct ReusePreH29 as [Hqueue | Hqueue];
    destruct Hqueue as [_ [Hentries _]];
    specialize (Hentries head ltac:(lia));
    destruct Hentries as [_ [_ [_ Hindex]]];
    split_pures; dump_pre_spatial; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_70 : maximum_profit_safety_wit_70.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_70_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_70_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_80_split_goal_1 : maximum_profit_safety_wit_80_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH29; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) (j + 1) __default__List_Z
       ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_80_split_goal_2 : maximum_profit_safety_wit_80_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH29; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) (j + 1) __default__List_Z
       ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_80 : maximum_profit_safety_wit_80.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_80_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_80_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_88_split_goal_1 : maximum_profit_safety_wit_88_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH29; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) (j + 1) __default__List_Z
       ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_88_split_goal_2 : maximum_profit_safety_wit_88_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH29; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) (j + 1) __default__List_Z
       ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_88 : maximum_profit_safety_wit_88.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_88_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_88_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_96_split_goal_1 : maximum_profit_safety_wit_96_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueuePopping dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH28; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) last_index __default__List_Z
       ReusePreH27 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_96_split_goal_2 : maximum_profit_safety_wit_96_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueuePopping dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH28; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) last_index __default__List_Z
       ReusePreH27 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_96 : maximum_profit_safety_wit_96.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_96_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_96_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_109_split_goal_1 : maximum_profit_safety_wit_109_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH27; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) best_index __default__List_Z
       ReusePreH26 Hdone ReusePreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_109_split_goal_2 : maximum_profit_safety_wit_109_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH27; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) best_index __default__List_Z
       ReusePreH26 Hdone ReusePreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_109 : maximum_profit_safety_wit_109.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_109_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_109_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_111_split_goal_1 : maximum_profit_safety_wit_111_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH27; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) best_index __default__List_Z
       ReusePreH26 Hdone ReusePreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_111_split_goal_2 : maximum_profit_safety_wit_111_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  assert (Hdone : Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l
    max_stock_pre wait_days_pre i)
    by (unfold Legacy.StockSellProgress in ReusePreH27; tauto).
  pose proof
    (Legacy.StockDaysDone_cell_bounded__safety_sell
       ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre
       wait_days_pre i ((i - wait_days_pre) - 1) best_index __default__List_Z
       ReusePreH26 Hdone ReusePreH29 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  dump_pre_spatial; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_111 : maximum_profit_safety_wit_111.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_111_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_111_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_129_split_goal_1 : maximum_profit_safety_wit_129_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyQueueExpiring dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyQueueExpiring in ReusePreH31.
  destruct ReusePreH31 as [Hqueue | Hqueue];
  unfold Legacy.StockBuyQueue in Hqueue;
  destruct Hqueue as [_ [Hentries _]];
  specialize (Hentries head ltac:(lia));
  unfold Legacy.StockFiniteIndexInWindow in Hentries;
  dump_pre_spatial; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_129_split_goal_2 : maximum_profit_safety_wit_129_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyQueueExpiring dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyQueueExpiring in ReusePreH31.
  destruct ReusePreH31 as [Hqueue | Hqueue];
  unfold Legacy.StockBuyQueue in Hqueue;
  destruct Hqueue as [_ [Hentries _]];
  specialize (Hentries head ltac:(lia));
  unfold Legacy.StockFiniteIndexInWindow in Hentries;
  dump_pre_spatial; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_129 : maximum_profit_safety_wit_129.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_129_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_129_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_139_split_goal_1 : maximum_profit_safety_wit_139_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH29.
  destruct ReusePreH29 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) (j - 1) __default__List_Z
    ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_139_split_goal_2 : maximum_profit_safety_wit_139_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH29.
  destruct ReusePreH29 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) (j - 1) __default__List_Z
    ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_139 : maximum_profit_safety_wit_139.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_139_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_139_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_147_split_goal_1 : maximum_profit_safety_wit_147_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH29.
  destruct ReusePreH29 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) (j - 1) __default__List_Z
    ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_147_split_goal_2 : maximum_profit_safety_wit_147_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH29.
  destruct ReusePreH29 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) (j - 1) __default__List_Z
    ReusePreH28 Hdone ReusePreH31 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_147 : maximum_profit_safety_wit_147.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_147_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_147_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_155_split_goal_1 : maximum_profit_safety_wit_155_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyQueuePopping dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH30.
  destruct ReusePreH30 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) last_index __default__List_Z
    ReusePreH29 Hdone ReusePreH32 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_155_split_goal_2 : maximum_profit_safety_wit_155_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyQueuePopping dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH30.
  destruct ReusePreH30 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) last_index __default__List_Z
    ReusePreH29 Hdone ReusePreH32 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_155 : maximum_profit_safety_wit_155.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_155_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_155_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_168_split_goal_1 : maximum_profit_safety_wit_168_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH28.
  destruct ReusePreH28 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) best_index __default__List_Z
    ReusePreH27 Hdone ReusePreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_168_split_goal_2 : maximum_profit_safety_wit_168_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH28.
  destruct ReusePreH28 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) best_index __default__List_Z
    ReusePreH27 Hdone ReusePreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_168 : maximum_profit_safety_wit_168.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_168_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_168_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_170_split_goal_1 : maximum_profit_safety_wit_170_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH28.
  destruct ReusePreH28 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) best_index __default__List_Z
    ReusePreH27 Hdone ReusePreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_170_split_goal_2 : maximum_profit_safety_wit_170_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyProgress in ReusePreH28.
  destruct ReusePreH28 as [Hdone _].
  pose proof (Legacy.StockDaysDone_cell_bounded__safety_buy
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre i
    ((i - wait_days_pre) - 1) best_index __default__List_Z
    ReusePreH27 Hdone ReusePreH30 ltac:(lia) ltac:(lia)) as Hcell.
  unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in Hcell.
  destruct Hcell as [Hcell_lo Hcell_hi].
  dump_pre_spatial; int_auto; nia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_safety_wit_170 : maximum_profit_safety_wit_170.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_safety_wit_170_split_goal_1.
  - Goal_apply proof_of_maximum_profit_safety_wit_170_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_1 : maximum_profit_entail_wit_1.
Proof.
  right. intros.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&( "dp" )) ((days_pre+1)*(max_stock_pre+1)) 982081 ltac:(nia)).
  sep_apply (IntArray.undef_full_split_to_undef_seg (&( "queue_index" )) (max_stock_pre+1) 991 ltac:(lia)).
  sep_apply (IntArray.undef_seg_to_undef_full (&( "dp" )) 0 ((days_pre+1)*(max_stock_pre+1))).
  sep_apply (IntArray.undef_seg_to_undef_full (&( "queue_index" )) 0 (max_stock_pre+1)).
  simpl. rewrite !Z.add_0_r, !Z.sub_0_r. cancel.
Qed.

Lemma proof_of_maximum_profit_entail_wit_2 : maximum_profit_entail_wit_2.
Proof.
  left. intros. simpl. rewrite !Z.add_0_r.
  sep_apply (scratch_flat_to_rows (&( "dp" )) (days_pre+1) (max_stock_pre+1) cells_2 ltac:(lia) ltac:(lia)).
  Intros rows. Intros.
  assert (Hrows : Forall (fun row => Zlength row = max_stock_pre + 1) rows) by tauto.
  Exists rows cells. entailer!.
  rewrite Forall_map. eapply Forall_impl; [|exact Hrows].
  intros row Hrow. unfold StockRowLength. symmetry. exact Hrow.
Qed.

Lemma proof_of_maximum_profit_entail_wit_4_split_goal_1 : maximum_profit_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_4 : maximum_profit_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_4_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_5_split_goal_1 : maximum_profit_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockTableShape dp_init days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hfill : Legacy.StockFillRows dp_init days_pre max_stock_pre 0).
  { unfold Legacy.StockFillRows.
    split; [lia |].
    split; [exact ReusePreH13 |].
    intros r stock Hr Hstock. exfalso; lia. }
  exact Hfill.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_5 : maximum_profit_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_5_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_6_split_goal_1 : maximum_profit_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape : Legacy.StockTableShape dp_l_2 days_pre max_stock_pre) by stock_restore.
  destruct Hshape as [Hlen Hrows].
  rewrite <- (Legacy.same_index_different_default i dp_l_2 __default__List_Z ltac:(lia)).
  apply Hrows; lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_6_split_goal_2 : maximum_profit_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH14 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hfill :
    Legacy.StockFillCells (Znth i dp_l_2 __default__List_Z)
      max_stock_pre i 0).
  { unfold Legacy.StockFillCells.
    unfold Legacy.StockInputsBounded in ReusePreH12.
    destruct ReusePreH12 as [_ [_ [_ [_ [_ [Hmax_stock_pre _]]]]]].
    split; [lia |].
    unfold Legacy.StockFillRows in ReusePreH13.
    destruct ReusePreH13 as [_ [HTableShape Hforall]].
    split.
    - unfold Legacy.StockTableShape in HTableShape.
      destruct HTableShape as [Hrow Hcol].
      assert (Hi: 0 <= i < days_pre + 1) by lia.
      specialize (Hcol i Hi).
      rewrite <- (Legacy.same_index_different_default i dp_l_2
        __default__List_Z ltac:(lia)).
      exact Hcol.
    - intros stock Hstock. exfalso; lia. }
  exact Hfill.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_6 : maximum_profit_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_6_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_7_1 : maximum_profit_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH16 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH18 : (Legacy.StockFillCells (Znth i dp_l_2 __default__List_Z) max_stock_pre i j )) by stock_restore.
  assert (ReusePreH19 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  set (row' := replace_Znth j 0 (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + i * width * sizeof (INT)) j width 0
         (Znth i dp_l_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold row'.
    pose proof
      (IntArray2.missing_i_merge_to_full
         (&( "dp" )) i (days_pre + 1) width dp_l_2 row') as Htable_merge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width i) width row')
      with
      (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width row')
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold dp_l. cancel.
  - assert (Hvalue : 0 = Legacy.StockInitialCell i j).
    { subst i j. unfold Legacy.StockInitialCell.
      destruct (Z.eq_dec 0 0); [reflexivity | contradiction]. }
    pose proof
      (stock_fill_update_step__init_copy
         dp_l_2 days_pre max_stock_pre i j 0 __default__List_Z
         ReusePreH17 ReusePreH18 ltac:(lia) ltac:(lia) Hvalue) as Hstep.
    simpl in Hstep.
    change
      (Legacy.StockFillRows dp_l days_pre max_stock_pre i /\
       Legacy.StockFillCells (Znth i dp_l __default__List_Z)
         max_stock_pre i (j + 1)) in Hstep.
    destruct Hstep as [Hrows Hcells].
    (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    all: try (unfold Legacy.StockFillRows in Hrows; tauto).

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_7_2 : maximum_profit_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockFillCells (Znth i dp_l_2 __default__List_Z) max_stock_pre i j )) by stock_restore.
  assert (ReusePreH18 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  set (row' := replace_Znth j neg_inf
    (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + i * width * sizeof (INT)) j width neg_inf
         (Znth i dp_l_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold row'.
    pose proof
      (IntArray2.missing_i_merge_to_full
         (&( "dp" )) i (days_pre + 1) width dp_l_2 row') as Htable_merge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width i) width row')
      with
      (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width row')
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold dp_l. cancel.
  - assert (Hvalue : neg_inf = Legacy.StockInitialCell i j).
    { subst neg_inf. unfold Legacy.StockInitialCell.
      destruct (Z.eq_dec i 0); [contradiction | reflexivity]. }
    pose proof
      (stock_fill_update_step__init_copy
         dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z
         ReusePreH16 ReusePreH17 ltac:(lia) ltac:(lia) Hvalue) as Hstep.
    simpl in Hstep.
    change
      (Legacy.StockFillRows dp_l days_pre max_stock_pre i /\
       Legacy.StockFillCells (Znth i dp_l __default__List_Z)
         max_stock_pre i (j + 1)) in Hstep.
    destruct Hstep as [Hrows Hcells].
    (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    all: try (unfold Legacy.StockFillRows in Hrows; tauto).

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_7_3 : maximum_profit_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH16 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH18 : (Legacy.StockFillCells (Znth i dp_l_2 __default__List_Z) max_stock_pre i j )) by stock_restore.
  assert (ReusePreH19 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  set (row' := replace_Znth j neg_inf
    (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + i * width * sizeof (INT)) j width neg_inf
         (Znth i dp_l_2 __default__List_Z)) as Hrow_merge.
    assert (Haddr :
      (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrow_merge; try lia.
    fold row'.
    pose proof
      (IntArray2.missing_i_merge_to_full
         (&( "dp" )) i (days_pre + 1) width dp_l_2 row') as Htable_merge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width i) width row')
      with
      (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width row')
      in Htable_merge.
    sep_apply Htable_merge; try lia.
    fold dp_l. cancel.
  - assert (Hvalue : neg_inf = Legacy.StockInitialCell i j).
    { subst i neg_inf. unfold Legacy.StockInitialCell.
      destruct (Z.eq_dec 0 0); [|contradiction].
      destruct (Z.eq_dec j 0); [contradiction | reflexivity]. }
    pose proof
      (stock_fill_update_step__init_copy
         dp_l_2 days_pre max_stock_pre i j neg_inf __default__List_Z
         ReusePreH17 ReusePreH18 ltac:(lia) ltac:(lia) Hvalue) as Hstep.
    simpl in Hstep.
    change
      (Legacy.StockFillRows dp_l days_pre max_stock_pre i /\
       Legacy.StockFillCells (Znth i dp_l __default__List_Z)
         max_stock_pre i (j + 1)) in Hstep.
    destruct Hstep as [Hrows Hcells].
    (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    all: try (unfold Legacy.StockFillRows in Hrows; tauto).

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_8_split_goal_1 : maximum_profit_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH15 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockFillCells (Znth i dp_l_2 __default__List_Z) max_stock_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hfill :
    Legacy.StockFillRows dp_l_2 days_pre max_stock_pre (i + 1)).
  { unfold Legacy.StockFillRows in *.
    destruct ReusePreH15 as [_ [HTableShape Hforall]].
    split; [lia |].
    split; [exact HTableShape |].
    intros r stock Hr Hstock.
    destruct (Z_lt_dec r i) as [H_lt | H_ge].
    - apply Hforall; lia.
    - assert (r = i) by lia. subst r.
      assert (j = max_stock_pre + 1) by lia. subst j.
      unfold Legacy.StockFillCells in ReusePreH16.
      destruct ReusePreH16 as [_ [Hlen Hforall']].
      rewrite (Legacy.same_index_different_default i dp_l_2
        __default__List_Z ltac:(unfold Legacy.StockTableShape in HTableShape; lia)).
      split; [exact Hlen |].
      apply Hforall'. exact Hstock. }
  exact Hfill.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_8 : maximum_profit_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_8_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_9_split_goal_1 : maximum_profit_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH14 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (OldPost : (Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre 1 )).
  {
  assert (Hdone :
    Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2
      max_stock_pre wait_days_pre 1).
  { assert (i = days_pre + 1) by lia. subst i.
    exact (proj1
      (stock_completed_initial_table_days_done__init_copy
         ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre
         wait_days_pre ltac:(lia) ReusePreH12 ReusePreH13)). }
  exact Hdone.
  }
  stock_finish.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_9_split_goal_2 : maximum_profit_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH14 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (OldPost : (Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre 1 )).
  {
  assert (Hdone :
    Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2
      max_stock_pre wait_days_pre 1).
  { assert (i = days_pre + 1) by lia. subst i.
    exact (proj1
      (stock_completed_initial_table_days_done__init_copy
         ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre
         wait_days_pre ltac:(lia) ReusePreH12 ReusePreH13)). }
  exact Hdone.
  }
  stock_finish.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_9_split_goal_3 : maximum_profit_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockFillRows dp_l_2 days_pre max_stock_pre i )) by stock_restore.
  assert (ReusePreH14 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hdone :
    Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2
      max_stock_pre wait_days_pre 1).
  { assert (i = days_pre + 1) by lia. subst i.
    exact (proj1
      (stock_completed_initial_table_days_done__init_copy
         ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre
         wait_days_pre ltac:(lia) ReusePreH12 ReusePreH13)). }
  exact Hdone.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_9 : maximum_profit_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_9_split_goal_3.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_10_split_goal_1 : maximum_profit_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i )) by stock_restore.
  assert (ReusePreH14 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  unfold Legacy.StockCopyProgress.
  split; [exact ReusePreH13 |].
  repeat split; try lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_10 : maximum_profit_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_10_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_11 : maximum_profit_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH15 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
    (IntArray.missing_i_merge_to_full
       ((&( "dp" )) + (i - 1) * width * sizeof (INT)) j width
       (Znth j (Znth (i - 1) dp_l __default__List_Z) 0)
       (Znth (i - 1) dp_l __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    (&( "dp" )) + (i - 1) * width * sizeof (INT) + j * sizeof (INT) =
    (&( "dp" )) + ((i - 1) * width + j) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  change
    (IntArray.full
       ((&( "dp" )) + (i - 1) * width * sizeof (INT)) width
       (Znth (i - 1) dp_l __default__List_Z) **
     IntArray2.missing_i (&( "dp" )) (i - 1) 0
       (days_pre + 1) width dp_l)
    with
    (IntArray2.ElemArray.full
       (IntArray2.row_addr (&( "dp" )) width (i - 1)) width
       (Znth (i - 1) dp_l __default__List_Z) **
     IntArray2.missing_i (&( "dp" )) (i - 1) 0
       (days_pre + 1) width dp_l).
  pose proof (IntArray2.missing_i_merge_to_full
    (&( "dp" )) (i - 1) (days_pre + 1) width dp_l
    (Znth (i - 1) dp_l __default__List_Z)) as Htablemerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr (&( "dp" )) width (i - 1)) width
    (Znth (i - 1) dp_l __default__List_Z)) with
    (IntArray.full ((&( "dp" )) + (i - 1) * width * sizeof (INT)) width
      (Znth (i - 1) dp_l __default__List_Z)) in Htablemerge.
  sep_apply Htablemerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  - (split_pures; try stock_weaken); (dump_pre_spatial; try stock_weaken); try assumption; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_12 : maximum_profit_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  set (row' := replace_Znth j previous_value
      (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + i * width * sizeof (INT)) j width previous_value
         (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    fold row'.
    change
      (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width row')
      with
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width i) width row').
    pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) i (days_pre + 1) width dp_l_2 row') as Htablemerge.
    sep_apply Htablemerge; try lia.
    fold dp_l. cancel.
  - assert (HshapeA : Legacy.StockTableShape dp_l_2 (Zlength ap_l) max_stock_pre).
    { unfold Legacy.StockCopyProgress in ReusePreH16.
      destruct ReusePreH16 as [HD _]. unfold Legacy.StockDaysDone in HD. tauto. }
    assert (Hasklen : Zlength ap_l = days_pre).
    { unfold Legacy.StockTableShape in HshapeA, ReusePreH17.
      destruct HshapeA as [HA _]. destruct ReusePreH17 as [HD _]. lia. }
    assert (Hprev : 0 <= i - 1 < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH17. destruct ReusePreH17 as [Hlen _]. lia. }
    assert (Hcur : 0 <= i < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH17. destruct ReusePreH17 as [Hlen _]. lia. }
    assert (Hvalue0 : previous_value = Znth j (Znth (i - 1) dp_l_2 nil) 0).
    { rewrite (Znth_indep dp_l_2 (i - 1) __default__List_Z nil)
        in PreH14 by exact Hprev. exact PreH14. }
    assert (Hroweq : row' = replace_Znth j previous_value (Znth i dp_l_2 nil)).
    { unfold row'. rewrite (Znth_indep dp_l_2 i __default__List_Z nil)
        by exact Hcur. reflexivity. }
    pose proof
      (stock_copy_update_step__init_copy
        ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre
        i j previous_value HshapeA ReusePreH16 Hvalue0
        ltac:(rewrite Hasklen; lia) ltac:(lia) ltac:(lia)) as Hstep.
    simpl in Hstep. rewrite <- Hroweq in Hstep.
    change
      (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre
         wait_days_pre i (j + 1) /\
       Legacy.StockTableShape dp_l (Zlength ap_l) max_stock_pre) in Hstep.
    destruct Hstep as [Hcopy' Hshape'].
    rewrite Hasklen in Hshape'. (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_1 : maximum_profit_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_2 : maximum_profit_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  pose proof ReusePreH15 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]].
  unfold Legacy.StockEarlyBuyProgress.
  unfold Legacy.StockCopyProgress in ReusePreH16.
  destruct ReusePreH16 as [HD [Hi [Hcol Hcopy]]].
  split; [exact HD |].
  split; [exact Hi |].
  split; [lia |].
  split.
  - apply Hcopy; lia.
  - intros stock Hstock.
    destruct (Z_lt_dec stock 1); [lia |].
    apply Hcopy; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_3 : maximum_profit_entail_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_4 : maximum_profit_entail_wit_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [Haskmax _]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_5 : maximum_profit_entail_wit_13_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [Hbidask _]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_6 : maximum_profit_entail_wit_13_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13_split_goal_7 : maximum_profit_entail_wit_13_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hdaily]]]]]].
  specialize (Hdaily i ltac:(lia)).
  destruct Hdaily as [_ [_ [Hbuy _]]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_13 : maximum_profit_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_6.
  - Goal_apply proof_of_maximum_profit_entail_wit_13_split_goal_7.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_14_1 : maximum_profit_entail_wit_14_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  set (value := (- j) * ask_price).
  set (row' := replace_Znth j value (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l. split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + i * width * sizeof (INT)) j width value
      (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr : (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr. sep_apply Hrowmerge; try lia. fold row'.
    change (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width row')
      with (IntArray2.ElemArray.full
        (IntArray2.row_addr (&( "dp" )) width i) width row').
    pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) i (days_pre + 1) width dp_l_2 row') as Htablemerge.
    sep_apply Htablemerge; try lia.
    fold dp_l. cancel.
  - assert (Hcur : 0 <= i < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH24. destruct ReusePreH24 as [Hlen _]. lia. }
    assert (Hroweq : row' = replace_Znth j value (Znth i dp_l_2 nil)).
    { unfold row'. rewrite (Znth_indep dp_l_2 i __default__List_Z nil)
        by exact Hcur. reflexivity. }
    pose proof ReusePreH23 as Hprogress.
    unfold Legacy.StockEarlyBuyProgress in Hprogress.
    destruct Hprogress as [Hdone [Hday [Hnext [Hzero Hcells]]]].
    specialize (Hcells j ltac:(lia)). destruct (Z_lt_dec j j); [lia |].
    rewrite <- (Legacy.same_index_different_default i dp_l_2 __default__List_Z Hcur)
      in PreH1.
    assert (Hmax : value = Z.max (Znth j (Znth (i - 1) dp_l_2 nil) 0)
      (- j * Znth (i - 1) ap_l 0)).
    { unfold value. subst ask_price. rewrite <- Hcells. symmetry.
      apply Z.max_r. lia. }
    pose proof (stock_early_buy_update_step__early_buy
      ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre
      i j value days_pre ReusePreH22 ReusePreH23 ltac:(lia) ltac:(lia) Hmax) as Hstep.
    simpl in Hstep. rewrite <- Hroweq in Hstep.
    change (Legacy.StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre
      wait_days_pre i (j + 1) /\ Legacy.StockTableShape dp_l days_pre max_stock_pre)
      in Hstep.
    destruct Hstep as [Hprogress' Hshape']. (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_14_2 : maximum_profit_entail_wit_14_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  set (value := Znth j (Znth i dp_l_2 __default__List_Z) 0).
  set (row' := replace_Znth j value (Znth i dp_l_2 __default__List_Z)).
  set (dp_l := replace_Znth i row' dp_l_2).
  Exists queue_l_2 dp_l. split_pure_spatial.
  - pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + i * width * sizeof (INT)) j width value
      (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr : (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr. sep_apply Hrowmerge; try lia. fold row'.
    change (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width row')
      with (IntArray2.ElemArray.full
        (IntArray2.row_addr (&( "dp" )) width i) width row').
    pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) i (days_pre + 1) width dp_l_2 row') as Htablemerge.
    sep_apply Htablemerge; try lia.
    fold dp_l. cancel.
  - assert (Hcur : 0 <= i < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH24. destruct ReusePreH24 as [Hlen _]. lia. }
    assert (Hroweq : row' = replace_Znth j value (Znth i dp_l_2 nil)).
    { unfold row'. rewrite (Znth_indep dp_l_2 i __default__List_Z nil)
        by exact Hcur. reflexivity. }
    pose proof ReusePreH23 as Hprogress.
    unfold Legacy.StockEarlyBuyProgress in Hprogress.
    destruct Hprogress as [Hdone [Hday [Hnext [Hzero Hcells]]]].
    specialize (Hcells j ltac:(lia)). destruct (Z_lt_dec j j); [lia |].
    rewrite <- (Legacy.same_index_different_default i dp_l_2 __default__List_Z Hcur)
      in PreH1.
    assert (Hmax : value = Z.max (Znth j (Znth (i - 1) dp_l_2 nil) 0)
      (- j * Znth (i - 1) ap_l 0)).
    { unfold value.
      rewrite <- (Legacy.same_index_different_default i dp_l_2 __default__List_Z Hcur).
      subst ask_price. rewrite Hcells. symmetry. apply Z.max_l. lia. }
    pose proof (stock_early_buy_update_step__early_buy
      ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre
      i j value days_pre ReusePreH22 ReusePreH23 ltac:(lia) ltac:(lia) Hmax) as Hstep.
    simpl in Hstep. rewrite <- Hroweq in Hstep.
    change (Legacy.StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre
      wait_days_pre i (j + 1) /\ Legacy.StockTableShape dp_l days_pre max_stock_pre)
      in Hstep.
    destruct Hstep as [Hprogress' Hshape']. (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_1 : maximum_profit_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  unfold Legacy.StockSellQueue.
  split; [lia |].
  split.
  - intros pos Hpos; lia.
  - split.
    + intros left right Hlr; lia.
    + intros candidate Hcandidate.
      unfold Legacy.StockFiniteIndexInWindow in Hcandidate.
      destruct Hcandidate as [_ [Hcandlen [_ [Hcandlow _]]]].
      unfold Legacy.StockTableShape in ReusePreH17.
      destruct ReusePreH17 as [_ Hrows].
      specialize (Hrows (i - wait_days_pre - 1) ltac:(lia)).
      lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_2 : maximum_profit_entail_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  pose proof ReusePreH15 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [Hasklen _].
  unfold Legacy.StockCopyProgress in ReusePreH16.
  destruct ReusePreH16 as [Hdone [Hday [Hcol Hcells]]].
  unfold Legacy.StockSellProgress.
  split; [exact Hdone |].
  split; [rewrite Hasklen; lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split.
  - intros stock Hstock; apply Hcells; lia.
  - split.
    + intros stock Hstock; lia.
    + apply Hcells; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_3 : maximum_profit_entail_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [_ [_ [_ Hsellbounds]]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_4 : maximum_profit_entail_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [_ [_ [_ Hsellbounds]]]; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_5 : maximum_profit_entail_wit_15_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [[Hbidlo Hbidle] [Hask1000 _]].
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15_split_goal_6 : maximum_profit_entail_wit_15_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockCopyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH15.
  destruct ReusePreH15 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [[Hbidlo Hbidle] _].
  exact Hbidlo.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_15 : maximum_profit_entail_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_15_split_goal_6.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_16_split_goal_1 : maximum_profit_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH13 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hexp :
    Legacy.StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price
      (j + 2) (j + sell_cap) head tail).
  { unfold Legacy.StockSellQueueExpiring. left.
    replace (j + sell_cap + 1) with ((j + sell_cap) + 1) by lia.
    exact ReusePreH29. }
  try rewrite <- ReusePreH13. exact Hexp.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_16 : maximum_profit_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_16_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_17_split_goal_1 : maximum_profit_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hexpired : Znth head queue_l_2 0 > j + sell_cap) by lia.
  assert (Hqueue :
    Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price
      (j + 2) (j + sell_cap) (head + 1) tail).
  { eapply Legacy.StockSellQueue_drop_expired__sell_expire; eauto. }
  assert (Hexp :
    Legacy.StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price
      (j + 2) (j + sell_cap) (head + 1) tail).
  { unfold Legacy.StockSellQueueExpiring. right. exact Hqueue. }
  try rewrite <- ReusePreH14. exact Hexp.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_17 : maximum_profit_entail_wit_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_17_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_1_split_goal_1 : maximum_profit_entail_wit_18_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH13 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hqueue :
    Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price
      (j + 2) (j + sell_cap) head tail).
  { eapply Legacy.StockSellQueueExpiring_empty__sell_expire; eauto. }
  try rewrite <- ReusePreH13. exact Hqueue.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_1 : maximum_profit_entail_wit_18_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_18_1_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_2_split_goal_1 : maximum_profit_entail_wit_18_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hhead_upper : Znth head queue_l_2 0 <= j + sell_cap) by lia.
  assert (Hqueue :
    Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price
      (j + 2) (j + sell_cap) head tail).
  { eapply Legacy.StockSellQueueExpiring_head_bounded__sell_expire; eauto. }
  try rewrite <- ReusePreH14. exact Hqueue.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_2_split_goal_2 : maximum_profit_entail_wit_18_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (Hhead_upper : Znth head queue_l_2 0 <= j + sell_cap) by lia.
  assert (Hqueue :
    Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price
      (j + 2) (j + sell_cap) head tail).
  { eapply Legacy.StockSellQueueExpiring_head_bounded__sell_expire; eauto. }
  assert (Hhead_lower : j <= Znth head queue_l_2 0).
  { unfold Legacy.StockSellQueue in Hqueue.
    destruct Hqueue as [_ [Helems _]].
    specialize (Helems head ltac:(lia)).
    destruct Helems as [_ [_ [_ [Hlower _]]]].
    lia. }
  exact Hhead_lower.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_18_2 : maximum_profit_entail_wit_18_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_18_2_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_18_2_split_goal_2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_19_1 : maximum_profit_entail_wit_19_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueue dp_l queue_l ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists queue_l dp_l.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  pose proof (IntArray.missing_i_merge_to_full
    ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) (j + 1) width
    (Znth (j + 1) (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z) 0)
    (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hcell.
  assert (Haddr :
    (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) + (j + 1) * sizeof ( INT ) =
    (&( "dp" )) + (((i - wait_days_pre) - 1) * width + (j + 1)) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof (IntArray2.missing_i_merge_to_full
    (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l
    (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
    (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) with
    (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
      width (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  - unfold Legacy.StockSellQueue in ReusePreH30.
    destruct ReusePreH30 as [_ [Hvalid _]].
    specialize (Hvalid (tail - 1) ltac:(lia)).
    unfold Legacy.StockFiniteIndexInWindow in Hvalid.
    destruct Hvalid as [Hnonneg _].
    exact Hnonneg.
  - unfold Legacy.StockSellQueue in ReusePreH30.
    destruct ReusePreH30 as [_ [Hvalid _]].
    specialize (Hvalid (tail - 1) ltac:(lia)).
    unfold Legacy.StockFiniteIndexInWindow in Hvalid.
    destruct Hvalid as [_ [Hlt _]].
    unfold Legacy.StockTableShape in ReusePreH31.
    destruct ReusePreH31 as [_ Hrows].
    specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)).
    rewrite Hrows in Hlt. lia.
  - eapply Legacy.StockSellQueue_begin_popping__sell_pop_append.
    + lia.
    + unfold Legacy.StockTableShape in ReusePreH31.
      destruct ReusePreH31 as [_ Hrows].
      specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)).
      rewrite Hrows. lia.
    + assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l).
      { unfold Legacy.StockTableShape in ReusePreH31.
        destruct ReusePreH31 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l
        __default__List_Z Hsource_len).
      unfold Legacy.STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
    + replace (j + 1 + 1) with (j + 2) by lia.
      exact ReusePreH30.
  - match goal with
  | |- Forall ?P (sublist ?h ?t ?q) =>
    apply (proj2 (Modern.stock_Forall_sublist P q h t ltac:(lia) ltac:(lia)));
    intros pos Hpos;
    pose proof ReusePreH30 as Hqueue;
    destruct Hqueue as [_ [Hvalid _]];
    specialize (Hvalid pos Hpos);
    unfold Legacy.StockFiniteIndexInWindow in Hvalid;
    destruct Hvalid as [Hnonneg [Hlt _]];
    pose proof ReusePreH31 as Hshape;
    destruct Hshape as [_ Hrows];
    specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia));
    rewrite Hrows in Hlt; lia
  end.
  - match goal with
  | |- Forall ?P (sublist ?h ?t ?q) =>
    apply (proj2 (Modern.stock_Forall_sublist P q h t ltac:(lia) ltac:(lia)));
    intros pos Hpos;
    pose proof ReusePreH30 as Hqueue;
    destruct Hqueue as [_ [Hvalid _]];
    specialize (Hvalid pos Hpos);
    unfold Legacy.StockFiniteIndexInWindow in Hvalid;
    destruct Hvalid as [Hnonneg [Hlt _]];
    pose proof ReusePreH31 as Hshape;
    destruct Hshape as [_ Hrows];
    specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia));
    rewrite Hrows in Hlt; lia
  end.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_19_2 : maximum_profit_entail_wit_19_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueue dp_l queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l
    (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
    (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) with
    (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
      width (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) (j + 1) width
    (Znth (j + 1) (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z) 0)
    (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hcell.
  assert (Haddr :
    (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) + (j + 1) * sizeof ( INT ) =
    (&( "dp" )) + (((i - wait_days_pre) - 1) * width + (j + 1)) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  eapply Legacy.StockSellQueue_begin_popping__sell_pop_append.
  - lia.
  - unfold Legacy.StockTableShape in ReusePreH31.
    destruct ReusePreH31 as [_ Hrows].
    specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)).
    rewrite Hrows. lia.
  - assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l).
    { unfold Legacy.StockTableShape in ReusePreH31.
      destruct ReusePreH31 as [Hlen _]. rewrite Hlen. lia. }
    rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l
      __default__List_Z Hsource_len).
    unfold Legacy.STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
  - replace (j + 1 + 1) with (j + 2) by lia.
    exact ReusePreH30.
  all: try assumption; try lia.

  - stock_finish.
  - stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_20_1 : maximum_profit_entail_wit_20_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockSellQueuePopping dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (Hqueue_range : forall pos, head <= pos < tail ->
    0 <= Znth pos queue_l_2 0 <= max_stock_pre).
  { intros pos Hpos.
    pose proof (proj1 (Modern.stock_Forall_sublist (Z.le 0) queue_l_2 head tail ltac:(lia) ltac:(lia)) PreH42 pos Hpos) as Hl.
    pose proof (proj1 (Modern.stock_Forall_sublist (Z.ge max_stock_pre) queue_l_2 head tail ltac:(lia) ltac:(lia)) PreH43 pos Hpos) as Hu.
    lia. }
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) with
    (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
      width (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) last_index width
    (Znth last_index (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hcell.
  assert (Haddr :
    (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) + last_index * sizeof ( INT ) =
    (&( "dp" )) + (((i - wait_days_pre) - 1) * width + last_index) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  - pose proof (Hqueue_range (tail - 1 - 1) ltac:(lia)). lia.
  - pose proof (Hqueue_range (tail - 1 - 1) ltac:(lia)). lia.
  - eapply Legacy.StockSellQueuePopping_drop_tail__sell_pop_append.
    + exact ReusePreH31.
    + lia.
    + unfold Legacy.StockSellScore.
      rewrite <- (PreH28 ltac:(lia)).
      assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
      { unfold Legacy.StockTableShape in ReusePreH33.
        destruct ReusePreH33 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
        __default__List_Z Hsource_len).
      rewrite PreH27 in PreH2. exact PreH2.
  - match goal with
  | |- Forall ?P (sublist ?h ?t ?q) =>
      apply (proj2 (Modern.stock_Forall_sublist P q h t ltac:(lia) ltac:(lia)));
      intros pos Hpos; pose proof (Hqueue_range pos ltac:(lia)); lia
  end.
  - match goal with
  | |- Forall ?P (sublist ?h ?t ?q) =>
      apply (proj2 (Modern.stock_Forall_sublist P q h t ltac:(lia) ltac:(lia)));
      intros pos Hpos; pose proof (Hqueue_range pos ltac:(lia)); lia
  end.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_20_2 : maximum_profit_entail_wit_20_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockSellQueuePopping dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) with
    (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
      width (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) last_index width
    (Znth last_index (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hcell.
  assert (Haddr :
    (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) + last_index * sizeof ( INT ) =
    (&( "dp" )) + (((i - wait_days_pre) - 1) * width + last_index) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  eapply Legacy.StockSellQueuePopping_drop_tail__sell_pop_append.
  - exact ReusePreH31.
  - lia.
  - unfold Legacy.StockSellScore.
    rewrite <- (PreH28 ltac:(lia)).
    assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH33.
      destruct ReusePreH33 as [Hlen _]. rewrite Hlen. lia. }
    rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
      __default__List_Z Hsource_len).
    rewrite PreH27 in PreH2. exact PreH2.
  all: try assumption; try lia.

  - stock_finish.
  - stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_1_split_goal_1 : maximum_profit_entail_wit_21_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_1_split_goal_2 : maximum_profit_entail_wit_21_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_1_split_goal_3 : maximum_profit_entail_wit_21_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (HPendingModern : Modern.StockSellQueuePending dp_l_2 queue_l_2
    ((i - wait_days_pre) - 1) bid_price (j + 1) (j + sell_cap) head tail).
  { unfold Modern.StockSellQueuePending. split; [assumption|]. intros Hlt. lia. }
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockSellQueuePending dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  pose proof ReusePreH23 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hvalues]]]]]].
  specialize (Hvalues i ltac:(lia)).
  destruct Hvalues as [_ [_ [_ Hsell]]].
  match goal with Hcap : sell_cap = Znth _ sell_l _ |- _ => rewrite <- Hcap in Hsell end.
  assert (Hiu : j + 1 <= j + sell_cap) by lia.
  apply Legacy.StockSellQueuePending_append__sell_pop_append.
  - exact Hiu.
  - exact ReusePreH25.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_1 : maximum_profit_entail_wit_21_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_21_1_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_21_1_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_21_1_split_goal_3.
Qed.

Lemma proof_of_maximum_profit_entail_wit_21_2 : maximum_profit_entail_wit_21_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockSellQueuePopping dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (HPending : Legacy.StockSellQueuePending dp_l_2 queue_l_2 ((i - wait_days_pre) - 1)
      bid_price (j + 1) (j + sell_cap) head tail).
  { unfold Legacy.StockSellQueuePending. split.
    - exact ReusePreH30.
    - split; [lia|].
      intros Hht. unfold Legacy.StockSellScore.
      rewrite <- (PreH27 Hht).
      assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
      { unfold Legacy.StockTableShape in ReusePreH32.
        destruct ReusePreH32 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
        __default__List_Z Hsource_len).
      rewrite PreH26 in PreH1. lia. }
  assert (HReady : Legacy.StockSellQueue dp_l_2 (replace_Znth tail (j + 1) queue_l_2)
      ((i - wait_days_pre) - 1) bid_price (j + 1) (j + sell_cap) head (tail + 1)).
  { apply Legacy.StockSellQueuePending_append__sell_pop_append.
    - pose proof ReusePreH28 as Hinputs.
      unfold Legacy.StockInputsBounded in Hinputs.
      destruct Hinputs as [_ [_ [_ [_ [_ [_ Hvalues]]]]]].
      specialize (Hvalues i ltac:(lia)).
      destruct Hvalues as [_ [_ [_ Hsell]]].
      match goal with Hcap : sell_cap = Znth _ sell_l _ |- _ => rewrite <- Hcap in Hsell end. lia.
    - exact HPending. }
  Exists (replace_Znth tail (j + 1) queue_l_2) dp_l_2.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try (rewrite Zlength_replace_Znth; lia); try lia.
  pose proof (IntArray2.missing_i_merge_to_full
    (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hmerge.
  change (IntArray2.ElemArray.full
    (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) with
    (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
      width (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) in Hmerge.
  pose proof (IntArray.missing_i_merge_to_full
    ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) last_index width
    (Znth last_index (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
    (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hcell.
  assert (Haddr :
    (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) + last_index * sizeof ( INT ) =
    (&( "dp" )) + (((i - wait_days_pre) - 1) * width + last_index) * sizeof ( INT )) by lia.
  rewrite <- Haddr.
  sep_apply Hcell; try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  all: try assumption; try (rewrite Zlength_replace_Znth; lia); try lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_22_2 : maximum_profit_entail_wit_22_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) (j + 1) width
         (Znth (j + 1) (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT) + (j + 1) * sizeof (INT) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + (j + 1)) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    pose proof
      (IntArray2.missing_i_merge_to_full
         (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Htablemerge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z))
      with
      (IntArray.full
         ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) width
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z))
      in Htablemerge.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - eapply stock_sell_queue_extend_lower_neg_inf__sell_cell_progress.
    + assert (Hsrc : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
      { unfold Legacy.StockTableShape in ReusePreH30. lia. }
      rewrite <- (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
        __default__List_Z Hsrc) in PreH1.
      unfold Legacy.STOCK_NEG_INF. lia.
    + replace (j + 1 + 1) with (j + 2) by lia.
      exact ReusePreH29.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_split_goal_1 : maximum_profit_entail_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockSellQueue in ReusePreH24.
  destruct ReusePreH24 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  destruct Hentries as [_ [Hrow [_ Hbounds]]].
  unfold Legacy.StockTableShape in ReusePreH25.
  destruct ReusePreH25 as [_ Hshape].
  specialize (Hshape ((i - wait_days_pre) - 1) ltac:(lia)).
  rewrite Hshape in Hrow.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_split_goal_2 : maximum_profit_entail_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockSellQueue in ReusePreH24.
  destruct ReusePreH24 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  destruct Hentries as [Hidx _].
  exact Hidx.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_split_goal_3 : maximum_profit_entail_wit_23_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbid [Hask _]].
  rewrite <- PreH17 in Hbid.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23_split_goal_4 : maximum_profit_entail_wit_23_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbid _].
  rewrite <- PreH17 in Hbid.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_23 : maximum_profit_entail_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_23_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_23_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_23_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_23_split_goal_4.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_24 : maximum_profit_entail_wit_24.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists dp_l queue_l_2.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  pose proof
    (IntArray.missing_i_merge_to_full
       ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) best_index width
       (Znth best_index (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z) 0)
       (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT) + best_index * sizeof (INT) =
    (&( "dp" )) + (((i - wait_days_pre) - 1) * width + best_index) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l
       (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Htablemerge.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
       (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z))
    with
    (IntArray.full
       ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) width
       (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z))
    in Htablemerge.
  sep_apply Htablemerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_1 : maximum_profit_entail_wit_25_1.
Proof.

  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH25 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  pose proof ReusePreH25 as Hinput_bounds0.
  unfold Legacy.StockInputsBounded in Hinput_bounds0.
  destruct Hinput_bounds0 as [_ [_ [_ [_ [_ [_ Hinput_at0]]]]]].
  specialize (Hinput_at0 i ltac:(lia)).
  destruct Hinput_at0 as
    [Hbid_bounds0 [Hask_bound0 [_ Hsell_bounds0]]].
  rewrite <- PreH23 in Hbid_bounds0.
  rewrite <- PreH24 in Hsell_bounds0.
  pose proof ReusePreH26 as Hprogress_bounds0.
  unfold Legacy.StockSellProgress in Hprogress_bounds0.
  destruct Hprogress_bounds0 as
    [_ [_ [Hsource_eq0 [Hsource_range0 _]]]].
  assert (Hpost :
    Legacy.StockSellProgress ap_l bp_l buy_l sell_l (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      max_stock_pre wait_days_pre i (i - wait_days_pre - 1) (j-1) /\
    Legacy.StockSellQueue (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) queue_l_2 (i - wait_days_pre - 1) bid_price
      ((j-1)+2) (((j-1)+sell_cap)+1) head tail /\
    Legacy.StockTableShape (replace_Znth i (replace_Znth j sell_candidate (Znth i dp_l_2 __default__List_Z)) dp_l_2) days_pre max_stock_pre).
  { split; [|split].
  3: {
    unfold Legacy.StockTableShape in *.
    destruct ReusePreH29 as [Htable_len Hrow_len].
    split.
    - rewrite Zlength_replace_Znth. exact Htable_len.
    - intros row Hrow.
      destruct (Z.eq_dec row i) as [-> | Hneq].
      + rewrite Znth_replace_Znth_Same by lia.
        rewrite Zlength_replace_Znth.
        assert (Hi_len : 0 <= i < Zlength dp_l_2) by
          (rewrite Htable_len; lia).
        rewrite <- (Legacy.same_index_different_default i dp_l_2
          __default__List_Z) by exact Hi_len.
        apply Hrow_len. lia.
      + rewrite Znth_replace_Znth_Diff by lia.
        apply Hrow_len. lia.
  }
  2: {
    replace (j - 1 + 2) with (j + 1) by lia.
    replace (j - 1 + sell_cap + 1) with (j + sell_cap) by lia.
    assert (Hsrc: 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH29. lia. }
    unfold Legacy.StockSellQueue in *.
    destruct ReusePreH28 as [Hheadtail [Hentries [Horder Hcover]]].
    split; [exact Hheadtail |].
    split; [intros pos Hpos |].
    + specialize (Hentries pos Hpos).
      destruct Hentries as [Hnonneg [Hlen [Hninf Hrange]]].
      split; [exact Hnonneg |].
      split.
      * rewrite Znth_replace_Znth_Diff.
        -- exact Hlen.
        -- unfold Legacy.StockTableShape in ReusePreH29. lia.
        -- exact Hsrc.
        -- lia.
      * split; [| exact Hrange].
        rewrite Znth_replace_Znth_Diff.
        -- exact Hninf.
        -- unfold Legacy.StockTableShape in ReusePreH29. lia.
        -- exact Hsrc.
        -- lia.
    + split.
      * intros left right Hlr.
        destruct (Horder left right Hlr) as [Horder_stock Horder_score].
        split; [exact Horder_stock |].
        unfold Legacy.StockSellScore.
        rewrite Znth_replace_Znth_Diff.
        -- unfold Legacy.StockSellScore in Horder_score. exact Horder_score.
        -- unfold Legacy.StockTableShape in ReusePreH29. lia.
        -- exact Hsrc.
        -- lia.
      * intros candidate Hcandidate.
        destruct Hcandidate as [Hnonneg [Hlen [Hninf Hrange]]].
        unfold Legacy.StockTableShape in ReusePreH29.
        destruct ReusePreH29 as [Htable_len _].
        assert (Hsource_row :
          Znth ((i - wait_days_pre) - 1)
            (replace_Znth i
               (replace_Znth j sell_candidate
                  (Znth i dp_l_2 __default__List_Z)) dp_l_2) (@nil Z) =
          Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)).
        { rewrite Znth_replace_Znth_Diff.
          - reflexivity.
          - rewrite Htable_len. lia.
          - exact Hsrc.
          - lia. }
        try rewrite Hsource_row in Hlen, Hninf.
        unfold Legacy.StockSellScore.
        try rewrite Hsource_row.
        apply Hcover.
        repeat split; try assumption; lia.
  }
  unfold Legacy.StockSellProgress in ReusePreH26 |- *.
  destruct ReusePreH26 as [Hdone [Hday [Hsource [Hsrange
      [Hjrange [Hcopy [Hcells Hlast]]]]]]].
    unfold Legacy.StockSellQueue in ReusePreH28.
    destruct ReusePreH28 as [Hht [Hentries [Horder Hcover]]].
    pose proof (Hentries head ltac:(lia)) as Hbest.
    destruct Hbest as [Hbest0 [Hbestlen [Hbestfinite Hbestrange]]].
    rewrite <- PreH19 in Hbest0, Hbestlen, Hbestfinite, Hbestrange.
    unfold Legacy.StockDaysDone in Hdone.
    destruct Hdone as [Hshape [Hbounded [Hdone0 Hportfolio]]].
    unfold Legacy.StockTableShape in Hshape.
    destruct Hshape as [Htablelen Hrowlen].
    assert (Hasklen : Zlength ap_l = days_pre).
    { pose proof ReusePreH25 as Hinputs_copy.
      unfold Legacy.StockInputsBounded in Hinputs_copy. tauto. }
    rewrite Hasklen in Htablelen, Hrowlen, Hbounded.
    assert (Hirow : 0 <= i < Zlength dp_l_2) by (rewrite Htablelen; lia).
    assert (Hsrcrow : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2) by
      (rewrite Htablelen; lia).
    assert (Hrowi : Zlength (Znth i dp_l_2 (@nil Z)) = max_stock_pre + 1).
    { apply Hrowlen. lia. }
    assert (Hsrcdefault :
      Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z =
      Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)).
    { symmetry. apply Legacy.same_index_different_default. exact Hsrcrow. }
    assert (Hidefault :
      Znth i dp_l_2 __default__List_Z = Znth i dp_l_2 (@nil Z)).
    { symmetry. apply Legacy.same_index_different_default. exact Hirow. }
    assert (Hfeasible : Legacy.StockFeasiblePortfolio ap_l bp_l buy_l sell_l
      max_stock_pre wait_days_pre ((i - wait_days_pre) - 1) best_index
      (Znth best_index (Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)) 0)).
    { pose proof (Hportfolio ((i - wait_days_pre) - 1) best_index ltac:(lia)
        ltac:(lia)) as Hvalue.
      unfold Legacy.StockPortfolioValue in Hvalue.
      destruct Hvalue as [_ [[Hneg Hnone] | [Hfeas _]]].
      - exfalso. apply Hbestfinite. exact Hneg.
      - exact Hfeas. }
    assert (Hnewhist : Legacy.StockTradingHistory ap_l bp_l buy_l sell_l
      max_stock_pre wait_days_pre i j sell_candidate).
    { unfold Legacy.StockFeasiblePortfolio in Hfeasible.
      destruct Hfeasible as [[Hstock0 Hprofit0] |
        [last_day [[Hlastlo Hlasthi] Hhist]]].
      - subst best_index.
        exfalso. lia.
      - rewrite Hsrcdefault in PreH37.
        rewrite PreH23 in PreH37.
        replace j with (best_index - (best_index - j)) by lia.
        replace sell_candidate with
          (Znth best_index (Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)) 0 +
           (best_index - j) * Znth (i - 1) bp_l 0) by lia.
        eapply Legacy.StockTradingHistory_sell with
          (previous_day := last_day) (previous_stock := best_index)
          (previous_profit := Znth best_index
             (Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)) 0)
          (amount := best_index - j).
        + exact Hhist.
        + lia.
        + rewrite <- PreH24. lia.
        + lia. }
    assert (Hsellbounded : Legacy.STOCK_NEG_INF <= sell_candidate <= Legacy.STOCK_MAX_PROFIT).
    { pose proof (stock_trading_history_profit_bound__sell_cell_progress
        ap_l bp_l buy_l sell_l max_stock_pre wait_days_pre i j
        sell_candidate days_pre ReusePreH25 PreH8 PreH12 Hnewhist) as Hb.
      unfold Legacy.STOCK_NEG_INF, Legacy.STOCK_MAX_PROFIT in *.
      nia. }
    assert (Hshape' : Legacy.StockTableShape
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      days_pre max_stock_pre).
    { unfold Legacy.StockTableShape. split.
      - rewrite Zlength_replace_Znth. exact Htablelen.
      - intros row Hrow.
        destruct (Z.eq_dec row i) as [-> | Hneq].
        + rewrite Znth_replace_Znth_Same by exact Hirow.
          rewrite Zlength_replace_Znth, Hidefault. exact Hrowi.
        + rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
          apply Hrowlen. lia. }
    assert (Hbounded' : Legacy.StockTableValuesBounded
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      days_pre max_stock_pre).
    { unfold Legacy.StockTableValuesBounded in *.
      intros row stock Hrow Hstock.
      destruct (Z.eq_dec row i) as [-> | Hneq].
      - rewrite Znth_replace_Znth_Same by exact Hirow.
        destruct (Z.eq_dec stock j) as [-> | Hstockneq].
        + rewrite Znth_replace_Znth_Same by (rewrite Hidefault, Hrowi; lia).
          exact Hsellbounded.
        + rewrite Znth_replace_Znth_Diff by
            (try rewrite Hidefault, Hrowi; lia).
          rewrite Hidefault. apply Hbounded; lia.
      - rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
        apply Hbounded; lia. }
    assert (Hdone' : Legacy.StockDaysDone ap_l bp_l buy_l sell_l
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2)
      max_stock_pre wait_days_pre i).
    { unfold Legacy.StockDaysDone. rewrite Hasklen.
      split; [exact Hshape' |].
      split; [exact Hbounded' |]. split; [exact Hdone0 |].
      intros row stock Hrow Hstock.
      rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      apply Hportfolio; lia. }
    assert (Hsource_new : Znth ((i - wait_days_pre) - 1)
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2) (@nil Z) =
      Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)).
    { rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      reflexivity. }
    assert (Hprev_new : Znth (i - 1)
      (replace_Znth i
        (replace_Znth j sell_candidate
          (Znth i dp_l_2 __default__List_Z)) dp_l_2) (@nil Z) =
      Znth (i - 1) dp_l_2 (@nil Z)).
    { rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      reflexivity. }
  split; [exact Hdone' |]. split; [exact Hday |].
  split; [exact Hsource |]. split; [exact Hsrange |].
  split; [lia |]. split.
  - intros stock Hstock.
      rewrite Znth_replace_Znth_Same by exact Hirow.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hidefault, Hrowi; lia).
      rewrite Hidefault.
      rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      apply Hcopy. lia.
  - split.
    + intros stock Hstock.
      destruct (Z.eq_dec stock j) as [-> | Hneq].
      { rewrite Znth_replace_Znth_Same by exact Hirow.
        rewrite Znth_replace_Znth_Same by
          (rewrite Hidefault, Hrowi; lia).
        unfold Legacy.StockSellCellValue. split.
        -- exists (best_index - j). unfold Legacy.StockSellCandidate. right.
           split; [rewrite <- PreH24; lia |].
           split; [lia |]. split.
           ++ replace (j + (best_index - j)) with best_index by lia.
              try rewrite Hsource_new. exact Hbestfinite.
           ++ rewrite Znth_replace_Znth_Diff by
                (try rewrite Htablelen; lia).
              rewrite PreH37, PreH23.
              replace (j + (best_index - j)) with best_index by lia.
              rewrite Hsrcdefault. ring.
        -- intros amount candidate Hcand.
           unfold Legacy.StockSellCandidate in Hcand.
           destruct Hcand as [[Hzero Hval] |
             [Hamount [Hstockbound [Hfinite Hval]]]].
           ++ subst amount candidate.
              rewrite Hprev_new in *.
              specialize (Hcopy j ltac:(lia)).
              rewrite <- Hcopy, <- Hidefault. lia.
           ++ assert (Hwindow : Legacy.StockFiniteIndexInWindow dp_l_2 ((i - wait_days_pre) - 1)
                (j + 1) (j + sell_cap) (j + amount)).
               { unfold Legacy.StockFiniteIndexInWindow.
                 split; [lia |].
                 split.
                 - pose proof (Hrowlen ((i - wait_days_pre) - 1) ltac:(lia)) as Hsrclen.
                   rewrite Hsrclen. lia.
                 - split.
                   + try rewrite Hsource_new in Hfinite. exact Hfinite.
                   + split; [lia |].
                     rewrite PreH24. lia. }
              destruct (Hcover (j + amount) Hwindow) as
                [pos [Hpos [Hindex Hscore]]].
              assert (Hheadscore : Legacy.StockSellScore dp_l_2 ((i - wait_days_pre) - 1) bid_price
                (Znth pos queue_l_2 0) <=
                Legacy.StockSellScore dp_l_2 ((i - wait_days_pre) - 1) bid_price best_index).
              { destruct (Z.eq_dec pos head) as [-> | Hneqpos].
                - rewrite PreH19. lia.
                - destruct (Horder head pos ltac:(lia)) as [_ Hord].
                  rewrite <- PreH19 in Hord. lia. }
              unfold Legacy.StockSellScore in *.
              try rewrite Hsource_new in Hval.
              rewrite <- PreH23 in Hval.
              rewrite Hsrcdefault in PreH37.
              lia. }
      { rewrite Znth_replace_Znth_Same by exact Hirow.
         rewrite Znth_replace_Znth_Diff by
           (try rewrite Hidefault, Hrowi; lia).
         rewrite Hidefault.
         rewrite Hidefault in Hsource_new, Hprev_new.
         specialize (Hcells stock ltac:(lia)).
         unfold Legacy.StockSellCellValue, Legacy.StockSellCandidate in *.
         try rewrite Hsource_new, Hprev_new.
         exact Hcells. }
    + rewrite Znth_replace_Znth_Same by exact Hirow.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Hidefault, Hrowi; lia).
      rewrite Hidefault.
      rewrite Hidefault in Hprev_new.
      rewrite Hprev_new. exact Hlast.

  all: try stock_finish.

  }
  destruct Hpost as [Hprogress_new [Hqueue_new Hshape_new]].
  Exists queue_l_2 (replace_Znth i
    (replace_Znth j sell_candidate
      (Znth i dp_l_2 __default__List_Z)) dp_l_2).
  split_pure_spatial.
  - pose proof
    (IntArray.missing_i_merge_to_full
       ((&( "dp" )) + i * width * sizeof (INT)) j width sell_candidate
       (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
    (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       (&( "dp" )) i (days_pre + 1) width dp_l_2
       (replace_Znth j sell_candidate
         (Znth i dp_l_2 __default__List_Z))) as Htablemerge.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr (&( "dp" )) width i) width
       (replace_Znth j sell_candidate
         (Znth i dp_l_2 __default__List_Z)))
    with
    (IntArray.full
       ((&( "dp" )) + i * width * sizeof (INT)) width
       (replace_Znth j sell_candidate
         (Znth i dp_l_2 __default__List_Z)))
    in Htablemerge.
  sep_apply Htablemerge; try lia.
  cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try stock_finish.

Qed.

Lemma proof_of_maximum_profit_entail_wit_25_2 : maximum_profit_entail_wit_25_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH25 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (Hprogress' : Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) (j - 1)).
  { unfold Legacy.StockSellProgress in ReusePreH26 |- *.
    destruct ReusePreH26 as [Hdone [Hday [Hsource [Hsrange
      [Hjrange [Hcopy [Hcells Hlast]]]]]]].
    unfold Legacy.StockSellQueue in ReusePreH28.
    destruct ReusePreH28 as [Hht [Hentries [Horder Hcover]]].
    unfold Legacy.StockTableShape in ReusePreH29.
    destruct ReusePreH29 as [Htablelen Hrowlen].
    assert (Hsrcrow : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2) by
      (rewrite Htablelen; lia).
    assert (Hirow : 0 <= i < Zlength dp_l_2) by
      (rewrite Htablelen; lia).
    assert (Hsrcdefault :
      Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z =
      Znth ((i - wait_days_pre) - 1) dp_l_2 (@nil Z)).
    { symmetry. apply Legacy.same_index_different_default. exact Hsrcrow. }
    assert (Hidefault :
      Znth i dp_l_2 __default__List_Z = Znth i dp_l_2 (@nil Z)).
    { symmetry. apply Legacy.same_index_different_default. exact Hirow. }
    split; [exact Hdone |].
    split; [exact Hday |].
    split; [exact Hsource |].
    split; [exact Hsrange |].
    split; [lia |].
    split.
    - intros stock Hstock. apply Hcopy. lia.
    - split.
      + intros stock Hstock.
        destruct (Z.eq_dec stock j) as [-> | Hneq].
        { unfold Legacy.StockSellCellValue, Legacy.StockSellCandidate.
          split.
          - exists 0. left. split; [lia |]. apply Hcopy. lia.
          - intros amount candidate Hcand.
            destruct Hcand as [[Hzero Hval] |
              [Hamount [Hstockbound [Hfinite Hval]]]].
            + subst amount candidate. specialize (Hcopy j ltac:(lia)). lia.
            + assert (Hwindow : Legacy.StockFiniteIndexInWindow dp_l_2 ((i - wait_days_pre) - 1)
                 (j + 1) (j + sell_cap) (j + amount)).
              { unfold Legacy.StockFiniteIndexInWindow.
                split; [lia |]. split.
                - pose proof (Hrowlen ((i - wait_days_pre) - 1) ltac:(lia)) as Hsrclen.
                  rewrite Hsrclen. lia.
                - split; [exact Hfinite |].
                  split; [lia |]. rewrite PreH24. lia. }
              destruct (Hcover (j + amount) Hwindow) as
                [pos [Hpos [Hindex Hscore]]].
              assert (Hheadscore : Legacy.StockSellScore dp_l_2 ((i - wait_days_pre) - 1) bid_price
                (Znth pos queue_l_2 0) <=
                Legacy.StockSellScore dp_l_2 ((i - wait_days_pre) - 1) bid_price best_index).
              { destruct (Z.eq_dec pos head) as [-> | Hneqpos].
                - rewrite PreH19. lia.
                - destruct (Horder head pos ltac:(lia)) as [_ Hord].
                  rewrite <- PreH19 in Hord. lia. }
              unfold Legacy.StockSellScore in *.
              rewrite Hsrcdefault in PreH37.
              rewrite Hidefault in PreH1.
              rewrite <- PreH23 in Hval.
              lia. }
        { apply Hcells. lia. }
      + exact Hlast. }
  pose proof ReusePreH25 as Hinputs_copy.
  unfold Legacy.StockInputsBounded in Hinputs_copy.
  destruct Hinputs_copy as [_ [_ [_ [_ [_ [_ Hinput_at]]]]]].
  specialize (Hinput_at i ltac:(lia)).
  destruct Hinput_at as [Hbid_bounds [Hask_bounds [_ Hsell_bounds]]].
  rewrite <- PreH23 in Hbid_bounds.
  rewrite <- PreH24 in Hsell_bounds.
  assert (Hsource_pos : 0 < ((i - wait_days_pre) - 1)).
  { unfold Legacy.StockSellProgress in ReusePreH26. tauto. }
  assert (Hsource_eq : ((i - wait_days_pre) - 1) = i - wait_days_pre - 1).
  { unfold Legacy.StockSellProgress in ReusePreH26. tauto. }
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  2: (split_pures; try stock_weaken).
  all: try (dump_pre_spatial; try stock_weaken).
  all: try assumption; try lia.
  pose proof
    (IntArray.missing_i_merge_to_full
       ((&( "dp" )) + i * width * sizeof (INT)) j width
       (Znth j (Znth i dp_l_2 __default__List_Z) 0)
       (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
  assert (Hcell_addr :
    (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
    (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
  rewrite <- Hcell_addr.
  sep_apply Hrowmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof
    (IntArray2.missing_i_merge_to_full
       (&( "dp" )) i (days_pre + 1) width dp_l_2
       (Znth i dp_l_2 __default__List_Z)) as Htablemerge.
  change
    (IntArray2.ElemArray.full
       (IntArray2.row_addr (&( "dp" )) width i) width
       (Znth i dp_l_2 __default__List_Z))
    with
    (IntArray.full
       ((&( "dp" )) + i * width * sizeof (INT)) width
       (Znth i dp_l_2 __default__List_Z))
    in Htablemerge.
  sep_apply Htablemerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
  Unshelve.
  - replace (j - 1 + 2) with (j + 1) by lia.
    replace (j - 1 + sell_cap + 1) with (j + sell_cap) by lia.
    exact ReusePreH28.
  all: try assumption; try lia; try exact Hprogress'.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3_split_goal_1 : maximum_profit_entail_wit_25_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  replace (j - 1 + 2) with (j + 1) by lia.
  replace (j - 1 + sell_cap + 1) with (j + sell_cap) by lia.
  exact ReusePreH24.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3_split_goal_2 : maximum_profit_entail_wit_25_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [Hasklen [Hbidlen [Hbuylen [Hselllen
    [Hdays [Hmaxstock Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [Hbid [Hask [Hbuy Hsell]]].
  unfold Legacy.StockSellProgress in ReusePreH23 |- *.
  destruct ReusePreH23 as [Hdone [Hday [Hsource [Hsrange
    [Hjrange [Hcopy [Hcells Hlast]]]]]]].
  split; [exact Hdone |].
  split; [exact Hday |].
  split; [exact Hsource |].
  split; [exact Hsrange |].
  split; [lia |].
  split.
  - intros stock Hstock. apply Hcopy. lia.
  - split.
    + intros stock Hstock.
    destruct (Z.eq_dec stock j) as [-> | Hneq].
      * unfold Legacy.StockSellCellValue, Legacy.StockSellCandidate.
        split.
        -- exists 0. left. split; [lia |]. apply Hcopy. lia.
        -- intros amount candidate Hcand.
           destruct Hcand as [[Hzero Hval] |
             [Hamount [Hstockbound [Hfinite Hval]]]].
           ++ subst amount candidate. specialize (Hcopy j ltac:(lia)). lia.
           ++ unfold Legacy.StockSellQueue in ReusePreH24.
              destruct ReusePreH24 as [_ [_ [_ Hcover]]].
              assert (Hwindow : Legacy.StockFiniteIndexInWindow dp_l_2 ((i - wait_days_pre) - 1)
                (j + 1) (j + sell_cap) (j + amount)).
              { unfold Legacy.StockTableShape in ReusePreH25.
                destruct ReusePreH25 as [_ Hrowlen].
                unfold Legacy.StockFiniteIndexInWindow.
                split; [lia |]. split.
                - pose proof (Hrowlen ((i - wait_days_pre) - 1) ltac:(lia)) as Hsrclen.
                  rewrite Hsrclen. lia.
                - split; [exact Hfinite |].
                  split; [lia |]. rewrite PreH18. lia. }
              destruct (Hcover (j + amount) Hwindow) as [pos [Hpos _]].
              lia.
      * apply Hcells. lia.
    + exact Hlast.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3_split_goal_3 : maximum_profit_entail_wit_25_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold Legacy.StockSellProgress in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3_split_goal_4 : maximum_profit_entail_wit_25_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold Legacy.StockSellProgress in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3_split_goal_5 : maximum_profit_entail_wit_25_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold Legacy.StockSellProgress in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3_split_goal_6 : maximum_profit_entail_wit_25_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH22 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 1 ) (j + sell_cap ) head tail )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH22.
  destruct ReusePreH22 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [[Hbidlo Hbidhi] [Hask [Hbuy [Hselllo Hsellhi]]]].
  unfold Legacy.StockSellProgress in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [Hjrange _]]]]].
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_25_3 : maximum_profit_entail_wit_25_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_25_3_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_25_3_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_25_3_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_25_3_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_25_3_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_25_3_split_goal_6.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_split_goal_1 : maximum_profit_entail_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  unfold Legacy.StockBuyQueue.
  split; [lia |].
  split.
  - intros pos Hpos. lia.
  - split.
    + intros left right Hpositions. lia.
    + intros candidate Hcandidate.
      unfold Legacy.StockFiniteIndexInWindow in Hcandidate.
      destruct Hcandidate as [Hnonneg [_ [_ [_ Hupper]]]].
      lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_split_goal_2 : maximum_profit_entail_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  unfold Legacy.StockSellProgress in ReusePreH28.
  destruct ReusePreH28 as [Hdone [Hday [Hsource [Hsrange
    [Hjrange [Hcopy [Hsell Hmaxeq]]]]]]].
  unfold Legacy.StockBuyProgress.
  split; [exact Hdone |].
  split; [exact Hday |].
  split; [reflexivity |].
  split; [try rewrite <- Hsource; exact Hsrange |].
  split; [lia |].
  split.
  - intros stock Hstock.
    assert (stock = 0) by lia. subst stock.
    pose proof (Hsell 0 ltac:(lia)) as Hsell0.
    try rewrite Hsource in Hsell0.
    unfold Legacy.StockBuyCellValue, Legacy.StockBuyCandidate.
    split.
    + split.
      * exists 0. left. split; [lia | exact Hsell0].
      * intros amount candidate Hcandidate.
        destruct Hcandidate as [[Hamount Hsellcandidate] | Hpositive].
        -- subst amount.
           destruct Hsell0 as [_ Hmaximal].
           destruct Hsellcandidate as [[sell_amount Hsellcandidate] _].
           apply Hmaximal with (amount := sell_amount).
           exact Hsellcandidate.
        -- lia.
    + exists (Znth 0 (Znth i dp_l_2 nil) 0). exact Hsell0.
  - intros stock Hstock.
    destruct (Z.eq_dec stock max_stock_pre) as [Heq | Hneq].
    + subst stock.
      unfold Legacy.StockSellCellValue, Legacy.StockSellCandidate.
      split.
      * exists 0. left. split; [lia | exact Hmaxeq].
      * intros amount candidate Hcandidate.
        destruct Hcandidate as [[Hamount Hcandidate] | Hpositive].
        -- subst amount candidate. lia.
        -- lia.
    + try rewrite <- Hsource. apply Hsell. lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_split_goal_3 : maximum_profit_entail_wit_26_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH27.
  destruct ReusePreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [_ [_ [Hbuy _]]]. lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_split_goal_4 : maximum_profit_entail_wit_26_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH27.
  destruct ReusePreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [_ [_ [Hbuy _]]]. lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_split_goal_5 : maximum_profit_entail_wit_26_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH27.
  destruct ReusePreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [_ [Hask _]]. lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26_split_goal_6 : maximum_profit_entail_wit_26_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockSellProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockSellQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) bid_price (j + 2 ) ((j + sell_cap ) + 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH27.
  destruct ReusePreH27 as [_ [_ [_ [_ [_ [_ Hinputs]]]]]].
  specialize (Hinputs i ltac:(lia)).
  destruct Hinputs as [Hbidask _]. lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_26 : maximum_profit_entail_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_26_split_goal_6.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27_split_goal_1 : maximum_profit_entail_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH9 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price ((j - buy_cap ) - 1 ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  unfold Legacy.StockBuyQueueExpiring. left.
  try rewrite <- ReusePreH9. exact ReusePreH27.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_27 : maximum_profit_entail_wit_27.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_27_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_28_split_goal_1 : maximum_profit_entail_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockBuyQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  try rewrite <- ReusePreH14.
  unfold Legacy.StockBuyQueueExpiring, Legacy.StockBuyQueue in *.
  destruct ReusePreH32 as [Hqueue | Hqueue].
  - right.
    destruct Hqueue as [Hbounds [Hentries [Hordered Hcovers]]].
    split; [lia |].
    split.
    + intros pos Hpos.
      pose proof (Hentries pos ltac:(lia)) as Hpos_entry.
      pose proof (Hentries head ltac:(lia)) as Hhead_entry.
      pose proof (Hordered head pos ltac:(lia)) as Hhead_before.
      destruct Hpos_entry as [Hpos_nonneg [Hpos_len [Hpos_valid Hpos_range]]].
      destruct Hhead_entry as [_ [_ [_ Hhead_range]]].
      destruct Hhead_before as [Hindices _].
      destruct Hpos_range as [_ Hpos_upper].
      destruct Hhead_range as [Hhead_lower Hhead_upper].
      repeat split; try assumption; lia.
    + split.
      * intros left right0 Hpositions. apply Hordered. lia.
      * intros candidate Hcandidate.
      destruct Hcandidate as [Hnonneg [Hinrow [Hvalid Hrange]]].
      specialize (Hcovers candidate).
      assert (Holdrange :
        0 <= candidate /\
        candidate < Zlength (Znth ((i - wait_days_pre) - 1) dp_l_2 nil) /\
        Znth candidate (Znth ((i - wait_days_pre) - 1) dp_l_2 nil) 0 <> Legacy.STOCK_NEG_INF /\
        j - buy_cap - 1 <= candidate <= j - 2) by
        (repeat split; try assumption; lia).
      specialize (Hcovers Holdrange).
      destruct Hcovers as [pos [Hpos [Hcandidate_le Hscore]]].
      destruct Hpos as [Hpos_lower Hpos_upper].
      destruct Hrange as [Hcandidate_lower Hcandidate_upper].
      pose proof (Hentries head ltac:(lia)) as Hhead_entry.
      destruct Hhead_entry as [_ [_ [_ Hhead_range]]].
      destruct Hhead_range as [Hhead_lower Hhead_upper].
      assert (head < pos).
      { destruct (Z.eq_dec pos head) as [Heq | Hneq].
        - subst pos. lia.
        - lia. }
      exists pos. split; [lia |].
      split; assumption.
  - destruct Hqueue as [_ [Hentries _]].
    specialize (Hentries head ltac:(lia)).
      destruct Hentries as [_ [_ [_ Hrange]]].
      lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_28 : maximum_profit_entail_wit_28.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_28_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_29_1_split_goal_1 : maximum_profit_entail_wit_29_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH13 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  try rewrite <- ReusePreH13.
  unfold Legacy.StockBuyQueueExpiring in ReusePreH31.
  unfold Legacy.StockBuyQueue in *.
  destruct ReusePreH31 as [Hqueue | Hqueue];
    destruct Hqueue as [Hbounds [Hentries [Hordered Hcovers]]].
  - split; [exact Hbounds |].
    split.
    + intros pos Hpos. lia.
    + split.
      * intros left right Hpositions. lia.
      * intros candidate Hcandidate. apply Hcovers.
      unfold Legacy.StockFiniteIndexInWindow in *.
      destruct Hcandidate as [Hnonneg [Hinrow [Hvalid Hrange]]].
      repeat split; try assumption; lia.
  - split; [exact Hbounds |].
    split.
    + intros pos Hpos. lia.
    + split.
      * intros left right Hpositions. lia.
      * exact Hcovers.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_29_1 : maximum_profit_entail_wit_29_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_29_1_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_29_2_split_goal_1 : maximum_profit_entail_wit_29_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (((i - wait_days_pre) - 1) = ((i - wait_days_pre ) - 1 ))) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockBuyQueueExpiring dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  try rewrite <- ReusePreH14.
  unfold Legacy.StockBuyQueueExpiring in ReusePreH32.
  destruct ReusePreH32 as [Hqueue | Hqueue]; [| exact Hqueue].
  unfold Legacy.StockBuyQueue in *.
  destruct Hqueue as [Hbounds [Hentries [Hordered Hcovers]]].
  split; [exact Hbounds |].
  split.
  - intros pos Hpos.
    pose proof (Hentries pos Hpos) as Hpos_entry.
    pose proof (Hentries head ltac:(lia)) as Hhead_entry.
    destruct Hpos_entry as [Hpos_nonneg [Hpos_len [Hpos_valid Hpos_range]]].
    destruct Hhead_entry as [_ [_ [_ Hhead_range]]].
    assert (j - buy_cap <= Znth pos queue_l_2 0).
    + destruct (Z.eq_dec pos head) as [Heq | Hneq].
      * subst pos. lia.
      * pose proof (Hordered head pos ltac:(lia)) as Hhead_before.
        destruct Hhead_before as [Hindices _]. lia.
    + repeat split; try assumption; lia.
  - split.
    + exact Hordered.
    + intros candidate Hcandidate.
      destruct Hcandidate as [Hnonneg [Hinrow [Hvalid Hrange]]].
      apply Hcovers.
      repeat split; try assumption; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_29_2 : maximum_profit_entail_wit_29_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_29_2_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_30_1 : maximum_profit_entail_wit_30_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyQueue dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists queue_l dp_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l
      (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
      (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
        width (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) (j - 1) width
      (Znth (j - 1) (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z) 0)
      (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hcell.
    assert (Haddr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) +
        (j - 1) * sizeof ( INT ) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + (j - 1)) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    + unfold Legacy.StockBuyQueue in ReusePreH30.
      destruct ReusePreH30 as [_ [Hvalid _]].
      specialize (Hvalid (tail - 1) ltac:(lia)).
      unfold Legacy.StockFiniteIndexInWindow in Hvalid. tauto.
    + unfold Legacy.StockBuyQueue in ReusePreH30.
      destruct ReusePreH30 as [_ [Hvalid _]].
      specialize (Hvalid (tail - 1) ltac:(lia)).
      destruct Hvalid as [_ [Hlt _]].
      unfold Legacy.StockTableShape in ReusePreH31.
      destruct ReusePreH31 as [_ Hrows].
      specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)). rewrite Hrows in Hlt. lia.
    + eapply (Legacy.StockBuyQueue_begin_popping__buy_pop_append
        dp_l queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 1)
        head tail).
      * lia.
      * unfold Legacy.StockTableShape in ReusePreH31.
        destruct ReusePreH31 as [_ Hrows].
        specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)). rewrite Hrows. lia.
      * assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l).
        { unfold Legacy.StockTableShape in ReusePreH31.
          destruct ReusePreH31 as [Hlen _]. rewrite Hlen. lia. }
        rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l
          __default__List_Z Hsource_len).
        unfold Legacy.STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
      * replace (j - 1 - 1) with (j - 2) by lia. exact ReusePreH30.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_30_2 : maximum_profit_entail_wit_30_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH28 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockBuyQueue dp_l queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l
      (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
      (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
        width (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) (j - 1) width
      (Znth (j - 1) (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z) 0)
      (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hcell.
    assert (Haddr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) +
        (j - 1) * sizeof ( INT ) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + (j - 1)) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    eapply (Legacy.StockBuyQueue_begin_popping__buy_pop_append
      dp_l queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 1)
      head tail).
    + lia.
    + unfold Legacy.StockTableShape in ReusePreH31.
      destruct ReusePreH31 as [_ Hrows].
      specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)). rewrite Hrows. lia.
    + assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l).
      { unfold Legacy.StockTableShape in ReusePreH31.
        destruct ReusePreH31 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l
        __default__List_Z Hsource_len).
      unfold Legacy.STOCK_NEG_INF. rewrite <- PreH3. exact PreH2.
    + replace (j - 1 - 1) with (j - 2) by lia. exact ReusePreH30.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_31_1 : maximum_profit_entail_wit_31_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH31 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockBuyQueuePopping dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH34 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
        width (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) last_index width
      (Znth last_index (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hcell.
    assert (Haddr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) +
        last_index * sizeof ( INT ) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + last_index) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    + unfold Legacy.StockBuyQueuePopping in ReusePreH33.
      destruct ReusePreH33 as [_ [_ [Hentries _]]].
      specialize (Hentries (tail - 1 - 1) ltac:(lia)).
      unfold Legacy.StockFiniteIndexInWindow in Hentries. tauto.
    + unfold Legacy.StockBuyQueuePopping in ReusePreH33.
      destruct ReusePreH33 as [_ [_ [Hentries _]]].
      specialize (Hentries (tail - 1 - 1) ltac:(lia)).
      unfold Legacy.StockFiniteIndexInWindow in Hentries.
      unfold Legacy.StockTableShape in ReusePreH34.
      destruct ReusePreH34 as [_ Hrowlen].
      pose proof (Hrowlen ((i - wait_days_pre) - 1) ltac:(lia)) as Hsource_len.
      lia.
    + eapply Legacy.StockBuyQueuePopping_drop_tail__buy_pop_append.
      * exact ReusePreH33.
      * lia.
      * unfold Legacy.StockBuyScore.
        assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
        { unfold Legacy.StockTableShape in ReusePreH34.
          destruct ReusePreH34 as [Hlen _]. rewrite Hlen. lia. }
        rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
          __default__List_Z Hsource_len).
        rewrite <- PreH29.
        rewrite (PreH30 PreH3) in PreH2. exact PreH2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_31_2 : maximum_profit_entail_wit_31_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH31 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockBuyQueuePopping dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH34 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
        width (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) last_index width
      (Znth last_index (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hcell.
    assert (Haddr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) +
        last_index * sizeof ( INT ) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + last_index) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    eapply Legacy.StockBuyQueuePopping_drop_tail__buy_pop_append.
    + exact ReusePreH33.
    + lia.
    + unfold Legacy.StockBuyScore.
      assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
      { unfold Legacy.StockTableShape in ReusePreH34.
        destruct ReusePreH34 as [Hlen _]. rewrite Hlen. lia. }
      rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
        __default__List_Z Hsource_len).
      rewrite <- PreH29.
      rewrite (PreH30 PreH3) in PreH2. exact PreH2.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_1_split_goal_1 : maximum_profit_entail_wit_32_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_1_split_goal_2 : maximum_profit_entail_wit_32_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_1_split_goal_3 : maximum_profit_entail_wit_32_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (HPendingModern : Modern.StockBuyQueuePending dp_l_2 queue_l_2
    ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 1) head tail).
  { unfold Modern.StockBuyQueuePending. split; [assumption|]. intros Hlt. lia. }
  stock_weaken.
  apply Legacy.StockBuyQueuePending_append__buy_pop_append.
  - stock_restore.
  - assert (Hinputs : Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre) by stock_restore.
    unfold Legacy.StockInputsBounded in Hinputs.
    destruct Hinputs as [_ [_ [_ [_ [_ [_ Hvalues]]]]]].
    specialize (Hvalues i ltac:(lia)). lia.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_1 : maximum_profit_entail_wit_32_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_32_1_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_32_1_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_32_1_split_goal_3.
Qed.

Lemma proof_of_maximum_profit_entail_wit_32_2 : maximum_profit_entail_wit_32_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH30 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH31 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH32 : (Legacy.StockBuyQueuePopping dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH33 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (HPending : Legacy.StockBuyQueuePending dp_l_2 queue_l_2
      ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 1) head tail).
  {
    unfold Legacy.StockBuyQueuePending.
    split; [exact ReusePreH32 |].
    split; [lia |].
    intros Hlt.
    unfold Legacy.StockBuyScore.
    assert (Hsource_len : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
    { unfold Legacy.StockTableShape in ReusePreH33.
      destruct ReusePreH33 as [Hlen _]. rewrite Hlen. lia. }
    rewrite (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
      __default__List_Z Hsource_len).
    rewrite <- (PreH29 Hlt).
    rewrite <- PreH28.
    lia.

  }
  assert (HReady : Legacy.StockBuyQueue dp_l_2 (replace_Znth tail (j - 1) queue_l_2)
      ((i - wait_days_pre) - 1) ask_price (j - buy_cap) (j - 1) head (tail + 1)).
  { apply Legacy.StockBuyQueuePending_append__buy_pop_append.
    - exact HPending.
    - pose proof ReusePreH30 as Hinputs.
      unfold Legacy.StockInputsBounded in Hinputs.
      destruct Hinputs as [_ [_ [_ [_ [_ [_ Hvalues]]]]]].
      specialize (Hvalues i ltac:(lia)). lia. }
  Exists (replace_Znth tail (j - 1) queue_l_2) dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hmerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ))
        width (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) in Hmerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT )) last_index width
      (Znth last_index (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
      (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hcell.
    assert (Haddr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof ( INT ) +
        last_index * sizeof ( INT ) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + last_index) * sizeof ( INT )) by lia.
    rewrite <- Haddr.
    sep_apply Hcell; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try (rewrite Zlength_replace_Znth; lia); try lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_33_2 : maximum_profit_entail_wit_33_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) (j - 1) width
         (Znth (j - 1) (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z) 0)
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT) + (j - 1) * sizeof (INT) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + (j - 1)) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    pose proof
      (IntArray2.missing_i_merge_to_full
         (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l_2
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z)) as Htablemerge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z))
      with
      (IntArray.full
         ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) width
         (Znth ((i - wait_days_pre) - 1) dp_l_2 __default__List_Z))
      in Htablemerge.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken).
    all: try assumption; try lia.
    eapply Legacy.StockBuyQueue_extend_invalid__buy_cell_progress.
    + replace (j - 1 - 1) with (j - 2) by lia.
      exact ReusePreH29.
    + unfold Legacy.StockTableShape in ReusePreH30.
      destruct ReusePreH30 as [Htablelen Hrows].
      specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)).
      lia.
    + assert (Hsrc : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
      { pose proof ReusePreH30 as Hshape.
        unfold Legacy.StockTableShape in Hshape.
        destruct Hshape as [Htablelen _]. lia. }
      rewrite <- (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
        __default__List_Z Hsrc) in PreH1.
      unfold Legacy.STOCK_NEG_INF. lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_34_split_goal_1 : maximum_profit_entail_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyQueue in ReusePreH25.
  destruct ReusePreH25 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  unfold Legacy.StockFiniteIndexInWindow in Hentries.
  destruct Hentries as [Hidx [_ [_ [_ Hupper]]]].
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_34_split_goal_2 : maximum_profit_entail_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockBuyQueue in ReusePreH25.
  destruct ReusePreH25 as [_ [Hentries _]].
  specialize (Hentries head ltac:(lia)).
  unfold Legacy.StockFiniteIndexInWindow in Hentries.
  destruct Hentries as [Hidx _].
  exact Hidx.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_34_split_goal_3 : maximum_profit_entail_wit_34_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbidask [Hask _]].
  rewrite <- PreH18 in Hask.
  exact Hask.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_34_split_goal_4 : maximum_profit_entail_wit_34_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [_ [_ Hinput]]]]]].
  specialize (Hinput i ltac:(lia)).
  destruct Hinput as [Hbidask _].
  rewrite <- PreH18 in Hbidask.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_34 : maximum_profit_entail_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_34_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_34_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_34_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_34_split_goal_4.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_35 : maximum_profit_entail_wit_35.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH27 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  Exists dp_l queue_l_2.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) best_index width
         (Znth best_index (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z) 0)
         (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      (&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT) + best_index * sizeof (INT) =
      (&( "dp" )) + (((i - wait_days_pre) - 1) * width + best_index) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    pose proof
      (IntArray2.missing_i_merge_to_full
         (&( "dp" )) ((i - wait_days_pre) - 1) (days_pre + 1) width dp_l
         (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z)) as Htablemerge.
    change
      (IntArray2.ElemArray.full
         (IntArray2.row_addr (&( "dp" )) width ((i - wait_days_pre) - 1)) width
         (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z))
      with
      (IntArray.full
         ((&( "dp" )) + ((i - wait_days_pre) - 1) * width * sizeof (INT)) width
         (Znth ((i - wait_days_pre) - 1) dp_l __default__List_Z))
      in Htablemerge.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken); try assumption; try lia; try reflexivity.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_1 : maximum_profit_entail_wit_36_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (Hsrc : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
  { unfold Legacy.StockTableShape in ReusePreH30. lia. }
  assert (Hirow : 0 <= i < Zlength dp_l_2).
  { unfold Legacy.StockTableShape in ReusePreH30. lia. }
  rewrite <- (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
    __default__List_Z Hsrc) in PreH38.
  rewrite <- (Legacy.same_index_different_default i dp_l_2
    __default__List_Z Hirow) in PreH1.
  assert (Hcell : Legacy.StockBuyCellValue ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre i ((i - wait_days_pre) - 1) j buy_candidate).
  { eapply Legacy.StockBuyCellValue_improve__buy_cell_progress with
      (queue := queue_l_2) (price := ask_price) (buy_cap := buy_cap)
      (head := head) (tail := tail) (best := best_index); eauto; try lia. }
  pose proof (Legacy.StockBuyProgress_replace_improved_step__buy_semantics
    ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
    i ((i - wait_days_pre) - 1) j buy_candidate ReusePreH26 ltac:(lia) ReusePreH30 ReusePreH27
    ltac:(lia) ltac:(lia) Hcell) as Hstep.
  cbn in Hstep.
  destruct Hstep as [Hprogress Hshape].
  rewrite (Legacy.same_index_different_default i dp_l_2
    __default__List_Z Hirow) in Hprogress, Hshape.
  assert (HqueueNext : Legacy.StockBuyQueue
    (replace_Znth i
      (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z))
      dp_l_2)
    queue_l_2 ((i - wait_days_pre) - 1) ask_price
    (j + 1 - buy_cap - 1) (j + 1 - 2) head tail).
  { replace (j + 1 - buy_cap - 1) with (j - buy_cap) by lia.
    replace (j + 1 - 2) with (j - 1) by lia.
    eapply Legacy.StockBuyQueue_replace_other_row__buy_cell_progress; eauto; lia. }
  pose proof ReusePreH26 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbidask [Hask [Hbuy _]]].
  rewrite <- PreH21 in Hbidask, Hask.
  rewrite <- PreH22 in Hbuy.
  pose proof ReusePreH27 as Hprogress0.
  unfold Legacy.StockBuyProgress in Hprogress0.
  destruct Hprogress0 as [_ [_ [Hsource [Hsrange _]]]].
  Exists queue_l_2 (replace_Znth i
    (replace_Znth j buy_candidate (Znth i dp_l_2 __default__List_Z))
    dp_l_2).
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + i * width * sizeof (INT)) j width buy_candidate
         (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    pose proof
      (IntArray2.missing_i_merge_to_full (&( "dp" )) i (days_pre + 1) width dp_l_2
         (replace_Znth j buy_candidate
           (Znth i dp_l_2 __default__List_Z))) as Htablemerge.
    change
      (IntArray2.ElemArray.full (IntArray2.row_addr (&( "dp" )) width i) width
        (replace_Znth j buy_candidate
          (Znth i dp_l_2 __default__List_Z)))
      with
      (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width
        (replace_Znth j buy_candidate
          (Znth i dp_l_2 __default__List_Z))) in Htablemerge.
    sep_apply Htablemerge; try lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken); try exact HqueueNext; try exact Hprogress;
      try exact Hshape; try assumption; try lia; try reflexivity.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_2 : maximum_profit_entail_wit_36_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH26 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH29 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH30 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  assert (Hsrc : 0 <= ((i - wait_days_pre) - 1) < Zlength dp_l_2).
  { unfold Legacy.StockTableShape in ReusePreH30. lia. }
  assert (Hirow : 0 <= i < Zlength dp_l_2).
  { unfold Legacy.StockTableShape in ReusePreH30. lia. }
  rewrite <- (Legacy.same_index_different_default ((i - wait_days_pre) - 1) dp_l_2
    __default__List_Z Hsrc) in PreH38.
  rewrite <- (Legacy.same_index_different_default i dp_l_2
    __default__List_Z Hirow) in PreH1.
  assert (Hcell : Legacy.StockBuyCellValue ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre i ((i - wait_days_pre) - 1) j (Znth j (Znth i dp_l_2 nil) 0)).
  { eapply Legacy.StockBuyCellValue_keep__buy_cell_progress with
      (queue := queue_l_2) (price := ask_price) (buy_cap := buy_cap)
      (head := head) (tail := tail) (best := best_index)
      (value := buy_candidate); eauto; try lia. }
  pose proof (Legacy.StockBuyProgress_step_same__buy_cell_progress
    ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j
    ReusePreH27 ltac:(lia) Hcell) as Hnext.
  pose proof ReusePreH26 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbidask [Hask [Hbuy _]]].
  pose proof ReusePreH27 as Hprogress.
  unfold Legacy.StockBuyProgress in Hprogress.
  destruct Hprogress as [_ [_ [Hsource [Hsrange _]]]].
  rewrite <- PreH21 in Hbidask, Hask.
  rewrite <- PreH22 in Hbuy.
  assert (HqueueNext : Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price
    (j + 1 - buy_cap - 1) (j + 1 - 2) head tail).
  { replace (j + 1 - buy_cap - 1) with (j - buy_cap) by lia.
    replace (j + 1 - 2) with (j - 1) by lia. exact ReusePreH29. }
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof
      (IntArray.missing_i_merge_to_full
         ((&( "dp" )) + i * width * sizeof (INT)) j width
         (Znth j (Znth i dp_l_2 __default__List_Z) 0)
         (Znth i dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Hcell_addr :
      (&( "dp" )) + i * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (i * width + j) * sizeof (INT)) by lia.
    rewrite <- Hcell_addr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    pose proof
      (IntArray2.missing_i_merge_to_full (&( "dp" )) i (days_pre + 1) width dp_l_2
         (Znth i dp_l_2 __default__List_Z)) as Htablemerge.
    change
      (IntArray2.ElemArray.full (IntArray2.row_addr (&( "dp" )) width i) width
        (Znth i dp_l_2 __default__List_Z))
      with
      (IntArray.full ((&( "dp" )) + i * width * sizeof (INT)) width
        (Znth i dp_l_2 __default__List_Z)) in Htablemerge.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: (dump_pre_spatial; try stock_weaken); try exact HqueueNext; try exact Hnext;
      try assumption; try lia; try reflexivity.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3_split_goal_1 : maximum_profit_entail_wit_36_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  replace (j + 1 - buy_cap - 1) with (j - buy_cap) by lia.
  replace (j + 1 - 2) with (j - 1) by lia.
  exact ReusePreH25.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3_split_goal_2 : maximum_profit_entail_wit_36_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (Hrowlen : j < Zlength (Znth ((i - wait_days_pre) - 1) dp_l_2 nil)).
  { unfold Legacy.StockTableShape in ReusePreH26.
    destruct ReusePreH26 as [_ Hrows].
    specialize (Hrows ((i - wait_days_pre) - 1) ltac:(lia)). lia. }
  assert (Hcell : Legacy.StockBuyCellValue ap_l bp_l buy_l sell_l dp_l_2
    max_stock_pre i ((i - wait_days_pre) - 1) j (Znth j (Znth i dp_l_2 nil) 0)).
  { eapply Legacy.StockBuyCellValue_empty_queue__buy_cell_progress; eauto; try lia. }
  pose proof (Legacy.StockBuyProgress_step_same__buy_cell_progress
    ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j
    ReusePreH24 ltac:(lia) Hcell) as Hnext.
  exact Hnext.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3_split_goal_3 : maximum_profit_entail_wit_36_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [_ [Hbuy _]]].
  rewrite <- PreH19 in Hbuy.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3_split_goal_4 : maximum_profit_entail_wit_36_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [_ [Hbuy _]]].
  rewrite <- PreH19 in Hbuy.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3_split_goal_5 : maximum_profit_entail_wit_36_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [_ [Hask _]].
  rewrite <- PreH18 in Hask.
  exact Hask.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3_split_goal_6 : maximum_profit_entail_wit_36_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH23 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH24 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH25 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price (j - buy_cap ) (j - 1 ) head tail )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  unfold Legacy.StockInputsBounded in ReusePreH23.
  destruct ReusePreH23 as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbidask _].
  rewrite <- PreH18 in Hbidask.
  lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_36_3 : maximum_profit_entail_wit_36_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_3_split_goal_1.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_3_split_goal_2.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_3_split_goal_3.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_3_split_goal_4.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_3_split_goal_5.
  - Goal_apply proof_of_maximum_profit_entail_wit_36_3_split_goal_6.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_37_1_split_goal_1 : maximum_profit_entail_wit_37_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH25 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH26 : (Legacy.StockBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i ((i - wait_days_pre) - 1) j )) by stock_restore.
  assert (ReusePreH27 : (Legacy.StockBuyQueue dp_l_2 queue_l_2 ((i - wait_days_pre) - 1) ask_price ((j - buy_cap ) - 1 ) (j - 2 ) head tail )) by stock_restore.
  assert (ReusePreH28 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  pose proof ReusePreH25 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [_ [_ [_ [_ Hdayinput]]]]]].
  specialize (Hdayinput i ltac:(lia)).
  destruct Hdayinput as [Hbid [Hask [Hbuy Hsell]]].
  rewrite <- PreH12 in Hbid.
  rewrite <- PreH13 in Hsell.
  pose proof (Legacy.StockBuyProgress_complete_day__buy_semantics
    ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
    i ((i - wait_days_pre) - 1) j ReusePreH25 PreH4 PreH7 ltac:(lia) ReusePreH26) as Hdone.
  exact Hdone.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_37_1 : maximum_profit_entail_wit_37_1.
Proof. aggressive_pre_process. Goal_apply proof_of_maximum_profit_entail_wit_37_1_split_goal_1. Qed.

Lemma proof_of_maximum_profit_entail_wit_37_2_split_goal_1 : maximum_profit_entail_wit_37_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH21 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH22 : (Legacy.StockEarlyBuyProgress ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i j )) by stock_restore.
  assert (ReusePreH23 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  assert (HDone :
    Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre
      wait_days_pre (i + 1)).
  { eapply stock_early_buy_complete__early_buy; eauto; lia. }
  exact HDone.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_37_2 : maximum_profit_entail_wit_37_2.
Proof. aggressive_pre_process. Goal_apply proof_of_maximum_profit_entail_wit_37_2_split_goal_1. Qed.

Lemma proof_of_maximum_profit_entail_wit_38_split_goal_1 : maximum_profit_entail_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH12 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH13 : (Legacy.StockDaysDone ap_l bp_l buy_l sell_l dp_l_2 max_stock_pre wait_days_pre i )) by stock_restore.
  assert (ReusePreH14 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  stock_weaken.
  pose proof ReusePreH12 as Hinputs.
  unfold Legacy.StockInputsBounded in Hinputs.
  destruct Hinputs as [Hask [Hbid [Hbuy [Hsell [Hdays [Hmax Hbounds]]]]]].
  eapply stock_answer_init__outer_answer; eauto; lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_38 : maximum_profit_entail_wit_38.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maximum_profit_entail_wit_38_split_goal_1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_1 : maximum_profit_entail_wit_39_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockAnswerProgress ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) days_pre (days_pre + 1) width dp_l_2
      (Znth days_pre dp_l_2 __default__List_Z)) as Htablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width days_pre) width
      (Znth days_pre dp_l_2 __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + days_pre * width * sizeof (INT))
        width (Znth days_pre dp_l_2 __default__List_Z)) in Htablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + days_pre * width * sizeof (INT)) j width
      (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0)
      (Znth days_pre dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr :
      (&( "dp" )) + days_pre * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (days_pre * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: try ((dump_pre_spatial; try stock_weaken); assumption).
    all: try ((dump_pre_spatial; try stock_weaken); lia).
    all: try (
      (dump_pre_spatial; try stock_weaken);
      apply (stock_answer_improve__outer_answer
        ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
        j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0));
      [ lia
      | exact PreH13
      | exact PreH2
      | exact ReusePreH16
      | assert (Hday : 0 <= days_pre < Zlength dp_l_2);
        [ unfold Legacy.StockTableShape in ReusePreH17; destruct ReusePreH17 as [Hlen _]; lia
        | rewrite <- (Legacy.same_index_different_default days_pre dp_l_2
            __default__List_Z Hday); reflexivity ]
      | exact PreH1 ]).
    all: unfold Legacy.StockAnswerProgress in ReusePreH16.
    all: destruct ReusePreH16 as [Hdone _].
    all: unfold Legacy.StockDaysDone in Hdone.
    all: destruct Hdone as [_ [Hbounded _]].
    all: unfold Legacy.StockTableValuesBounded in Hbounded.
    all: pose proof ReusePreH15 as Hinputs.
    all: unfold Legacy.StockInputsBounded in Hinputs.
    all: destruct Hinputs as [Hask _].
    all: rewrite Hask in Hbounded.
    all: specialize (Hbounded days_pre j ltac:(lia) ltac:(lia)).
    all: unfold Legacy.STOCK_MAX_PROFIT in Hbounded.
    all: assert (Hday : 0 <= days_pre < Zlength dp_l_2) by
      (unfold Legacy.StockTableShape in ReusePreH17;
       destruct ReusePreH17 as [Hlen _]; lia).
    all: rewrite <- (Legacy.same_index_different_default days_pre dp_l_2
      __default__List_Z Hday).
    all: (dump_pre_spatial; try stock_weaken).
    all: lia.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_39_2 : maximum_profit_entail_wit_39_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH15 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockAnswerProgress ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre j answer )) by stock_restore.
  assert (ReusePreH17 : (Legacy.StockTableShape dp_l_2 days_pre max_stock_pre )) by stock_restore.
  Exists queue_l_2 dp_l_2.
  split_pure_spatial.
  - pose proof (IntArray2.missing_i_merge_to_full
      (&( "dp" )) days_pre (days_pre + 1) width dp_l_2
      (Znth days_pre dp_l_2 __default__List_Z)) as Htablemerge.
    change (IntArray2.ElemArray.full
      (IntArray2.row_addr (&( "dp" )) width days_pre) width
      (Znth days_pre dp_l_2 __default__List_Z)) with
      (IntArray.full ((&( "dp" )) + days_pre * width * sizeof (INT))
        width (Znth days_pre dp_l_2 __default__List_Z)) in Htablemerge.
    pose proof (IntArray.missing_i_merge_to_full
      ((&( "dp" )) + days_pre * width * sizeof (INT)) j width
      (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0)
      (Znth days_pre dp_l_2 __default__List_Z)) as Hrowmerge.
    assert (Haddr :
      (&( "dp" )) + days_pre * width * sizeof (INT) + j * sizeof (INT) =
      (&( "dp" )) + (days_pre * width + j) * sizeof (INT)) by lia.
    rewrite <- Haddr.
    sep_apply Hrowmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    sep_apply Htablemerge; try lia.
    rewrite replace_Znth_Znth by lia.
    cancel.
  - (split_pures; try stock_weaken).
    all: try ((dump_pre_spatial; try stock_weaken); assumption).
    all: try ((dump_pre_spatial; try stock_weaken); lia).
    (dump_pre_spatial; try stock_weaken).
    apply (stock_answer_keep__outer_answer
      ap_l bp_l buy_l sell_l dp_l_2 days_pre max_stock_pre wait_days_pre
      j answer (Znth j (Znth days_pre dp_l_2 __default__List_Z) 0)).
    + lia.
    + exact PreH2.
    + exact ReusePreH16.
    + assert (Hday : 0 <= days_pre < Zlength dp_l_2).
      { unfold Legacy.StockTableShape in ReusePreH17. destruct ReusePreH17 as [Hlen _]. lia. }
      rewrite <- (Legacy.same_index_different_default days_pre dp_l_2
        __default__List_Z Hday).
      reflexivity.
    + exact PreH1.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_split_goal_1 : maximum_profit_entail_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst source_day.
  assert (ReusePreH14 : (Legacy.StockInputsBounded ap_l bp_l buy_l sell_l days_pre max_stock_pre )) by stock_restore.
  assert (ReusePreH15 : (Legacy.StockAnswerProgress ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre j answer )) by stock_restore.
  assert (ReusePreH16 : (Legacy.StockTableShape dp_l days_pre max_stock_pre )) by stock_restore.
  dump_pre_spatial.
  stock_weaken.
  apply (stock_answer_finish__outer_answer
    ap_l bp_l buy_l sell_l dp_l days_pre max_stock_pre wait_days_pre
    j answer).
  - lia.
  - exact PreH1.
  - exact PreH11.
  - exact ReusePreH15.

  all: try stock_finish.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40_split_goal_spatial : maximum_profit_entail_wit_40_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto). try subst width.
  prop_apply (IntArray.undef_seg_valid (&( "queue_index" )) (max_stock_pre+1) 991).
  prop_apply (IntArray.undef_seg_valid (&( "dp" )) ((days_pre+1)*(max_stock_pre+1)) 982081). Intros.
  pose proof (Zlength_nonneg queue_l). pose proof (Zlength_nonneg dp_l).
  sep_apply (IntArray.full_to_undef_full (&( "queue_index" )) (max_stock_pre+1) queue_l).
  sep_apply (IntArray.undef_full_to_undef_seg (&( "queue_index" )) (max_stock_pre+1)).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&( "queue_index" )) 0 (max_stock_pre+1) 991 ltac:(lia)).
  sep_apply (scratch_rows_to_flat_undef (&( "dp" )) (days_pre+1) (max_stock_pre+1) dp_l ltac:(lia)).
  sep_apply (IntArray.undef_full_to_undef_seg (&( "dp" )) ((days_pre+1)*(max_stock_pre+1))).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&( "dp" )) 0 ((days_pre+1)*(max_stock_pre+1)) 982081 ltac:(nia)).
  simpl. rewrite !Z.add_0_r. cancel.
Qed.

Lemma proof_of_maximum_profit_entail_wit_40 : maximum_profit_entail_wit_40.
Proof.
  unfold maximum_profit_entail_wit_40. right. intros.
  apply _derivable1_andp_intros.
  - exact (proof_of_maximum_profit_entail_wit_40_split_goal_1
      wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l answer j
      width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31).
  - exact (proof_of_maximum_profit_entail_wit_40_split_goal_spatial
      wait_days_pre max_stock_pre days_pre sell_l buy_l bp_l ap_l queue_l dp_l answer j
      width neg_inf PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
      PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
      PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31).
Qed.
