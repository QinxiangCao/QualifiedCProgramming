Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition STOCK_NEG_INF : Z := -1000000000.
Definition STOCK_MAX_PROFIT : Z := 1000000000.
Definition StockInitialCell (day stock : Z) : Z :=
  if Z.eq_dec day 0 then
    if Z.eq_dec stock 0 then 0 else STOCK_NEG_INF
  else STOCK_NEG_INF.

Definition StockTableShape
    (table : list (list Z)) (days max_stock : Z) : Prop :=
  Zlength table = days + 1 /\
  forall row, 0 <= row < days + 1 ->
    Zlength (Znth row table []) = max_stock + 1.

Definition StockTableValuesBounded
    (table : list (list Z)) (days max_stock : Z) : Prop :=
  forall row stock,
    0 <= row < days + 1 ->
    0 <= stock < max_stock + 1 ->
    STOCK_NEG_INF <= Znth stock (Znth row table []) 0 <= STOCK_MAX_PROFIT.

Definition StockInputsBounded
    (ask bid buy sell : list Z) (days max_stock : Z) : Prop :=
  Zlength ask = days /\
  Zlength bid = days /\
  Zlength buy = days /\
  Zlength sell = days /\
  1 <= days <= 990 /\
  1 <= max_stock <= 990 /\
  (forall day, 1 <= day <= days ->
     1 <= Znth (day - 1) bid 0 <= Znth (day - 1) ask 0 /\
     Znth (day - 1) ask 0 <= 1000 /\
     1 <= Znth (day - 1) buy 0 <= max_stock /\
     1 <= Znth (day - 1) sell 0 <= max_stock).

Inductive StockTradingHistory
    (ask bid buy sell : list Z) (max_stock wait : Z)
    : Z -> Z -> Z -> Prop :=
  | StockTradingHistory_first_buy :
      forall day amount,
        1 <= day ->
        1 <= amount <= Znth (day - 1) buy 0 ->
        amount <= max_stock ->
        StockTradingHistory ask bid buy sell max_stock wait
          day amount (- amount * Znth (day - 1) ask 0)
  | StockTradingHistory_buy :
      forall previous_day previous_stock previous_profit day amount,
        StockTradingHistory ask bid buy sell max_stock wait
          previous_day previous_stock previous_profit ->
        previous_day + wait < day ->
        1 <= amount <= Znth (day - 1) buy 0 ->
        previous_stock + amount <= max_stock ->
        StockTradingHistory ask bid buy sell max_stock wait
          day (previous_stock + amount)
          (previous_profit - amount * Znth (day - 1) ask 0)
  | StockTradingHistory_sell :
      forall previous_day previous_stock previous_profit day amount,
        StockTradingHistory ask bid buy sell max_stock wait
          previous_day previous_stock previous_profit ->
        previous_day + wait < day ->
        1 <= amount <= Znth (day - 1) sell 0 ->
        amount <= previous_stock ->
        StockTradingHistory ask bid buy sell max_stock wait
          day (previous_stock - amount)
          (previous_profit + amount * Znth (day - 1) bid 0).

Definition StockFeasiblePortfolio
    (ask bid buy sell : list Z) (max_stock wait horizon stock profit : Z) : Prop :=
  (stock = 0 /\ profit = 0) \/
  exists last_day,
    1 <= last_day <= horizon /\
    StockTradingHistory ask bid buy sell max_stock wait
      last_day stock profit.

Definition StockPortfolioValue
    (ask bid buy sell : list Z)
    (max_stock wait horizon stock value : Z) : Prop :=
  0 <= stock <= max_stock /\
  ((value = STOCK_NEG_INF /\
    ~ exists profit,
        StockFeasiblePortfolio
          ask bid buy sell max_stock wait horizon stock profit) \/
   (StockFeasiblePortfolio
      ask bid buy sell max_stock wait horizon stock value /\
    forall profit,
      StockFeasiblePortfolio
        ask bid buy sell max_stock wait horizon stock profit ->
      profit <= value)).

Definition StockMaximumProfit
    (ask bid buy sell : list Z)
    (days max_stock wait answer : Z) : Prop :=
  exists stock,
    0 <= stock <= max_stock /\
    StockFeasiblePortfolio
      ask bid buy sell max_stock wait days stock answer /\
    forall stock' profit,
      0 <= stock' <= max_stock ->
      StockFeasiblePortfolio
        ask bid buy sell max_stock wait days stock' profit ->
      profit <= answer.

Definition StockFillRows
    (table : list (list Z)) (days max_stock row : Z) : Prop :=
  0 <= row <= days + 1 /\
  StockTableShape table days max_stock /\
  forall d stock,
    0 <= d < row ->
    0 <= stock < max_stock + 1 ->
    Zlength (Znth d table []) = max_stock + 1 /\
    Znth stock (Znth d table []) 0 = StockInitialCell d stock.

Definition StockFillCells
    (current_row : list Z) (max_stock row col : Z) : Prop :=
  0 <= col <= max_stock + 1 /\
  Zlength current_row = max_stock + 1 /\
  forall stock,
    0 <= stock < col ->
    Znth stock current_row 0 = StockInitialCell row stock.

Definition StockDaysDone
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait next_day : Z) : Prop :=
  StockTableShape table (Zlength ask) max_stock /\
  StockTableValuesBounded table (Zlength ask) max_stock /\
  0 <= next_day /\
  forall day stock,
    0 <= day < next_day ->
    0 <= stock <= max_stock ->
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (Znth stock (Znth day table []) 0).

Definition StockCopyProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day col : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  1 <= day /\
  0 <= col <= max_stock + 1 /\
  forall stock,
    0 <= stock < col ->
    Znth stock (Znth day table []) 0 =
    Znth stock (Znth (day - 1) table []) 0.

Definition StockEarlyBuyProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day next_stock : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  1 <= day /\
  1 <= next_stock <= Znth (day - 1) buy 0 + 1 /\
  Znth 0 (Znth day table []) 0 =
    Znth 0 (Znth (day - 1) table []) 0 /\
  forall stock,
    1 <= stock <= max_stock ->
    if Z_lt_dec stock next_stock then
      Znth stock (Znth day table []) 0 =
      Z.max (Znth stock (Znth (day - 1) table []) 0)
            (- stock * Znth (day - 1) ask 0)
    else
      Znth stock (Znth day table []) 0 =
      Znth stock (Znth (day - 1) table []) 0.

Definition StockSellScore
    (table : list (list Z)) (source price stock : Z) : Z :=
  Znth stock (Znth source table []) 0 + stock * price.

Definition StockBuyScore
    (table : list (list Z)) (source price stock : Z) : Z :=
  Znth stock (Znth source table []) 0 + stock * price.

Definition StockFiniteTableIndex
    (table : list (list Z)) (source stock : Z) : Prop :=
  0 <= stock /\
  stock < Zlength (Znth source table []) /\
  Znth stock (Znth source table []) 0 <> STOCK_NEG_INF.

Definition StockFiniteIndexInWindow
    (table : list (list Z)) (source lower upper stock : Z) : Prop :=
  0 <= stock /\
  stock < Zlength (Znth source table []) /\
  Znth stock (Znth source table []) 0 <> STOCK_NEG_INF /\
  lower <= stock <= upper.

Definition StockSellQueue
    (table : list (list Z)) (queue : list Z)
    (source price lower upper head tail : Z) : Prop :=
  0 <= head <= tail /\
  (forall pos, head <= pos < tail ->
     StockFiniteIndexInWindow table source lower upper
       (Znth pos queue 0)) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 > Znth right queue 0 /\
     StockSellScore table source price (Znth left queue 0) >
     StockSellScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source lower upper candidate ->
     exists pos, head <= pos < tail /\
       Znth pos queue 0 <= candidate /\
       StockSellScore table source price candidate <=
       StockSellScore table source price (Znth pos queue 0)).

Definition StockSellQueueExpiring
    (table : list (list Z)) (queue : list Z)
    (source price lower current_upper head tail : Z) : Prop :=
  StockSellQueue table queue source price
    lower (current_upper + 1) head tail \/
  StockSellQueue table queue source price
    lower current_upper head tail.

Definition StockSellQueuePopping
    (table : list (list Z)) (queue : list Z)
    (source price incoming upper head tail : Z) : Prop :=
  StockFiniteTableIndex table source incoming /\
  0 <= head <= tail /\
  (forall pos, head <= pos < tail ->
     StockFiniteIndexInWindow table source (incoming + 1) upper
       (Znth pos queue 0)) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 > Znth right queue 0 /\
     StockSellScore table source price (Znth left queue 0) >
     StockSellScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source incoming upper candidate ->
     StockSellScore table source price candidate <=
       StockSellScore table source price incoming \/
     exists pos, head <= pos < tail /\
       Znth pos queue 0 <= candidate /\
       StockSellScore table source price candidate <=
       StockSellScore table source price (Znth pos queue 0)).

Definition StockSellQueuePending
    (table : list (list Z)) (queue : list Z)
    (source price incoming upper head tail : Z) : Prop :=
  StockSellQueuePopping table queue source price incoming upper head tail /\
  tail < Zlength queue /\
  (head < tail ->
   StockSellScore table source price incoming <
   StockSellScore table source price (Znth (tail - 1) queue 0)).

Definition StockBuyQueue
    (table : list (list Z)) (queue : list Z)
    (source price lower upper head tail : Z) : Prop :=
  0 <= head <= tail /\
  (forall pos, head <= pos < tail ->
     StockFiniteIndexInWindow table source lower upper
       (Znth pos queue 0)) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 < Znth right queue 0 /\
     StockBuyScore table source price (Znth left queue 0) >
     StockBuyScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source lower upper candidate ->
     exists pos, head <= pos < tail /\
       candidate <= Znth pos queue 0 /\
       StockBuyScore table source price candidate <=
       StockBuyScore table source price (Znth pos queue 0)).

Definition StockBuyQueueExpiring
    (table : list (list Z)) (queue : list Z)
    (source price current_lower upper head tail : Z) : Prop :=
  StockBuyQueue table queue source price
    (current_lower - 1) upper head tail \/
  StockBuyQueue table queue source price
    current_lower upper head tail.

Lemma StockBuyQueue_replace_other_row__buy_cell_progress :
  forall table queue source price lower upper head tail row_index row,
    0 <= source < Zlength table ->
    0 <= row_index < Zlength table ->
    source <> row_index ->
    StockBuyQueue table queue source price lower upper head tail ->
    StockBuyQueue (replace_Znth row_index row table) queue source price
      lower upper head tail.
Proof.
  intros table queue source price lower upper head tail row_index row
    Hsource Hrow Hneq Hqueue.
  assert (Hsource_row :
    Znth source (replace_Znth row_index row table) [] =
    Znth source table []).
  { rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  unfold StockBuyQueue, StockFiniteIndexInWindow, StockBuyScore in *.
  rewrite Hsource_row.
  exact Hqueue.
Qed.

Definition StockBuyQueuePopping
    (table : list (list Z)) (queue : list Z)
    (source price lower incoming head tail : Z) : Prop :=
  StockFiniteTableIndex table source incoming /\
  0 <= head <= tail /\
  (forall pos, head <= pos < tail ->
     StockFiniteIndexInWindow table source lower (incoming - 1)
       (Znth pos queue 0)) /\
  (forall left right, head <= left < right /\ right < tail ->
     Znth left queue 0 < Znth right queue 0 /\
     StockBuyScore table source price (Znth left queue 0) >
     StockBuyScore table source price (Znth right queue 0)) /\
  (forall candidate,
     StockFiniteIndexInWindow table source lower incoming candidate ->
     StockBuyScore table source price candidate <=
       StockBuyScore table source price incoming \/
     exists pos, head <= pos < tail /\
       candidate <= Znth pos queue 0 /\
       StockBuyScore table source price candidate <=
       StockBuyScore table source price (Znth pos queue 0)).

Definition StockBuyQueuePending
    (table : list (list Z)) (queue : list Z)
    (source price lower incoming head tail : Z) : Prop :=
  StockBuyQueuePopping table queue source price lower incoming head tail /\
  tail < Zlength queue /\
  (head < tail ->
   StockBuyScore table source price incoming <
   StockBuyScore table source price (Znth (tail - 1) queue 0)).

Definition StockSellCandidate
    (bid sell : list Z) (table : list (list Z))
    (max_stock day source stock amount value : Z) : Prop :=
  (amount = 0 /\
   value = Znth stock (Znth (day - 1) table []) 0) \/
  (1 <= amount <= Znth (day - 1) sell 0 /\
   stock + amount <= max_stock /\
   Znth (stock + amount) (Znth source table []) 0 <> STOCK_NEG_INF /\
   value =
     Znth (stock + amount) (Znth source table []) 0 +
     amount * Znth (day - 1) bid 0).

Definition StockSellCellValue
    (bid sell : list Z) (table : list (list Z))
    (max_stock day source stock value : Z) : Prop :=
  (exists amount,
     StockSellCandidate
       bid sell table max_stock day source stock amount value) /\
  (forall amount candidate,
     StockSellCandidate
       bid sell table max_stock day source stock amount candidate ->
     candidate <= value).

Definition StockBuyCandidate
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock day source stock amount value : Z) : Prop :=
  (amount = 0 /\
   StockSellCellValue bid sell table max_stock day source stock value) \/
  (1 <= amount <= Znth (day - 1) buy 0 /\
   amount <= stock /\
   Znth (stock - amount) (Znth source table []) 0 <> STOCK_NEG_INF /\
   value =
     Znth (stock - amount) (Znth source table []) 0 -
     amount * Znth (day - 1) ask 0).

Definition StockBuyCellValue
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock day source stock value : Z) : Prop :=
  ((exists amount,
      StockBuyCandidate
        ask bid buy sell table max_stock day source stock amount value) /\
   (forall amount candidate,
      StockBuyCandidate
        ask bid buy sell table max_stock day source stock amount candidate ->
      candidate <= value)) /\
  exists zero_value,
    StockSellCellValue
      bid sell table max_stock day source stock zero_value.

Definition StockSellProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day source next_stock : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  1 <= day <= Zlength ask /\
  source = day - wait - 1 /\
  0 < source < day /\
  -1 <= next_stock < max_stock /\
  (forall stock,
     0 <= stock <= next_stock ->
     Znth stock (Znth day table []) 0 =
       Znth stock (Znth (day - 1) table []) 0) /\
  (forall stock,
     next_stock < stock < max_stock ->
     StockSellCellValue bid sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)) /\
  Znth max_stock (Znth day table []) 0 =
    Znth max_stock (Znth (day - 1) table []) 0.

Definition StockBuyProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (max_stock wait day source next_stock : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day /\
  1 <= day <= Zlength ask /\
  source = day - wait - 1 /\
  0 < source < day /\
  1 <= next_stock <= max_stock + 1 /\
  (forall stock,
     0 <= stock < next_stock ->
     StockBuyCellValue ask bid buy sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)) /\
  (forall stock,
     next_stock <= stock <= max_stock ->
     StockSellCellValue bid sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)).

Definition StockAnswerProgress
    (ask bid buy sell : list Z) (table : list (list Z))
    (days max_stock wait next_stock answer : Z) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait (days + 1) /\
  0 <= next_stock <= max_stock + 1 /\
  0 <= answer /\
  ((next_stock = 0 /\ answer = 0) \/
   (0 < next_stock /\
    (exists stock,
       0 <= stock < next_stock /\
       StockFeasiblePortfolio
         ask bid buy sell max_stock wait days stock answer) /\
    (forall stock profit,
       0 <= stock < next_stock ->
       StockFeasiblePortfolio
         ask bid buy sell max_stock wait days stock profit ->
       profit <= answer))).

Lemma same_index_different_default:
  forall (i : Z) (dp_l_2 : list(list Z)) (__default__List_Z : list Z),
    0 <= i < Zlength dp_l_2 ->
    (Znth i dp_l_2 nil) = (Znth i dp_l_2 __default__List_Z).
Proof.
  intros i dp_l_2 __default__List_Z Hi.
  apply Znth_indep.
  exact Hi.
Qed.

Lemma StockDaysDone_cell_bounded__safety_sell :
  forall ask bid buy sell table days max_stock wait next_day row stock
         (default_row : list Z),
    StockInputsBounded ask bid buy sell days max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait next_day ->
    StockTableShape table days max_stock ->
    0 <= row < days + 1 ->
    0 <= stock <= max_stock ->
    STOCK_NEG_INF <= Znth stock (Znth row table default_row) 0 <=
      STOCK_MAX_PROFIT.
Proof.
  intros ask bid buy sell table days max_stock wait next_day row stock
    default_row Hinputs Hdone Hshape Hrow Hstock.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [Hasklen _].
  unfold StockDaysDone in Hdone.
  destruct Hdone as [_ [Hbounded _]].
  unfold StockTableValuesBounded in Hbounded.
  rewrite Hasklen in Hbounded.
  specialize (Hbounded row stock Hrow ltac:(lia)).
  rewrite <- (same_index_different_default row table default_row) by
    (unfold StockTableShape in Hshape; lia).
  exact Hbounded.
Qed.

Lemma StockDaysDone_cell_bounded__safety_buy :
  forall ask bid buy sell table days max_stock wait next_day row stock
         (default_row : list Z),
    StockInputsBounded ask bid buy sell days max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait next_day ->
    StockTableShape table days max_stock ->
    0 <= row < days + 1 ->
    0 <= stock <= max_stock ->
    STOCK_NEG_INF <= Znth stock (Znth row table default_row) 0 <=
      STOCK_MAX_PROFIT.
Proof.
  intros ask bid buy sell table days max_stock wait next_day row stock
    default_row Hinputs Hdone Hshape Hrow Hstock.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [Hasklen _].
  unfold StockDaysDone in Hdone.
  destruct Hdone as [_ [Hbounded _]].
  unfold StockTableValuesBounded in Hbounded.
  rewrite Hasklen in Hbounded.
  specialize (Hbounded row stock Hrow ltac:(lia)).
  rewrite <- (same_index_different_default row table default_row) by
    (unfold StockTableShape in Hshape; lia).
  exact Hbounded.
Qed.

Lemma stock_fill_cells_snoc__init_copy :
  forall current max_stock row col value,
    StockFillCells current max_stock row col ->
    col < max_stock + 1 ->
    value = StockInitialCell row col ->
    StockFillCells (replace_Znth col value current)
      max_stock row (col + 1).
Proof.
  intros current max_stock row col value Hfill Hcol_lt Hvalue.
  unfold StockFillCells in *.
  destruct Hfill as [Hcol [Hlen Hprefix]].
  split; [lia |].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros stock Hstock.
    destruct (Z.eq_dec stock col) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia. exact Hvalue.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hprefix. lia.
Qed.

Lemma stock_initial_cell_bounded__init_copy :
  forall row stock,
    STOCK_NEG_INF <= StockInitialCell row stock <= STOCK_MAX_PROFIT.
Proof.
  intros row stock.
  unfold StockInitialCell, STOCK_NEG_INF, STOCK_MAX_PROFIT.
  destruct (Z.eq_dec row 0); destruct (Z.eq_dec stock 0); lia.
Qed.

Lemma stock_trading_history_day_positive__init_copy :
  forall ask bid buy sell max_stock wait day stock profit,
    0 <= wait ->
    StockTradingHistory ask bid buy sell max_stock wait day stock profit ->
    1 <= day.
Proof.
  intros ask bid buy sell max_stock wait day stock profit Hwait Hhist.
  induction Hhist; lia.
Qed.

Lemma stock_initial_portfolio_value__init_copy :
  forall ask bid buy sell max_stock wait stock,
    0 <= wait ->
    0 <= stock <= max_stock ->
    StockPortfolioValue ask bid buy sell max_stock wait 0 stock
      (StockInitialCell 0 stock).
Proof.
  intros ask bid buy sell max_stock wait stock Hwait Hstock.
  unfold StockPortfolioValue.
  split; [exact Hstock |].
  unfold StockInitialCell.
  destruct (Z.eq_dec stock 0) as [-> | Hneq].
  - simpl. right.
    split.
    + unfold StockFeasiblePortfolio. left. tauto.
    + intros profit Hfeasible.
      unfold StockFeasiblePortfolio in Hfeasible.
      destruct Hfeasible as [[_ Hprofit] |
        [last_day [[Hlast_lo Hlast_hi] Hhist]]].
      * rewrite Hprofit. lia.
      * pose proof
          (stock_trading_history_day_positive__init_copy
             ask bid buy sell max_stock wait last_day 0 profit
             Hwait Hhist).
        lia.
  - simpl. left.
    split; [reflexivity |].
    intros [profit Hfeasible].
    unfold StockFeasiblePortfolio in Hfeasible.
    destruct Hfeasible as [[Hstock0 _] |
      [last_day [[Hlast_lo Hlast_hi] Hhist]]].
    + contradiction.
    + pose proof
        (stock_trading_history_day_positive__init_copy
           ask bid buy sell max_stock wait last_day stock profit
           Hwait Hhist).
      lia.
Qed.

Lemma stock_completed_initial_table_days_done__init_copy :
  forall ask bid buy sell table days max_stock wait,
    0 <= wait ->
    StockInputsBounded ask bid buy sell days max_stock ->
    StockFillRows table days max_stock (days + 1) ->
    StockDaysDone ask bid buy sell table max_stock wait 1 /\
    StockTableShape table days max_stock.
Proof.
  intros ask bid buy sell table days max_stock wait Hwait0 Hinputs Hrows.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as
    [Hask [Hbid [Hbuy [Hsell [Hdays [Hmax Hvalues]]]]]].
  unfold StockFillRows in Hrows.
  destruct Hrows as [Hrow [Hshape Hcells]].
  split.
  - unfold StockDaysDone.
    rewrite Hask.
    split; [exact Hshape |].
    split.
    + unfold StockTableValuesBounded.
      intros row stock Hrow' Hstock.
      specialize (Hcells row stock Hrow' Hstock).
      destruct Hcells as [_ ->].
      apply stock_initial_cell_bounded__init_copy.
    + split; [lia |].
      intros day stock Hday Hstock.
      assert (day = 0) by lia. subst day.
      assert (Hstock55 : 0 <= stock < max_stock + 1) by lia.
      specialize (Hcells 0 stock ltac:(lia) Hstock55).
      destruct Hcells as [_ Hcell].
      rewrite Hcell.
      apply stock_initial_portfolio_value__init_copy; lia.
  - exact Hshape.
Qed.

Lemma stock_fill_update_step__init_copy :
  forall table days max_stock row col value d,
    StockFillRows table days max_stock row ->
    StockFillCells (Znth row table d) max_stock row col ->
    0 <= row < days + 1 ->
    col < max_stock + 1 ->
    value = StockInitialCell row col ->
    let row' := replace_Znth col value (Znth row table d) in
    let table' := replace_Znth row row' table in
    StockFillRows table' days max_stock row /\
    StockFillCells (Znth row table' d) max_stock row (col + 1).
Proof.
  intros table days max_stock row col value d Hrows Hcells Hrow Hcol Hvalue
    row' table'.
  unfold StockFillRows in Hrows.
  destruct Hrows as [Hrow_bound [Hshape Hprefix]].
  unfold StockTableShape in Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  pose proof Hcells as Hcells_orig.
  unfold StockFillCells in Hcells.
  destruct Hcells as [Hcol_bound [Hcurrent_len Hcells]].
  assert (Hrow'_len : Zlength row' = max_stock + 1).
  { unfold row'. rewrite Zlength_replace_Znth. exact Hcurrent_len. }
  assert (Hshape' : StockTableShape table' days max_stock).
  { unfold StockTableShape.
    split.
    - unfold table'. rewrite Zlength_replace_Znth. exact Htable_len.
    - intros r Hr.
      unfold table'.
      destruct (Z.eq_dec r row) as [-> | Hneq].
      + rewrite Znth_replace_Znth_Same by (rewrite Htable_len; lia).
        exact Hrow'_len.
      + rewrite Znth_replace_Znth_Diff by
          (try rewrite Htable_len; lia).
        apply Hrow_len. exact Hr. }
  split.
  - unfold StockFillRows.
    split; [exact Hrow_bound |].
    split; [exact Hshape' |].
    intros r stock Hr Hstock.
    unfold table'.
    rewrite Znth_replace_Znth_Diff by
      (try rewrite Htable_len; lia).
    apply Hprefix; assumption.
  - assert (Hadvanced : StockFillCells row' max_stock row (col + 1)).
    { unfold row'.
      apply stock_fill_cells_snoc__init_copy
        with (current := Znth row table d) (value := value);
        assumption. }
    unfold table'.
    rewrite Znth_replace_Znth_Same by (rewrite Htable_len; lia).
    exact Hadvanced.
Qed.

Lemma stock_copy_update_step__init_copy :
  forall ask bid buy sell table max_stock wait day col value,
    StockTableShape table (Zlength ask) max_stock ->
    StockCopyProgress ask bid buy sell table max_stock wait day col ->
    value = Znth col (Znth (day - 1) table []) 0 ->
    0 <= day < Zlength ask + 1 ->
    0 <= col < max_stock + 1 -> col <= max_stock ->
    let row' := replace_Znth col value (Znth day table []) in
    let table' := replace_Znth day row' table in
    StockCopyProgress ask bid buy sell table' max_stock wait day (col + 1) /\
    StockTableShape table' (Zlength ask) max_stock.
Proof.
  intros ask bid buy sell table max_stock wait day col value
    Hshape Hcopy Hvalue Hday Hcol Hcolmaxstock row' table'.
  unfold StockTableShape in Hshape.
  destruct Hshape as [Htable_len Hrow_len].
  assert (Hday_len : Zlength (Znth day table []) = max_stock + 1)
    by (apply Hrow_len; lia).
  assert (Hprev : 0 <= day - 1 < Zlength ask + 1) by
    (unfold StockCopyProgress in Hcopy; lia).
  assert (Hrow'_len : Zlength row' = max_stock + 1).
  { unfold row'. rewrite Zlength_replace_Znth. exact Hday_len. }
  assert (Hshape' : StockTableShape table' (Zlength ask) max_stock).
  { unfold StockTableShape. split.
    - unfold table'. rewrite Zlength_replace_Znth. exact Htable_len.
    - intros r Hr. unfold table'. destruct (Z.eq_dec r day) as [-> | Hneq].
      + rewrite Znth_replace_Znth_Same by (rewrite Htable_len; exact Hday).
        exact Hrow'_len.
      + rewrite Znth_replace_Znth_Diff by (try rewrite Htable_len; lia).
        apply Hrow_len. exact Hr. }
  split; [|exact Hshape'].
  unfold StockCopyProgress in *.
  destruct Hcopy as [Hdone [Hday1 [Hcolmax Hprefix]]]. split.
  - unfold StockDaysDone in *.
    destruct Hdone as [Hshape0 [Hbounded [Hnext Hportfolio]]].
    split; [exact Hshape'|]. split.
    + unfold StockTableValuesBounded in *.
      intros r stock Hr Hstock. unfold table'.
      destruct (Z.eq_dec r day) as [-> | Hrday].
      * rewrite Znth_replace_Znth_Same by (rewrite Htable_len; exact Hday).
        unfold row'. destruct (Z.eq_dec stock col) as [-> | Hstockcol].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hday_len; exact Hcol).
           rewrite Hvalue. apply Hbounded; assumption.
        -- rewrite Znth_replace_Znth_Diff by (try rewrite Hday_len; lia).
           apply Hbounded; assumption.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Htable_len; lia).
        apply Hbounded; assumption.
    + split; [exact Hnext|]. intros r stock Hr Hstock. unfold table'.
      rewrite Znth_replace_Znth_Diff by (try rewrite Htable_len; lia).
      apply Hportfolio; assumption.
  - split; [exact Hday1|]. split; [lia|]. intros stock Hstock.
    unfold table'. rewrite Znth_replace_Znth_Same by
      (rewrite Htable_len; exact Hday).
    rewrite Znth_replace_Znth_Diff by
      (try rewrite Htable_len; try exact Hprev; lia).
    unfold row'. destruct (Z.eq_dec stock col) as [-> | Hstockcol].
    + rewrite Znth_replace_Znth_Same by (rewrite Hday_len; exact Hcol).
      exact Hvalue.
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hday_len; lia).
      apply Hprefix. lia.
Qed.

Lemma stock_trading_history_day_positive__early_buy :
  forall ask bid buy sell max_stock wait day stock profit,
    0 <= wait ->
    StockTradingHistory ask bid buy sell max_stock wait day stock profit ->
    1 <= day.
Proof.
  intros ask bid buy sell max_stock wait day stock profit Hwait Hhist.
  induction Hhist; lia.
Qed.

Lemma stock_feasible_early_day_iff__early_buy :
  forall ask bid buy sell max_stock wait day stock profit,
    0 <= wait -> 1 <= day -> day - 1 <= wait ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit <->
    StockFeasiblePortfolio ask bid buy sell max_stock wait (day - 1) stock profit \/
    (1 <= stock <= Znth (day - 1) buy 0 /\ stock <= max_stock /\
     profit = - stock * Znth (day - 1) ask 0).
Proof.
  intros ask bid buy sell max_stock wait day stock profit Hwait Hday Hearly.
  split.
  - intros Hfeasible. unfold StockFeasiblePortfolio in Hfeasible.
    destruct Hfeasible as [[Hstock Hprofit] |
      [last_day [[Hlastlo Hlasthi] Hhist]]].
    + left. unfold StockFeasiblePortfolio. left. tauto.
    + destruct (Z_lt_ge_dec last_day day) as [Hlt | Hge].
      * left. unfold StockFeasiblePortfolio. right.
        exists last_day. split; [lia | exact Hhist].
      * assert (last_day = day) by lia. subst last_day. inversion Hhist; subst.
        -- right. repeat split; try assumption; try lia; reflexivity.
        -- match goal with
           | Hprev : StockTradingHistory _ _ _ _ _ _ ?pd ?ps ?pp |- _ =>
               pose proof (stock_trading_history_day_positive__early_buy
                 ask bid buy sell max_stock wait pd ps pp Hwait Hprev)
           end. lia.
        -- match goal with
           | Hprev : StockTradingHistory _ _ _ _ _ _ ?pd ?ps ?pp |- _ =>
               pose proof (stock_trading_history_day_positive__early_buy
                 ask bid buy sell max_stock wait pd ps pp Hwait Hprev)
           end. lia.
  - intros [Hold | [Hamount [Hstockmax Hprofit]]].
    + unfold StockFeasiblePortfolio in *.
      destruct Hold as [Hzero | [last_day [Hlast Hhist]]].
      * left. exact Hzero.
      * right. exists last_day. split; [lia | exact Hhist].
    + unfold StockFeasiblePortfolio. right. exists day.
      split; [lia |]. subst profit.
      apply StockTradingHistory_first_buy; assumption.
Qed.

Lemma stock_portfolio_extend_first_buy__early_buy :
  forall ask bid buy sell max_stock wait day stock old candidate,
    0 <= wait -> 1 <= day -> day - 1 <= wait ->
    0 <= stock <= max_stock ->
    1 <= stock <= Znth (day - 1) buy 0 ->
    candidate = - stock * Znth (day - 1) ask 0 ->
    STOCK_NEG_INF <= candidate ->
    StockPortfolioValue ask bid buy sell max_stock wait (day - 1) stock old ->
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (Z.max old candidate).
Proof.
  intros ask bid buy sell max_stock wait day stock old candidate
    Hwait Hday Hearly Hstock Hbuy Hcandidate Hcandlow Hold.
  unfold StockPortfolioValue in *.
  destruct Hold as [_ Hold]. split; [exact Hstock |].
  assert (Hcandfeasible :
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock candidate).
  { apply (proj2 (stock_feasible_early_day_iff__early_buy
      ask bid buy sell max_stock wait day stock candidate Hwait Hday Hearly)).
    right. split; [exact Hbuy |]. split; [lia | exact Hcandidate]. }
  right. split.
  - destruct Hold as [[Holdeq Hnone] | [Holdfeasible Holdmax]].
    + rewrite Holdeq. rewrite Z.max_r; [exact Hcandfeasible | exact Hcandlow].
    + destruct (Z.max_spec old candidate) as [[_ Hmaxeq] | [_ Hmaxeq]].
      * rewrite Hmaxeq. exact Hcandfeasible.
      * rewrite Hmaxeq.
        apply (proj2 (stock_feasible_early_day_iff__early_buy
          ask bid buy sell max_stock wait day stock old Hwait Hday Hearly)).
        left. exact Holdfeasible.
  - intros profit Hprofit.
    apply (proj1 (stock_feasible_early_day_iff__early_buy
      ask bid buy sell max_stock wait day stock profit Hwait Hday Hearly))
      in Hprofit.
    destruct Hprofit as [Hprev | [Hamount [_ ->]]].
    + destruct Hold as [[Holdeq Hnone] | [Holdfeasible Holdmax]].
      * exfalso. apply Hnone. eauto.
      * specialize (Holdmax profit Hprev). apply Z.le_trans with old;
          [exact Holdmax | apply Z.le_max_l].
    + subst candidate. apply Z.le_max_r.
Qed.

Lemma stock_portfolio_no_first_buy__early_buy :
  forall ask bid buy sell max_stock wait day stock value,
    0 <= wait -> 1 <= day -> day - 1 <= wait ->
    0 <= stock <= max_stock ->
    (stock = 0 \/ Znth (day - 1) buy 0 < stock) ->
    StockPortfolioValue ask bid buy sell max_stock wait (day - 1) stock value ->
    StockPortfolioValue ask bid buy sell max_stock wait day stock value.
Proof.
  intros ask bid buy sell max_stock wait day stock value
    Hwait Hday Hearly Hstock Hnone Hold.
  unfold StockPortfolioValue in *.
  destruct Hold as [_ Hold]. split; [exact Hstock |].
  destruct Hold as [[Hvalue Hnot] | [Hfeasible Hmax]].
  - left. split; [exact Hvalue |]. intros [profit Hprofit].
    apply (proj1 (stock_feasible_early_day_iff__early_buy
      ask bid buy sell max_stock wait day stock profit Hwait Hday Hearly))
      in Hprofit.
    destruct Hprofit as [Hprev | [Hamount _]].
    + apply Hnot. eauto.
    + destruct Hnone; lia.
  - right. split.
    + apply (proj2 (stock_feasible_early_day_iff__early_buy
        ask bid buy sell max_stock wait day stock value Hwait Hday Hearly)).
      left. exact Hfeasible.
    + intros profit Hprofit.
      apply (proj1 (stock_feasible_early_day_iff__early_buy
        ask bid buy sell max_stock wait day stock profit Hwait Hday Hearly))
        in Hprofit.
      destruct Hprofit as [Hprev | [Hamount _]].
      * apply Hmax. exact Hprev.
      * destruct Hnone; lia.
Qed.

Lemma stock_early_buy_complete__early_buy :
  forall ask bid buy sell table days max_stock wait day next_stock,
    StockInputsBounded ask bid buy sell days max_stock ->
    StockEarlyBuyProgress ask bid buy sell table max_stock wait day next_stock ->
    1 <= day <= days -> day - 1 <= wait ->
    Znth (day - 1) buy 0 < next_stock ->
    StockDaysDone ask bid buy sell table max_stock wait (day + 1).
Proof.
  intros ask bid buy sell table days max_stock wait day next_stock
    Hinputs Hprogress Hdaybound Hearly Hfinished.
  pose proof Hinputs as Hinputbounds.
  unfold StockInputsBounded in Hinputbounds.
  destruct Hinputbounds as
    [Hasklen [Hbidlen [Hbuylen [Hselllen [Hdays [Hmax Hvalues]]]]]].
  specialize (Hvalues day Hdaybound).
  destruct Hvalues as [Hask [Hbid [Hbuy Hsell]]].
  unfold StockEarlyBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hday [Hnext [Hzero Hcells]]]].
  unfold StockDaysDone in Hdone |- *.
  destruct Hdone as [Hshape [Hbounded [Hnonneg Hportfolio]]].
  split; [exact Hshape |]. split; [exact Hbounded |]. split; [lia |].
  intros d stock Hd Hstock.
  destruct (Z_lt_ge_dec d day) as [Hlt | Hge].
  - apply Hportfolio; [lia | exact Hstock].
  - assert (d = day) by lia. subst d.
    pose proof (Hportfolio (day - 1) stock ltac:(lia) Hstock) as Hold.
    destruct (Z.eq_dec stock 0) as [-> | Hstock0].
    + rewrite Hzero.
      apply stock_portfolio_no_first_buy__early_buy;
        try assumption; try lia.
    + specialize (Hcells stock ltac:(lia)).
      destruct (Z_lt_dec stock next_stock) as [Hprocessed | Huntouched].
      * rewrite Hcells.
        apply stock_portfolio_extend_first_buy__early_buy;
          try assumption; try lia; try reflexivity.
        unfold STOCK_NEG_INF. nia.
      * rewrite Hcells.
        apply stock_portfolio_no_first_buy__early_buy;
          try assumption; try lia.
Qed.

Lemma stock_early_buy_update_step__early_buy :
  forall ask bid buy sell table max_stock wait day next_stock value days,
    StockInputsBounded ask bid buy sell days max_stock ->
    StockEarlyBuyProgress ask bid buy sell table max_stock wait day next_stock ->
    1 <= day <= days ->
    1 <= next_stock <= Znth (day - 1) buy 0 ->
    value = Z.max (Znth next_stock (Znth (day - 1) table []) 0)
                  (- next_stock * Znth (day - 1) ask 0) ->
    let row' := replace_Znth next_stock value (Znth day table []) in
    let table' := replace_Znth day row' table in
    StockEarlyBuyProgress ask bid buy sell table' max_stock wait day
      (next_stock + 1) /\ StockTableShape table' days max_stock.
Proof.
  intros ask bid buy sell table max_stock wait day next_stock value days
    Hinputs Hprogress Hdaybound Hnextbound Hvalue row' table'.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as
    [Hasklen [Hbidlen [Hbuylen [Hselllen [Hdays [Hmax Hinput]]]]]].
  specialize (Hinput day Hdaybound).
  destruct Hinput as [Hask [Hbid [Hbuy Hsell]]].
  unfold StockEarlyBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hday1 [Hnext [Hzero Hcells]]]].
  unfold StockDaysDone in Hdone.
  destruct Hdone as [Hshape [Hbounded [Hdone0 Hportfolio]]].
  unfold StockTableShape in Hshape.
  destruct Hshape as [Htablelen Hrowlen].
  assert (Hdayidx : 0 <= day < Zlength ask + 1) by lia.
  assert (Hrowlength : Zlength (Znth day table []) = max_stock + 1).
  { apply Hrowlen. exact Hdayidx. }
  assert (Hrow'length : Zlength row' = max_stock + 1).
  { unfold row'. rewrite Zlength_replace_Znth. exact Hrowlength. }
  assert (Hshape' : StockTableShape table' (Zlength ask) max_stock).
  { unfold StockTableShape. split.
    - unfold table'. rewrite Zlength_replace_Znth. exact Htablelen.
    - intros r Hr. unfold table'. destruct (Z.eq_dec r day) as [-> | Hneq].
      + rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
        exact Hrow'length.
      + rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
        apply Hrowlen. exact Hr. }
  assert (Hbounded' : StockTableValuesBounded table' (Zlength ask) max_stock).
  { unfold StockTableValuesBounded in *.
    intros r stock Hr Hstock. unfold table'.
    destruct (Z.eq_dec r day) as [-> | Hneq].
    - rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
      unfold row'. destruct (Z.eq_dec stock next_stock) as [-> | Hstockneq].
      + rewrite Znth_replace_Znth_Same by (rewrite Hrowlength; lia).
        rewrite Hvalue.
        pose proof (Hbounded (day - 1) next_stock ltac:(lia) ltac:(lia)) as Hold.
        destruct (Z.max_spec
          (Znth next_stock (Znth (day - 1) table []) 0)
          (- next_stock * Znth (day - 1) ask 0)) as [[_ ->] | [_ ->]];
          [| exact Hold].
        unfold STOCK_NEG_INF, STOCK_MAX_PROFIT. nia.
      + rewrite Znth_replace_Znth_Diff by (try rewrite Hrowlength; lia).
        apply Hbounded; assumption.
    - rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      apply Hbounded; assumption. }
  assert (Hprevtable : Znth (day - 1) table' [] = Znth (day - 1) table []).
  { unfold table'. rewrite Znth_replace_Znth_Diff by
      (try rewrite Htablelen; lia). reflexivity. }
  split.
  - unfold StockEarlyBuyProgress. split.
    + unfold StockDaysDone. split; [exact Hshape' |].
      split; [exact Hbounded' |]. split; [exact Hdone0 |].
      intros r stock Hr Hstock. unfold table'.
      rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
      apply Hportfolio; assumption.
    + split; [exact Hday1 |]. split; [lia |]. split.
      * rewrite Hprevtable. unfold table', row'.
        rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
        rewrite Znth_replace_Znth_Diff by (try rewrite Hrowlength; lia).
        exact Hzero.
      * intros stock Hstock. rewrite Hprevtable. unfold table', row'.
        rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
        destruct (Z.eq_dec stock next_stock) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hrowlength; lia).
           destruct (Z_lt_dec next_stock (next_stock + 1)); [exact Hvalue | lia].
        -- rewrite Znth_replace_Znth_Diff by (try rewrite Hrowlength; lia).
           destruct (Z_lt_dec stock (next_stock + 1)) as [Hlt | Hge].
           ++ assert (stock < next_stock) by lia.
              specialize (Hcells stock Hstock).
              destruct (Z_lt_dec stock next_stock); [exact Hcells | lia].
           ++ specialize (Hcells stock Hstock).
              destruct (Z_lt_dec stock next_stock); [lia | exact Hcells].
  - rewrite <- Hasklen. exact Hshape'.
Qed.

Lemma StockSellQueueExpiring_empty__sell_expire:
  forall table queue source price lower upper head tail,
    StockSellQueueExpiring table queue source price lower upper head tail ->
    head >= tail ->
    StockSellQueue table queue source price lower upper head tail.
Proof.
  intros table queue source price lower upper head tail Hexp Hempty.
  unfold StockSellQueueExpiring in Hexp.
  destruct Hexp as [Hwide | Hnarrow]; [|exact Hnarrow].
  unfold StockSellQueue in Hwide |- *.
  unfold StockFiniteIndexInWindow in *.
  destruct Hwide as [Hbounds [_ [_ Hcover]]].
  split; [lia|].
  split.
  - intros pos Hpos. lia.
  - split.
    + intros left right Hlr. lia.
    + intros candidate Hcandidate.
      destruct (Hcover candidate) as [pos [Hpos _]].
      { destruct Hcandidate as [Hc0 [Hclen [Hcninf [Hclow Hcup]]]].
        split; [exact Hc0|].
        split; [exact Hclen|].
        split; [exact Hcninf|].
        split; [exact Hclow|].
        lia. }
      lia.
Qed.

Lemma StockSellQueueExpiring_head_bounded__sell_expire:
  forall table queue source price lower upper head tail,
    StockSellQueueExpiring table queue source price lower upper head tail ->
    head < tail ->
    Znth head queue 0 <= upper ->
    StockSellQueue table queue source price lower upper head tail.
Proof.
  intros table queue source price lower upper head tail Hexp Hht Hhead.
  unfold StockSellQueueExpiring in Hexp.
  destruct Hexp as [Hwide | Hnarrow]; [|exact Hnarrow].
  unfold StockSellQueue in Hwide |- *.
  unfold StockFiniteIndexInWindow in *.
  destruct Hwide as [Hbounds [Helems [Horder Hcover]]].
  split; [exact Hbounds|].
  split.
  - intros pos Hpos.
    pose proof (Helems pos Hpos) as HposElem.
    destruct HposElem as [Hp0 [Hplen [Hpninf [Hplow Hpwide]]]].
    split; [exact Hp0|].
    split; [exact Hplen|].
    split; [exact Hpninf|].
    split; [exact Hplow|].
    destruct (Z.eq_dec pos head) as [-> | Hne]; [exact Hhead|].
    pose proof (Horder head pos ltac:(lia)) as [Hdecrease _].
    lia.
  - split; [exact Horder|].
    intros candidate Hcandidate.
    apply Hcover.
    destruct Hcandidate as [Hc0 [Hclen [Hcninf [Hclow Hcup]]]].
    split; [exact Hc0|].
    split; [exact Hclen|].
    split; [exact Hcninf|].
    split; [exact Hclow|].
    lia.
Qed.

Lemma StockSellQueue_drop_expired__sell_expire:
  forall table queue source price lower upper head tail,
    StockSellQueueExpiring table queue source price lower upper head tail ->
    head < tail ->
    Znth head queue 0 > upper ->
    StockSellQueue table queue source price lower upper (head + 1) tail.
Proof.
  intros table queue source price lower upper head tail Hexp Hht Hexpired.
  unfold StockSellQueueExpiring in Hexp.
  destruct Hexp as [Hwide | Hnarrow].
  - unfold StockSellQueue in Hwide |- *.
    unfold StockFiniteIndexInWindow in *.
    destruct Hwide as [Hbounds [Helems [Horder Hcover]]].
    split; [lia|].
    split.
    + intros pos Hpos.
      pose proof (Helems head ltac:(lia)) as HheadElem.
      specialize (Helems pos ltac:(lia)).
      specialize (Horder head pos ltac:(lia)).
      destruct HheadElem as [_ [_ [_ [_ HheadUpper]]]].
      destruct Helems as [Hp0 [Hplen [Hpninf [Hplow Hpwide]]]].
      destruct Horder as [Hdecrease _].
      split; [exact Hp0|].
      split; [exact Hplen|].
      split; [exact Hpninf|].
      split; [exact Hplow|].
      lia.
    + split.
      * intros left right Hlr. apply Horder. lia.
      * intros candidate Hcandidate.
        destruct (Hcover candidate) as [pos [Hpos [Hindex Hscore]]].
        { destruct Hcandidate as [Hc0 [Hclen [Hcninf [Hclow Hcup]]]].
          split; [exact Hc0|].
          split; [exact Hclen|].
          split; [exact Hcninf|].
          split; [exact Hclow|].
          lia. }
        exists pos. split; [|split]; try assumption.
        assert (pos <> head).
        { intro Heq. subst pos. destruct Hcandidate as [_ [_ [_ [_ Hcup]]]]. lia. }
        lia.
  - unfold StockSellQueue in Hnarrow.
    unfold StockFiniteIndexInWindow in *.
    destruct Hnarrow as [Hbounds [Helems _]].
    specialize (Helems head ltac:(lia)).
    destruct Helems as [_ [_ [_ [_ Hupper]]]].
    lia.
Qed.

Lemma StockSellQueue_begin_popping__sell_pop_append :
  forall table queue source price incoming upper head tail,
    0 <= incoming ->
    incoming < Zlength (Znth source table []) ->
    Znth incoming (Znth source table []) 0 <> STOCK_NEG_INF ->
    StockSellQueue table queue source price (incoming + 1) upper head tail ->
    StockSellQueuePopping table queue source price incoming upper head tail.
Proof.
  intros table queue source price incoming upper head tail
    Hin0 Hinlen Hinne HQ.
  unfold StockSellQueue in HQ.
  unfold StockSellQueuePopping.
  unfold StockFiniteTableIndex, StockFiniteIndexInWindow in *.
  destruct HQ as [Hbounds [Hvalid [Hmono Hcover]]].
  split; [repeat split; assumption|].
  split; [exact Hbounds|].
  split.
  - intros pos Hpos.
    specialize (Hvalid pos Hpos).
    destruct Hvalid as [Hp0 [Hplen [Hpne Hrange]]].
    repeat split; try assumption; lia.
  - split; [exact Hmono|].
    intros candidate Hcandidate.
    destruct Hcandidate as [Hc0 [Hclen [Hcne Hrange]]].
    destruct (Z.eq_dec candidate incoming) as [Heq | Hneq].
    + left. subst candidate. lia.
    + right. apply Hcover.
      repeat split; try assumption; lia.
Qed.

Lemma StockSellQueuePopping_drop_tail__sell_pop_append :
  forall table queue source price incoming upper head tail,
    StockSellQueuePopping table queue source price incoming upper head tail ->
    head < tail ->
    StockSellScore table source price (Znth (tail - 1) queue 0) <=
      StockSellScore table source price incoming ->
    StockSellQueuePopping table queue source price incoming upper head (tail - 1).
Proof.
  intros table queue source price incoming upper head tail
    HP Hht Hscorelast.
  unfold StockSellQueuePopping in *.
  unfold StockFiniteTableIndex, StockFiniteIndexInWindow in *.
  destruct HP as [Hincoming [Hbounds [Hvalid [Hmono Hcover]]]].
  split; [exact Hincoming|].
  split; [lia|].
  split.
  - intros pos Hpos. apply Hvalid. lia.
  - split.
    + intros left right Hlr. apply Hmono. lia.
    + intros candidate Hcandidate.
    specialize (Hcover candidate Hcandidate).
    destruct Hcover as [Hbest | [pos [Hpos [Hidx Hscore]]]].
    * left. exact Hbest.
    * destruct (Z.eq_dec pos (tail - 1)) as [Heq | Hneq].
      -- left. subst pos. lia.
      -- right. exists pos. repeat split; try assumption; lia.
Qed.

Lemma StockBuyQueue_begin_popping__buy_pop_append :
  forall table queue source price lower incoming head tail,
    0 <= incoming ->
    incoming < Zlength (Znth source table []) ->
    Znth incoming (Znth source table []) 0 <> STOCK_NEG_INF ->
    StockBuyQueue table queue source price lower (incoming - 1) head tail ->
    StockBuyQueuePopping table queue source price lower incoming head tail.
Proof.
  intros table queue source price lower incoming head tail
    Hin0 Hinlen Hinne HQ.
  unfold StockBuyQueue in HQ.
  unfold StockBuyQueuePopping.
  unfold StockFiniteTableIndex, StockFiniteIndexInWindow in *.
  destruct HQ as [Hbounds [Hvalid [Hmono Hcover]]].
  split; [repeat split; assumption|].
  split; [exact Hbounds|].
  split.
  - intros pos Hpos.
    specialize (Hvalid pos Hpos).
    destruct Hvalid as [Hp0 [Hplen [Hpne Hrange]]].
    repeat split; try assumption; lia.
  - split; [exact Hmono|].
    intros candidate Hcandidate.
    destruct Hcandidate as [Hc0 [Hclen [Hcne Hrange]]].
    destruct (Z.eq_dec candidate incoming) as [Heq | Hneq].
    + left. subst candidate. lia.
    + right. apply Hcover.
      repeat split; try assumption; lia.
Qed.

Lemma StockBuyQueuePopping_drop_tail__buy_pop_append :
  forall table queue source price lower incoming head tail,
    StockBuyQueuePopping table queue source price lower incoming head tail ->
    head < tail ->
    StockBuyScore table source price (Znth (tail - 1) queue 0) <=
      StockBuyScore table source price incoming ->
    StockBuyQueuePopping table queue source price lower incoming head (tail - 1).
Proof.
  intros table queue source price lower incoming head tail
    HP Hht Hscorelast.
  unfold StockBuyQueuePopping in *.
  unfold StockFiniteTableIndex, StockFiniteIndexInWindow in *.
  destruct HP as [Hincoming [Hbounds [Hvalid [Hmono Hcover]]]].
  split; [exact Hincoming|].
  split; [lia|].
  split.
  - intros pos Hpos. apply Hvalid. lia.
  - split.
    + intros left right Hlr. apply Hmono. lia.
    + intros candidate Hcandidate.
    specialize (Hcover candidate Hcandidate).
    destruct Hcover as [Hbest | [pos [Hpos [Hidx Hscore]]]].
    * left. exact Hbest.
    * destruct (Z.eq_dec pos (tail - 1)) as [Heq | Hneq].
      -- left. subst pos. lia.
      -- right. exists pos. repeat split; try assumption; lia.
Qed.

Lemma StockBuyQueue_extend_invalid__buy_cell_progress :
  forall table queue source price lower upper head tail,
    StockBuyQueue table queue source price lower (upper - 1) head tail ->
    0 <= upper < Zlength (Znth source table []) ->
    Znth upper (Znth source table []) 0 = STOCK_NEG_INF ->
    StockBuyQueue table queue source price lower upper head tail.
Proof.
  intros table queue source price lower upper head tail Hqueue Hupper Hinvalid.
  unfold StockBuyQueue in *.
  unfold StockFiniteIndexInWindow in *.
  destruct Hqueue as [Hheads [Hentries [Horder Hdom]]].
  split; [exact Hheads|].
  split.
  - intros pos Hpos.
    specialize (Hentries pos Hpos).
    destruct Hentries as [Hnonneg [Hlt [Hfinite Hbounds]]].
    repeat split; try assumption; lia.
  - split; [exact Horder|].
    intros candidate Hcandidate.
    destruct Hcandidate as [Hnonneg [Hlt [Hfinite Hbounds]]].
    assert (candidate <> upper).
    { intro Heq. subst candidate. contradiction. }
    apply Hdom. repeat split; try assumption; lia.
Qed.

Lemma StockBuyCellValue_empty_queue__buy_cell_progress :
  forall ask bid buy sell table max_stock wait day source stock
         queue price buy_cap head tail,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock ->
    stock <= max_stock ->
    stock < Zlength (Znth source table []) ->
    StockBuyQueue table queue source price
      (stock - buy_cap) (stock - 1) head tail ->
    head >= tail ->
    buy_cap = Znth (day - 1) buy 0 ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock
      (Znth stock (Znth day table []) 0).
Proof.
  intros ask bid buy sell table max_stock wait day source stock
    queue price buy_cap head tail Hprogress Hstock_bound Hstock_len
    Hqueue Hempty Hcap.
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [_ [_ [_ [_ [_ [_ Hsell]]]]]].
  specialize (Hsell stock ltac:(lia)).
  unfold StockBuyQueue in Hqueue.
  unfold StockFiniteIndexInWindow in *.
  destruct Hqueue as [_ [_ [_ Hdom]]].
  unfold StockBuyCellValue.
  split.
  - split.
    + exists 0. unfold StockBuyCandidate. left. auto.
    + intros amount candidate Hcandidate.
      unfold StockBuyCandidate in Hcandidate.
      destruct Hcandidate as [[Hzero Hsell_candidate] | Hpositive].
      * destruct Hsell as [Hexists Hmax].
        destruct Hsell_candidate as [[sell_amount Hsell_witness] _].
        subst amount. apply (Hmax sell_amount candidate Hsell_witness).
      * destruct Hpositive as [Hamount [Hstock [Hfinite Hvalue]]].
        specialize (Hdom (stock - amount) ltac:(repeat split; try assumption; lia)).
        destruct Hdom as [pos [Hpos _]]. lia.
  - exists (Znth stock (Znth day table []) 0). exact Hsell.
Qed.

Lemma StockBuyProgress_step_same__buy_cell_progress :
  forall ask bid buy sell table max_stock wait day source stock,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock ->
    stock <= max_stock ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock
      (Znth stock (Znth day table []) 0) ->
    StockBuyProgress ask bid buy sell table max_stock wait day source (stock + 1).
Proof.
  intros ask bid buy sell table max_stock wait day source stock
    Hprogress Hbound Hcell.
  unfold StockBuyProgress in *.
  destruct Hprogress as [Hdone [Hday [Hsource [Hsrange [Hstock [Hbuy Hsell]]]]]].
  split; [exact Hdone|].
  split; [exact Hday|].
  split; [exact Hsource|].
  split; [exact Hsrange|].
  split; [lia|].
  split.
  - intros k Hk. destruct (Z_lt_ge_dec k stock).
    + apply Hbuy. lia.
    + assert (k = stock) by lia. subst k. exact Hcell.
  - intros k Hk. apply Hsell. lia.
Qed.

Lemma stock_answer_init__outer_answer :
  forall ask bid buy sell table days max_stock wait i,
    0 <= max_stock -> i > days -> i <= days + 1 ->
    StockDaysDone ask bid buy sell table max_stock wait i ->
    StockAnswerProgress ask bid buy sell table days max_stock wait 0 0.
Proof.
  intros ask bid buy sell table days max_stock wait i Hmax Hi Hile Hdone.
  assert (i = days + 1) by lia. subst i.
  unfold StockAnswerProgress.
  split; [exact Hdone|]. split; [lia|]. split; [lia|].
  left; split; reflexivity.
Qed.

Lemma stock_answer_improve__outer_answer :
  forall ask bid buy sell table days max_stock wait j answer value,
    0 <= days -> 0 <= answer -> j <= max_stock ->
    StockAnswerProgress ask bid buy sell table days max_stock wait j answer ->
    value = Znth j (Znth days table nil) 0 ->
    value > answer ->
    StockAnswerProgress ask bid buy sell table days max_stock wait (j + 1) value.
Proof.
  intros ask bid buy sell table days max_stock wait j answer value
    Hdays Hans Hj Hprogress Hvalue Hgt.
  unfold StockAnswerProgress in Hprogress |- *.
  destruct Hprogress as [Hdone [Hjrange [Hans0 Hprefix]]].
  split; [exact Hdone|]. split; [lia|].
  assert (Hcell : StockPortfolioValue ask bid buy sell max_stock wait days j value).
  { unfold StockDaysDone in Hdone.
    destruct Hdone as [_ [_ [_ Hall]]].
    rewrite Hvalue. apply Hall; lia. }
  assert (Hfeasible : StockFeasiblePortfolio ask bid buy sell max_stock wait days j value).
  { unfold StockPortfolioValue in Hcell.
    destruct Hcell as [_ [[Hneg Hnone] | [Hfeas Hmax]]].
    - unfold STOCK_NEG_INF in Hneg. lia.
    - exact Hfeas. }
  assert (Hmaxcell : forall profit,
    StockFeasiblePortfolio ask bid buy sell max_stock wait days j profit ->
    profit <= value).
  { intros profit Hf. unfold StockPortfolioValue in Hcell.
    destruct Hcell as [_ [[Hneg Hnone] | [Hfeas Hmax]]].
    - exfalso. apply Hnone. exists profit. exact Hf.
    - apply Hmax. exact Hf. }
  split; [lia|]. right. split; [lia|]. split.
  - exists j. split; [lia|exact Hfeasible].
  - intros stock profit Hstock Hf.
    destruct (Z_lt_ge_dec stock j) as [Hlt|Hge].
    + destruct Hprefix as [[Hj0 _]|[Hjpos [_ Hold]]]; [lia|].
      pose proof (Hold stock profit ltac:(lia) Hf). lia.
    + assert (stock = j) by lia. subst stock. apply Hmaxcell; exact Hf.
Qed.

Lemma stock_answer_keep__outer_answer :
  forall ask bid buy sell table days max_stock wait j answer value,
    0 <= days -> j <= max_stock ->
    StockAnswerProgress ask bid buy sell table days max_stock wait j answer ->
    value = Znth j (Znth days table nil) 0 ->
    value <= answer ->
    StockAnswerProgress ask bid buy sell table days max_stock wait (j + 1) answer.
Proof.
  intros ask bid buy sell table days max_stock wait j answer value
    Hdays Hj Hprogress Hvalue Hle.
  unfold StockAnswerProgress in Hprogress |- *.
  destruct Hprogress as [Hdone [Hjrange [Hans Hprefix]]].
  split; [exact Hdone|]. split; [lia|]. split; [exact Hans|].
  assert (Hcell : StockPortfolioValue ask bid buy sell max_stock wait days j value).
  { unfold StockDaysDone in Hdone.
    destruct Hdone as [_ [_ [_ Hall]]].
    rewrite Hvalue. apply Hall; lia. }
  right. split; [lia|].
  destruct Hprefix as [[Hj0 Hans0]|[Hjpos [Hex Hold]]].
  - subst j answer. split.
    + exists 0. split; [lia|]. unfold StockFeasiblePortfolio. left. tauto.
    + intros stock profit Hstock Hf. assert (stock = 0) by lia. subst stock.
      unfold StockPortfolioValue in Hcell.
      destruct Hcell as [_ [[_ Hnone]|[_ Hmax]]].
      * exfalso. apply Hnone. exists profit. exact Hf.
      * specialize (Hmax profit Hf). lia.
  - split.
    + destruct Hex as [stock [Hstock Hf]]. exists stock. split; [lia|exact Hf].
    + intros stock profit Hstock Hf.
      destruct (Z_lt_ge_dec stock j) as [Hlt|Hge].
      * eapply Hold; eauto; lia.
      * assert (stock = j) by lia. subst stock.
        unfold StockPortfolioValue in Hcell.
        destruct Hcell as [_ [[_ Hnone]|[_ Hmax]]].
        -- exfalso. apply Hnone. exists profit. exact Hf.
        -- specialize (Hmax profit Hf). lia.
Qed.

Lemma stock_answer_finish__outer_answer :
  forall ask bid buy sell table days max_stock wait j answer,
    0 <= max_stock -> j > max_stock -> j <= max_stock + 1 ->
    StockAnswerProgress ask bid buy sell table days max_stock wait j answer ->
    StockMaximumProfit ask bid buy sell days max_stock wait answer.
Proof.
  intros ask bid buy sell table days max_stock wait j answer Hmaxstock Hj Hle Hprogress.
  assert (j = max_stock + 1) by lia. subst j.
  unfold StockAnswerProgress in Hprogress.
  destruct Hprogress as [_ [_ [_ Hprefix]]].
  destruct Hprefix as [[Hbad _]|[_ [Hex Hmax]]]; [lia|].
  destruct Hex as [stock [Hstock Hfeas]].
  unfold StockMaximumProfit. exists stock. repeat split; try lia; try exact Hfeas.
  intros stock' profit Hstock' Hf.
  apply (Hmax stock' profit); [lia|exact Hf].
Qed.

Lemma StockSellCellValue_empty_queue :
  forall bid sell sell_cap table max_stock day source stock queue head tail,
    0 <= stock ->
    stock < max_stock ->
    head >= tail ->
    Znth (day - 1) sell 0 = sell_cap ->
    0 <= source < day ->
    StockTableShape table day max_stock ->
    (forall k, 0 <= k <= stock ->
      Znth k (Znth day table []) 0 = Znth k (Znth (day - 1) table []) 0) ->
    StockSellQueue table queue source (Znth (day - 1) bid 0) (stock + 1) (stock + sell_cap) head tail ->
    StockSellCellValue bid sell table max_stock day source stock
      (Znth stock (Znth day table []) 0).
Proof.
  intros bid sell sell_cap table max_stock day source stock queue head tail
    Hstock_low Hstock_high Hempty Hsell_cap Hsource_range Hshape Hcopy Hqueue.
  unfold StockSellCellValue; split.
  { exists 0; unfold StockSellCandidate; left.
    split; [reflexivity|]; specialize (Hcopy stock ltac:(lia)); exact Hcopy. }
  { intros amount candidate Hcand.
    unfold StockSellCandidate in Hcand.
    destruct Hcand as [[Hzero Hcopy_val] | Hpositive].
    { rewrite Hcopy_val; specialize (Hcopy stock ltac:(lia)); rewrite Hcopy; lia. }
    { destruct Hpositive as [Hamt_bound [Hstock_bound2 [Hfinite Hval]]].
      unfold StockSellQueue in Hqueue.
      unfold StockFiniteIndexInWindow in *.
      destruct Hqueue as [Hhead_tail [Helems [Hmono Hcoverage]]].
      unfold StockTableShape in Hshape.
      destruct Hshape as [Htable_len Hrow_len].
      specialize (Hrow_len source ltac:(lia)).
      assert (Hk_range : 0 <= stock + amount /\
        stock + amount < Zlength (Znth source table []) /\
        Znth (stock + amount) (Znth source table []) 0 <> STOCK_NEG_INF /\
        stock + 1 <= stock + amount <= stock + sell_cap)
        by (split; [lia|split; [rewrite Hrow_len; lia|split; [exact Hfinite|split; lia]]]).
      specialize (Hcoverage (stock + amount) Hk_range).
      destruct Hcoverage as [pos [Hpos_range _]].
      lia. } }
Qed.

Lemma StockSellQueuePending_append__sell_pop_append :
  forall table queue source price incoming upper head tail,
    incoming <= upper ->
    StockSellQueuePending table queue source price incoming upper head tail ->
    StockSellQueue table (replace_Znth tail incoming queue)
      source price incoming upper head (tail + 1).
Proof.
  intros table queue source price incoming upper head tail Hiu HP.
  unfold StockSellQueuePending in HP.
  destruct HP as [Hpop [Htail Hlast]].
  unfold StockSellQueuePopping in Hpop.
  destruct Hpop as [Hincoming [Hbounds [Hvalid [Hmono Hcover]]]].
  unfold StockSellQueue.
  split; [lia|].
  split.
  - intros pos Hpos.
    destruct (Z.eq_dec pos tail) as [-> | Hne].
    + rewrite Znth_replace_Znth_Same by lia.
      unfold StockFiniteTableIndex in Hincoming.
      unfold StockFiniteIndexInWindow.
      destruct Hincoming as [Hi0 [Hilen Hine]].
      repeat split; try assumption; lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hvalid pos ltac:(lia)).
      unfold StockFiniteIndexInWindow in *.
      lia.
  - split.
    + intros left right Hlr.
      destruct Hlr as [[Hhead Hleft] Hright].
      destruct (Z.eq_dec right tail) as [-> | Hrightne].
      * rewrite Znth_replace_Znth_Same by lia.
        rewrite Znth_replace_Znth_Diff by lia.
        specialize (Hvalid left ltac:(lia)).
        unfold StockFiniteIndexInWindow in Hvalid.
        pose proof (Hlast ltac:(lia)) as Hlastscore.
        destruct (Z.eq_dec left (tail - 1)) as [-> | Hleftne].
        -- lia.
        -- pose proof (Hmono left (tail - 1) ltac:(lia)) as Hord.
           lia.
      * rewrite !Znth_replace_Znth_Diff by lia.
        apply Hmono. lia.
    + intros candidate Hcandidate.
      specialize (Hcover candidate Hcandidate).
      destruct Hcover as [Hbest | [pos [Hpos [Hindex Hscore]]]].
      * exists tail.
        rewrite Znth_replace_Znth_Same by lia.
        unfold StockFiniteIndexInWindow in Hcandidate.
        lia.
      * exists pos.
        rewrite Znth_replace_Znth_Diff by lia.
        lia.
Qed.

Lemma stock_sell_queue_extend_lower_neg_inf__sell_cell_progress :
  forall table queue source price lower upper head tail,
    Znth lower (Znth source table []) 0 = STOCK_NEG_INF ->
    StockSellQueue table queue source price (lower + 1) upper head tail ->
    StockSellQueue table queue source price lower upper head tail.
Proof.
  intros table queue source price lower upper head tail Hneg Hqueue.
  unfold StockSellQueue in *.
  destruct Hqueue as [Hht [Hentries [Horder Hcover]]].
  split; [exact Hht |].
  split.
  - intros pos Hpos.
    specialize (Hentries pos Hpos).
    unfold StockFiniteIndexInWindow in *.
    destruct Hentries as [Hnonneg [Hlen [Hfinite Hrange]]].
    repeat split; try assumption; lia.
  - split; [exact Horder |].
    intros candidate Hcandidate.
    unfold StockFiniteIndexInWindow in Hcandidate.
    destruct Hcandidate as [Hnonneg [Hlen [Hfinite Hrange]]].
    assert (candidate <> lower).
    { intro Heq. subst candidate. apply Hfinite. exact Hneg. }
    apply Hcover.
    unfold StockFiniteIndexInWindow.
    repeat split; try assumption; lia.
Qed.

Lemma stock_trading_history_profit_bound__sell_cell_progress :
  forall ask bid buy sell max_stock wait day stock profit days,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    day <= days ->
    StockTradingHistory ask bid buy sell max_stock wait day stock profit ->
    - (day * max_stock * 1000) <= profit <= day * max_stock * 1000.
Proof.
  intros ask bid buy sell max_stock wait day stock profit days
    Hinputs Hwait Hday Hhist.
  induction Hhist.
  - unfold StockInputsBounded in Hinputs.
    destruct Hinputs as [_ [_ [_ [_ [_ [Hmax Hvals]]]]]].
    specialize (Hvals day ltac:(lia)).
    destruct Hvals as [Hbid [Hask [Hbuy Hsell]]].
    nia.
  - specialize (IHHhist ltac:(lia)).
    pose proof (stock_trading_history_day_positive__init_copy
      ask bid buy sell max_stock wait previous_day previous_stock
      previous_profit Hwait Hhist) as Hprevday.
    unfold StockInputsBounded in Hinputs.
    destruct Hinputs as [_ [_ [_ [_ [_ [Hmax Hvals]]]]]].
    specialize (Hvals day ltac:(lia)).
    destruct Hvals as [Hbid [Hask [Hbuy Hsell]]].
    nia.
  - specialize (IHHhist ltac:(lia)).
    pose proof (stock_trading_history_day_positive__init_copy
      ask bid buy sell max_stock wait previous_day previous_stock
      previous_profit Hwait Hhist) as Hprevday.
    unfold StockInputsBounded in Hinputs.
    destruct Hinputs as [_ [_ [_ [_ [_ [Hmax Hvals]]]]]].
    specialize (Hvals day ltac:(lia)).
    destruct Hvals as [Hbid [Hask [Hbuy Hsell]]].
    nia.
Qed.

Lemma StockBuyQueuePending_append__buy_pop_append :
  forall table queue source price lower incoming head tail,
    StockBuyQueuePending table queue source price lower incoming head tail ->
    lower <= incoming ->
    StockBuyQueue table (replace_Znth tail incoming queue)
      source price lower incoming head (tail + 1).
Proof.
  intros table queue source price lower incoming head tail HP Hlower.
  unfold StockBuyQueuePending in HP.
  destruct HP as [HP [Hcapacity Hstrict]].
  unfold StockBuyQueuePopping in HP.
  destruct HP as [Hincoming [Hbounds [Hvalid [Horder Hcover]]]].
  unfold StockBuyQueue.
  split; [lia |].
  split.
  - intros pos Hpos.
    destruct (Z.eq_dec pos tail) as [Heq | Hneq].
    + subst pos. rewrite Znth_replace_Znth_Same by lia.
      unfold StockFiniteTableIndex in Hincoming.
      unfold StockFiniteIndexInWindow.
      repeat split; try tauto; lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      pose proof (Hvalid pos ltac:(lia)) as Hold.
      unfold StockFiniteIndexInWindow in *.
      destruct Hold as [H0 [Hlen [Hfinite Hrange]]].
      repeat split; try assumption; lia.
  - split.
    + intros left right Hlr.
      destruct (Z.eq_dec right tail) as [Heq | Hneq].
      * subst right.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Znth_replace_Znth_Diff by lia.
        pose proof (Hvalid left ltac:(lia)) as Hleft.
        unfold StockFiniteIndexInWindow in Hleft.
        destruct Hleft as [_ [_ [_ Hleft_range]]].
        split; [lia |].
        destruct (Z.eq_dec left (tail - 1)) as [Hlast | Hbefore].
        -- subst left. specialize (Hstrict ltac:(lia)). lia.
        -- pose proof (Horder left (tail - 1) ltac:(lia)) as [_ Hscore].
           specialize (Hstrict ltac:(lia)). lia.
      * repeat rewrite Znth_replace_Znth_Diff by lia.
        apply Horder. lia.
    + intros candidate Hcandidate.
      specialize (Hcover candidate Hcandidate).
      destruct Hcover as [Hincoming_best | [pos [Hpos [Hindex Hscore]]]].
      * exists tail. split; [lia |].
        rewrite Znth_replace_Znth_Same by lia.
        unfold StockFiniteIndexInWindow in Hcandidate.
        destruct Hcandidate as [_ [_ [_ Hrange]]].
        split; [lia | exact Hincoming_best].
      * exists pos. split; [lia |].
        rewrite Znth_replace_Znth_Diff by lia.
        split; assumption.
Qed.

Lemma StockBuyCellValue_improve__buy_cell_progress :
  forall ask bid buy sell table max_stock wait day source stock
         queue price buy_cap head tail best value,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock ->
    stock <= max_stock ->
    StockBuyQueue table queue source price
      (stock - buy_cap) (stock - 1) head tail ->
    head < tail ->
    best = Znth head queue 0 ->
    buy_cap = Znth (day - 1) buy 0 ->
    price = Znth (day - 1) ask 0 ->
    value = StockBuyScore table source price best - stock * price ->
    Znth stock (Znth day table []) 0 < value ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value.
Proof.
  intros ask bid buy sell table max_stock wait day source stock queue price
    buy_cap head tail best value Hprogress Hstockmax Hqueue Hnonempty Hbest Hcap
    Hprice Hvalue Himprove.
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hday [_ [Hsrange [_ [_ Hsell]]]]]].
  specialize (Hsell stock ltac:(lia)).
  assert (Hrowlen : Zlength (Znth source table []) = max_stock + 1).
  { unfold StockDaysDone in Hdone.
    destruct Hdone as [Hshape _]. unfold StockTableShape in Hshape.
    destruct Hshape as [_ Hrows]. apply Hrows. lia. }
  unfold StockBuyQueue in Hqueue.
  destruct Hqueue as [Hheads [Hentries [Horder Hdom]]].
  subst best.
  pose proof (Hentries head ltac:(lia)) as Hheadentry.
  unfold StockFiniteIndexInWindow in Hheadentry.
  destruct Hheadentry as [Hbest0 [Hbestlen [Hbestfinite [Hbestlow Hbesthigh]]]].
  assert (HcandidateEq :
    value = Znth (Znth head queue 0) (Znth source table []) 0 -
      (stock - Znth head queue 0) * Znth (day - 1) ask 0).
  { rewrite <- Hprice. unfold StockBuyScore in Hvalue.
    rewrite Z.mul_sub_distr_r. nia. }
  unfold StockBuyCellValue.
  split.
  - split.
    + exists (stock - Znth head queue 0).
      unfold StockBuyCandidate. right.
      split; [lia|].
      split; [lia|].
      split.
      { replace (stock - (stock - Znth head queue 0)) with
          (Znth head queue 0) by lia. exact Hbestfinite. }
      replace (stock - (stock - Znth head queue 0)) with
        (Znth head queue 0) by lia. exact HcandidateEq.
    + intros amount candidate Hcandidate.
      unfold StockBuyCandidate in Hcandidate.
      destruct Hcandidate as [[Hzero Hsellcandidate] | Hpositive].
      * subst amount.
        destruct Hsell as [_ Hsellmax].
        destruct Hsellcandidate as [[sell_amount Hsellwitness] _].
        specialize (Hsellmax sell_amount candidate Hsellwitness). lia.
      * destruct Hpositive as [Hamount [Hstock [Hfinite Hcandidate_value]]].
        assert (Hwindow : StockFiniteIndexInWindow table source
          (stock - buy_cap) (stock - 1) (stock - amount)).
        { unfold StockFiniteIndexInWindow.
          split; [lia|]. split; [rewrite Hrowlen; lia|].
          split; [exact Hfinite|]. split; lia. }
        destruct (Hdom (stock - amount) Hwindow)
          as [pos [Hpos [_ Hscore]]].
        assert (Hheadscore :
          StockBuyScore table source price (Znth pos queue 0) <=
          StockBuyScore table source price (Znth head queue 0)).
        { destruct (Z.eq_dec pos head) as [Heq | Hneq].
          - subst pos. lia.
          - pose proof (Horder head pos ltac:(lia)) as [_ Hord].
            lia. }
        unfold StockBuyScore in Hscore, Hheadscore, Hvalue.
        rewrite <- Hprice in Hcandidate_value.
        lia.
  - exists (Znth stock (Znth day table []) 0). exact Hsell.
Qed.

Lemma StockBuyCellValue_keep__buy_cell_progress :
  forall ask bid buy sell table max_stock wait day source stock
         queue price buy_cap head tail best value,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock ->
    stock <= max_stock ->
    StockBuyQueue table queue source price
      (stock - buy_cap) (stock - 1) head tail ->
    head < tail ->
    best = Znth head queue 0 ->
    buy_cap = Znth (day - 1) buy 0 ->
    price = Znth (day - 1) ask 0 ->
    value = StockBuyScore table source price best - stock * price ->
    value <= Znth stock (Znth day table []) 0 ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock
      (Znth stock (Znth day table []) 0).
Proof.
  intros ask bid buy sell table max_stock wait day source stock queue price
    buy_cap head tail best value Hprogress Hstockmax Hqueue Hnonempty Hbest Hcap
    Hprice Hvalue Hkeep.
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hday [_ [Hsrange [_ [_ Hsell]]]]]].
  specialize (Hsell stock ltac:(lia)).
  assert (Hrowlen : Zlength (Znth source table []) = max_stock + 1).
  { unfold StockDaysDone in Hdone.
    destruct Hdone as [Hshape _]. unfold StockTableShape in Hshape.
    destruct Hshape as [_ Hrows]. apply Hrows. lia. }
  unfold StockBuyQueue in Hqueue.
  destruct Hqueue as [Hheads [Hentries [Horder Hdom]]].
  subst best.
  unfold StockBuyCellValue.
  split.
  - split.
    + exists 0. unfold StockBuyCandidate. left. auto.
    + intros amount candidate Hcandidate.
      unfold StockBuyCandidate in Hcandidate.
      destruct Hcandidate as [[Hzero Hsellcandidate] | Hpositive].
      * subst amount. destruct Hsell as [_ Hsellmax].
        destruct Hsellcandidate as [[sell_amount Hsellwitness] _].
        apply (Hsellmax sell_amount candidate Hsellwitness).
      * destruct Hpositive as [Hamount [Hstock [Hfinite Hcandidate_value]]].
        assert (Hwindow : StockFiniteIndexInWindow table source
          (stock - buy_cap) (stock - 1) (stock - amount)).
        { unfold StockFiniteIndexInWindow.
          split; [lia|]. split; [rewrite Hrowlen; lia|].
          split; [exact Hfinite|]. split; lia. }
        destruct (Hdom (stock - amount) Hwindow)
          as [pos [Hpos [_ Hscore]]].
        assert (Hheadscore :
          StockBuyScore table source price (Znth pos queue 0) <=
          StockBuyScore table source price (Znth head queue 0)).
        { destruct (Z.eq_dec pos head) as [Heq | Hneq].
          - subst pos. lia.
          - pose proof (Horder head pos ltac:(lia)) as [_ Hord].
            lia. }
        unfold StockBuyScore in Hscore, Hheadscore, Hvalue.
        rewrite <- Hprice in Hcandidate_value.
        lia.
  - exists (Znth stock (Znth day table []) 0). exact Hsell.
Qed.

Lemma StockDaysDone_lookup_portfolio__buy_semantics :
  forall ask bid buy sell table max_stock wait next_day day stock,
    StockDaysDone ask bid buy sell table max_stock wait next_day ->
    0 <= day < next_day ->
    0 <= stock <= max_stock ->
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (Znth stock (Znth day table []) 0).
Proof.
  intros ask bid buy sell table max_stock wait next_day day stock
    Hdone Hday Hstock.
  unfold StockDaysDone in Hdone.
  destruct Hdone as [_ [_ [_ Hportfolio]]].
  apply Hportfolio; assumption.
Qed.

Lemma StockPortfolioValue_dominates__buy_semantics :
  forall ask bid buy sell max_stock wait day stock value profit,
    StockPortfolioValue ask bid buy sell max_stock wait day stock value ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit ->
    profit <= value.
Proof.
  intros ask bid buy sell max_stock wait day stock value profit
    Hvalue Hfeasible.
  unfold StockPortfolioValue in Hvalue.
  destruct Hvalue as [_ [[_ Hnone] | [_ Hmax]]].
  - exfalso. apply Hnone. exists profit. exact Hfeasible.
  - apply Hmax. exact Hfeasible.
Qed.

Lemma StockPortfolioValue_finite__buy_semantics :
  forall ask bid buy sell max_stock wait day stock value,
    StockPortfolioValue ask bid buy sell max_stock wait day stock value ->
    value <> STOCK_NEG_INF ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock value.
Proof.
  intros ask bid buy sell max_stock wait day stock value Hvalue Hfinite.
  unfold StockPortfolioValue in Hvalue.
  destruct Hvalue as [_ [[Heq _] | [Hfeasible _]]].
  - contradiction.
  - exact Hfeasible.
Qed.

Lemma StockTradingHistory_stock_bounded__buy_semantics :
  forall ask bid buy sell max_stock wait day stock profit,
    StockTradingHistory ask bid buy sell max_stock wait day stock profit ->
    0 <= stock <= max_stock.
Proof.
  intros ask bid buy sell max_stock wait day stock profit Hhistory.
  induction Hhistory; lia.
Qed.

Lemma StockTradingHistory_profit_range__buy_semantics :
  forall ask bid buy sell days max_stock wait day stock profit,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    day <= days ->
    StockTradingHistory ask bid buy sell max_stock wait day stock profit ->
    STOCK_NEG_INF < profit < STOCK_MAX_PROFIT.
Proof.
  intros ask bid buy sell days max_stock wait day stock profit
    Hinputs Hwait Hday Hhistory.
  pose proof Hinputs as Hbounds.
  unfold StockInputsBounded in Hbounds.
  destruct Hbounds as
    [Hask [Hbid [Hbuy [Hsell [Hdays [Hmax Hvalues]]]]]].
  assert (Hcoarse :
    - day * max_stock * 1000 <= profit <= day * max_stock * 1000).
  { revert Hday.
    induction Hhistory; intros Hcurrent.
    - specialize (Hvalues day ltac:(lia)).
      destruct Hvalues as [Hbidask [Haskprice [Hbuylimit _]]].
      assert (Htrade :
        0 <= amount * Znth (day - 1) ask 0 <= max_stock * 1000).
      { split.
        - apply Z.mul_nonneg_nonneg; lia.
        - apply Z.mul_le_mono_nonneg; lia. }
      assert (Hdayscale : max_stock * 1000 <= day * max_stock * 1000)
        by nia.
      nia.
    - assert (Hprevious : previous_day <= days) by lia.
      specialize (IHHhistory Hprevious).
      pose proof (stock_trading_history_day_positive__init_copy
        ask bid buy sell max_stock wait previous_day previous_stock
        previous_profit Hwait Hhistory) as Hprevious_positive.
      specialize (Hvalues day ltac:(lia)).
      destruct Hvalues as [Hbidask [Haskprice [Hbuylimit _]]].
      assert (Htrade :
        0 <= amount * Znth (day - 1) ask 0 <= max_stock * 1000).
      { split.
        - apply Z.mul_nonneg_nonneg; lia.
        - apply Z.mul_le_mono_nonneg; lia. }
      assert (Hstep :
        previous_day * max_stock * 1000 + max_stock * 1000 <=
        day * max_stock * 1000) by nia.
      nia.
    - assert (Hprevious : previous_day <= days) by lia.
      specialize (IHHhistory Hprevious).
      pose proof (stock_trading_history_day_positive__init_copy
        ask bid buy sell max_stock wait previous_day previous_stock
        previous_profit Hwait Hhistory) as Hprevious_positive.
      specialize (Hvalues day ltac:(lia)).
      destruct Hvalues as [Hbidprice [Haskprice [_ Hselllimit]]].
      assert (Htrade :
        0 <= amount * Znth (day - 1) bid 0 <= max_stock * 1000).
      { split.
        - apply Z.mul_nonneg_nonneg; lia.
        - apply Z.mul_le_mono_nonneg; lia. }
      assert (Hstep :
        previous_day * max_stock * 1000 + max_stock * 1000 <=
        day * max_stock * 1000) by nia.
      nia. }
  unfold STOCK_NEG_INF, STOCK_MAX_PROFIT.
  nia.
Qed.

Lemma StockFeasiblePortfolio_profit_range__buy_semantics :
  forall ask bid buy sell days max_stock wait horizon stock profit,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    horizon <= days ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait horizon stock profit ->
    STOCK_NEG_INF < profit < STOCK_MAX_PROFIT.
Proof.
  intros ask bid buy sell days max_stock wait horizon stock profit
    Hinputs Hwait Hhorizon Hfeasible.
  unfold StockFeasiblePortfolio in Hfeasible.
  destruct Hfeasible as [[_ ->] | [last_day [[_ Hlast] Hhistory]]].
  - unfold STOCK_NEG_INF, STOCK_MAX_PROFIT. lia.
  - eapply (StockTradingHistory_profit_range__buy_semantics
      ask bid buy sell days max_stock wait last_day stock profit);
      eauto; lia.
Qed.

Lemma StockFeasiblePortfolio_mono_horizon__buy_semantics :
  forall ask bid buy sell max_stock wait h1 h2 stock profit,
    h1 <= h2 ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait h1 stock profit ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait h2 stock profit.
Proof.
  intros ask bid buy sell max_stock wait h1 h2 stock profit Hle Hfeasible.
  unfold StockFeasiblePortfolio in *.
  destruct Hfeasible as [Hzero | [last_day [Hlast Hhistory]]].
  - left. exact Hzero.
  - right. exists last_day. split; [lia|exact Hhistory].
Qed.

Lemma StockSellCellValue_sound__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    1 <= day ->
    day <= days ->
    source = day - wait - 1 ->
    0 < source < day ->
    0 <= stock <= max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait day ->
    StockSellCellValue bid sell table max_stock day source stock value ->
    value = STOCK_NEG_INF \/
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock value.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hwait Hdaypos Hday Hsource Hsource_day Hstock Hdone Hcell.
  unfold StockSellCellValue in Hcell.
  destruct Hcell as [[amount Hcandidate] _].
  unfold StockSellCandidate in Hcandidate.
  destruct Hcandidate as [[-> Hvalue] |
    [Hamount [Hstockmax [Hfinite Hvalue]]]].
  - pose proof (StockDaysDone_lookup_portfolio__buy_semantics
      ask bid buy sell table max_stock wait day (day - 1) stock
      Hdone ltac:(lia) Hstock) as Hprevious.
    unfold StockPortfolioValue in Hprevious.
    destruct Hprevious as [_ [[Hneg _] | [Hfeasible _]]].
    + left. lia.
    + right. rewrite Hvalue.
      exact (StockFeasiblePortfolio_mono_horizon__buy_semantics
        ask bid buy sell max_stock wait (day - 1) day stock
        (Znth stock (Znth (day - 1) table []) 0)
        ltac:(lia) Hfeasible).
  - assert (Hsource_stock : 0 <= stock + amount <= max_stock) by lia.
    pose proof (StockDaysDone_lookup_portfolio__buy_semantics
      ask bid buy sell table max_stock wait day source (stock + amount)
      Hdone ltac:(lia) Hsource_stock) as Hprevious.
    pose proof (StockPortfolioValue_finite__buy_semantics
      ask bid buy sell max_stock wait source (stock + amount)
      (Znth (stock + amount) (Znth source table []) 0)
      Hprevious Hfinite) as Hfeasible.
    unfold StockFeasiblePortfolio in Hfeasible.
    destruct Hfeasible as [[Hzero _] |
      [last_day [[Hlastlo Hlasthi] Hhistory]]].
    + lia.
    + right. unfold StockFeasiblePortfolio. right. exists day.
      split; [lia|]. rewrite Hvalue.
      replace stock with (stock + amount - amount) by lia.
      replace (stock + amount - amount + amount) with (stock + amount) by lia.
      eapply StockTradingHistory_sell with
        (previous_day := last_day) (previous_stock := stock + amount)
        (previous_profit := Znth (stock + amount) (Znth source table []) 0)
        (amount := amount); eauto; lia.
Qed.

Lemma StockSellCellValue_dominates_old__buy_semantics :
  forall ask bid buy sell table max_stock wait day source stock value profit,
    1 <= day ->
    0 <= stock <= max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait day ->
    StockSellCellValue bid sell table max_stock day source stock value ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait (day - 1)
      stock profit ->
    profit <= value.
Proof.
  intros ask bid buy sell table max_stock wait day source stock value profit
    Hday Hstock Hdone Hcell Hfeasible.
  pose proof (StockDaysDone_lookup_portfolio__buy_semantics
    ask bid buy sell table max_stock wait day (day - 1) stock
    Hdone ltac:(lia) Hstock) as Hprevious.
  pose proof (StockPortfolioValue_dominates__buy_semantics
    ask bid buy sell max_stock wait (day - 1) stock
    (Znth stock (Znth (day - 1) table []) 0) profit
    Hprevious Hfeasible) as Hdominates.
  unfold StockSellCellValue in Hcell.
  destruct Hcell as [_ Hmax].
  assert (Hcandidate : StockSellCandidate bid sell table max_stock day source
    stock 0 (Znth stock (Znth (day - 1) table []) 0)).
  { unfold StockSellCandidate. left. auto. }
  specialize (Hmax 0 (Znth stock (Znth (day - 1) table []) 0) Hcandidate).
  lia.
Qed.

Lemma StockSellCellValue_dominates_sell__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value
         previous_day previous_stock previous_profit amount profit,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    day <= days ->
    source = day - wait - 1 ->
    0 < source < day ->
    0 <= stock <= max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait day ->
    StockSellCellValue bid sell table max_stock day source stock value ->
    StockTradingHistory ask bid buy sell max_stock wait
      previous_day previous_stock previous_profit ->
    previous_day + wait < day ->
    1 <= amount <= Znth (day - 1) sell 0 ->
    amount <= previous_stock ->
    stock = previous_stock - amount ->
    profit = previous_profit + amount * Znth (day - 1) bid 0 ->
    profit <= value.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value
    previous_day previous_stock previous_profit amount profit Hinputs Hwait
    Hday Hsource Hsource_day Hstock Hdone Hcell Hhistory Hgap Hamount Hamountstock
    Hstockeq Hprofiteq.
  assert (Hprevious_stock : 0 <= previous_stock <= max_stock).
  { eapply StockTradingHistory_stock_bounded__buy_semantics; eauto. }
  assert (Hprevious_feasible :
    StockFeasiblePortfolio ask bid buy sell max_stock wait source
      previous_stock previous_profit).
  { unfold StockFeasiblePortfolio. right. exists previous_day.
    pose proof (stock_trading_history_day_positive__init_copy
      ask bid buy sell max_stock wait previous_day previous_stock
      previous_profit Hwait Hhistory).
    split; [lia|exact Hhistory]. }
  pose proof (StockDaysDone_lookup_portfolio__buy_semantics
    ask bid buy sell table max_stock wait day source previous_stock
    Hdone ltac:(lia) Hprevious_stock) as Hsource_value.
  pose proof (StockPortfolioValue_dominates__buy_semantics
    ask bid buy sell max_stock wait source previous_stock
    (Znth previous_stock (Znth source table []) 0) previous_profit
    Hsource_value Hprevious_feasible) as Hdominates.
  assert (Hfinite :
    Znth previous_stock (Znth source table []) 0 <> STOCK_NEG_INF).
  { intro Heq. unfold StockPortfolioValue in Hsource_value.
    destruct Hsource_value as [_ [[_ Hnone] | [Hfeasible _]]].
    - apply Hnone. exists previous_profit. exact Hprevious_feasible.
    - pose proof (StockFeasiblePortfolio_profit_range__buy_semantics
        ask bid buy sell days max_stock wait source previous_stock
        (Znth previous_stock (Znth source table []) 0)
        Hinputs Hwait ltac:(lia) Hfeasible) as Hrange.
      unfold STOCK_NEG_INF in *. lia. }
  unfold StockSellCellValue in Hcell.
  destruct Hcell as [_ Hmax].
  assert (Hcandidate : StockSellCandidate bid sell table max_stock day source
    stock amount
    (Znth previous_stock (Znth source table []) 0 +
      amount * Znth (day - 1) bid 0)).
  { unfold StockSellCandidate. right.
    replace (stock + amount) with previous_stock by lia.
    repeat split; try assumption; lia. }
  specialize (Hmax amount
    (Znth previous_stock (Znth source table []) 0 +
      amount * Znth (day - 1) bid 0) Hcandidate).
  lia.
Qed.

Lemma StockPortfolioValue_finite_if_feasible__buy_semantics :
  forall ask bid buy sell days max_stock wait horizon stock value profit,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    horizon <= days ->
    StockPortfolioValue ask bid buy sell max_stock wait horizon stock value ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait horizon stock profit ->
    value <> STOCK_NEG_INF.
Proof.
  intros ask bid buy sell days max_stock wait horizon stock value profit
    Hinputs Hwait Hhorizon Hvalue Hfeasible Heq.
  unfold StockPortfolioValue in Hvalue.
  destruct Hvalue as [_ [[_ Hnone] | [Hself _]]].
  - apply Hnone. exists profit. exact Hfeasible.
  - pose proof (StockFeasiblePortfolio_profit_range__buy_semantics
      ask bid buy sell days max_stock wait horizon stock value
      Hinputs Hwait Hhorizon Hself) as Hrange.
    unfold STOCK_NEG_INF in *. lia.
Qed.

Lemma StockBuyCellValue_sound__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    1 <= day ->
    day <= days ->
    source = day - wait - 1 ->
    0 < source < day ->
    0 <= stock <= max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait day ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value ->
    value = STOCK_NEG_INF \/
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock value.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hwait Hdaypos Hday Hsource Hsource_day Hstock Hdone Hcell.
  unfold StockBuyCellValue in Hcell.
  destruct Hcell as [[[amount Hcandidate] _] _].
  unfold StockBuyCandidate in Hcandidate.
  destruct Hcandidate as [[-> Hsell] |
    [Hamount [Hamountstock [Hfinite Hvalue]]]].
  - eapply StockSellCellValue_sound__buy_semantics; eauto.
  - assert (Hsource_stock : 0 <= stock - amount <= max_stock) by lia.
    pose proof (StockDaysDone_lookup_portfolio__buy_semantics
      ask bid buy sell table max_stock wait day source (stock - amount)
      Hdone ltac:(lia) Hsource_stock) as Hprevious.
    pose proof (StockPortfolioValue_finite__buy_semantics
      ask bid buy sell max_stock wait source (stock - amount)
      (Znth (stock - amount) (Znth source table []) 0)
      Hprevious Hfinite) as Hfeasible.
    unfold StockFeasiblePortfolio in Hfeasible.
    destruct Hfeasible as [[Hzero Hprofit] |
      [last_day [[Hlastlo Hlasthi] Hhistory]]].
    + right. unfold StockFeasiblePortfolio. right. exists day.
      split; [lia|]. rewrite Hvalue, Hprofit.
      replace stock with amount by lia.
      replace (0 - amount * Znth (day - 1) ask 0) with
        (- amount * Znth (day - 1) ask 0) by lia.
      eapply StockTradingHistory_first_buy; eauto; lia.
    + right. unfold StockFeasiblePortfolio. right. exists day.
      split; [lia|]. rewrite Hvalue.
      replace stock with (stock - amount + amount) by lia.
      replace (stock - amount + amount - amount) with (stock - amount) by lia.
      eapply StockTradingHistory_buy with
        (previous_day := last_day) (previous_stock := stock - amount)
        (previous_profit := Znth (stock - amount) (Znth source table []) 0)
        (amount := amount); eauto; lia.
Qed.

Lemma StockBuyCellValue_dominates_feasible__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value profit,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    1 <= day ->
    day <= days ->
    source = day - wait - 1 ->
    0 < source < day ->
    0 <= stock <= max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait day ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value ->
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit ->
    profit <= value.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value profit
    Hinputs Hwait Hdaypos Hday Hsource Hsource_day Hstock Hdone Hcell Hfeasible.
  unfold StockBuyCellValue in Hcell.
  destruct Hcell as [[Hachieve Hmax] [zero_value Hsell]].
  assert (Hold : forall p,
    StockFeasiblePortfolio ask bid buy sell max_stock wait (day - 1) stock p ->
    p <= value).
  { intros p Hp.
    pose proof (StockSellCellValue_dominates_old__buy_semantics
      ask bid buy sell table max_stock wait day source stock zero_value p
      Hdaypos Hstock Hdone Hsell Hp) as Hzero.
    assert (Hcandidate : StockBuyCandidate ask bid buy sell table max_stock
      day source stock 0 zero_value).
    { unfold StockBuyCandidate. left. auto. }
    specialize (Hmax 0 zero_value Hcandidate). lia. }
  unfold StockFeasiblePortfolio in Hfeasible.
  destruct Hfeasible as [Hzero | [last_day [[Hlastlo Hlasthi] Hhistory]]].
  - apply Hold. unfold StockFeasiblePortfolio. left. exact Hzero.
  - destruct (Z_lt_ge_dec last_day day) as [Hearly | Hterminal].
    + apply Hold. unfold StockFeasiblePortfolio. right. exists last_day.
      split; [lia|exact Hhistory].
    + assert (Hlast : last_day = day) by lia. subst last_day.
      inversion Hhistory; subst stock profit; clear Hhistory.
      * assert (Hsource_zero :
          StockFeasiblePortfolio ask bid buy sell max_stock wait source 0 0).
        { unfold StockFeasiblePortfolio. left. auto. }
        pose proof (StockDaysDone_lookup_portfolio__buy_semantics
          ask bid buy sell table max_stock wait day source 0
          Hdone ltac:(lia) ltac:(lia)) as Hsource_value.
        pose proof (StockPortfolioValue_dominates__buy_semantics
          ask bid buy sell max_stock wait source 0
          (Znth 0 (Znth source table []) 0) 0
          Hsource_value Hsource_zero) as Hdom.
        pose proof (StockPortfolioValue_finite_if_feasible__buy_semantics
          ask bid buy sell days max_stock wait source 0
          (Znth 0 (Znth source table []) 0) 0
          Hinputs Hwait ltac:(lia) Hsource_value Hsource_zero) as Hfinite.
        assert (Hcandidate : StockBuyCandidate ask bid buy sell table max_stock
          day source amount amount
          (Znth 0 (Znth source table []) 0 -
            amount * Znth (day - 1) ask 0)).
        { unfold StockBuyCandidate. right.
          replace (amount - amount) with 0 by lia.
          repeat split; try assumption; lia. }
        specialize (Hmax amount
          (Znth 0 (Znth source table []) 0 -
            amount * Znth (day - 1) ask 0) Hcandidate). lia.
      * assert (Hprevious_stock : 0 <= previous_stock <= max_stock).
        { eapply StockTradingHistory_stock_bounded__buy_semantics; eauto. }
        assert (Hprevious_feasible :
          StockFeasiblePortfolio ask bid buy sell max_stock wait source
            previous_stock previous_profit).
        { unfold StockFeasiblePortfolio. right. exists previous_day.
          pose proof (stock_trading_history_day_positive__init_copy
            ask bid buy sell max_stock wait previous_day previous_stock
            previous_profit Hwait H).
          split; [lia|exact H]. }
        pose proof (StockDaysDone_lookup_portfolio__buy_semantics
          ask bid buy sell table max_stock wait day source previous_stock
          Hdone ltac:(lia) Hprevious_stock) as Hsource_value.
        pose proof (StockPortfolioValue_dominates__buy_semantics
          ask bid buy sell max_stock wait source previous_stock
          (Znth previous_stock (Znth source table []) 0) previous_profit
          Hsource_value Hprevious_feasible) as Hdom.
        pose proof (StockPortfolioValue_finite_if_feasible__buy_semantics
          ask bid buy sell days max_stock wait source previous_stock
          (Znth previous_stock (Znth source table []) 0) previous_profit
          Hinputs Hwait ltac:(lia) Hsource_value Hprevious_feasible) as Hfinite.
        assert (Hcandidate : StockBuyCandidate ask bid buy sell table max_stock
          day source (previous_stock + amount) amount
          (Znth previous_stock (Znth source table []) 0 -
            amount * Znth (day - 1) ask 0)).
        { unfold StockBuyCandidate. right.
          replace (previous_stock + amount - amount) with previous_stock by lia.
          repeat split; try assumption; lia. }
        specialize (Hmax amount
          (Znth previous_stock (Znth source table []) 0 -
            amount * Znth (day - 1) ask 0) Hcandidate). lia.
      * pose proof (StockSellCellValue_dominates_sell__buy_semantics
          ask bid buy sell table days max_stock wait day source
          (previous_stock - amount) zero_value previous_day previous_stock
          previous_profit amount
          (previous_profit + amount * Znth (day - 1) bid 0)
          Hinputs Hwait Hday Hsource Hsource_day Hstock
          Hdone Hsell H H0 H1 H2 eq_refl eq_refl) as Hzero.
        assert (Hcandidate : StockBuyCandidate ask bid buy sell table max_stock
          day source (previous_stock - amount) 0 zero_value).
        { unfold StockBuyCandidate. left. auto. }
        specialize (Hmax 0 zero_value Hcandidate). lia.
Qed.

Lemma StockBuyCellValue_to_StockPortfolioValue__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    1 <= day ->
    day <= days ->
    source = day - wait - 1 ->
    0 < source < day ->
    0 <= stock <= max_stock ->
    StockDaysDone ask bid buy sell table max_stock wait day ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value ->
    StockPortfolioValue ask bid buy sell max_stock wait day stock value.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hwait Hdaypos Hday Hsource Hsource_day Hstock Hdone Hcell.
  split; [exact Hstock|].
  pose proof (StockBuyCellValue_sound__buy_semantics
    ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hwait Hdaypos Hday Hsource Hsource_day Hstock Hdone Hcell) as Hsound.
  destruct Hsound as [Hneg | Hfeasible].
  - left. split; [exact Hneg|].
    intros [profit Hfeasible].
    pose proof (StockBuyCellValue_dominates_feasible__buy_semantics
      ask bid buy sell table days max_stock wait day source stock value profit
      Hinputs Hwait Hdaypos Hday Hsource Hsource_day Hstock Hdone Hcell
      Hfeasible) as Hdom.
    pose proof (StockFeasiblePortfolio_profit_range__buy_semantics
      ask bid buy sell days max_stock wait day stock profit
      Hinputs Hwait Hday Hfeasible) as Hrange.
    unfold STOCK_NEG_INF in *. lia.
  - right. split; [exact Hfeasible|].
    intros profit Hprofit.
    eapply StockBuyCellValue_dominates_feasible__buy_semantics; eauto.
Qed.

Lemma StockBuyProgress_complete_day__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source next_stock,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    day <= days ->
    max_stock < next_stock ->
    StockBuyProgress ask bid buy sell table max_stock wait day source next_stock ->
    StockDaysDone ask bid buy sell table max_stock wait (day + 1).
Proof.
  intros ask bid buy sell table days max_stock wait day source next_stock
    Hinputs Hwait Hday Hcomplete Hprogress.
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hdayrange [Hsource [Hsourcerange
    [Hnextrange [Hbuy Hsell]]]]]].
  pose proof Hdone as Hdone0.
  unfold StockDaysDone in Hdone |-.
  destruct Hdone as [Hshape [Hbounded [Hnext Hportfolio]]].
  split; [exact Hshape|].
  split; [exact Hbounded|].
  split; [lia|].
  intros d stock Hd Hstock.
  destruct (Z_lt_ge_dec d day) as [Hearly | Hcurrent].
  - apply Hportfolio; lia.
  - assert (Hd_eq : d = day) by lia. subst d.
    exact (StockBuyCellValue_to_StockPortfolioValue__buy_semantics
      ask bid buy sell table days max_stock wait day source stock
      (Znth stock (Znth day table []) 0)
      Hinputs Hwait ltac:(lia) Hday Hsource Hsourcerange Hstock Hdone0
      (Hbuy stock ltac:(lia))).
Qed.

Lemma StockSellCellValue_replace_current_row__buy_semantics :
  forall bid sell table max_stock day source stock value col replacement days,
    StockTableShape table days max_stock ->
    0 <= day < days + 1 ->
    0 <= source < days + 1 ->
    0 <= day - 1 < days + 1 ->
    0 <= col < max_stock + 1 ->
    source <> day ->
    day - 1 <> day ->
    StockSellCellValue bid sell table max_stock day source stock value ->
    let row' := replace_Znth col replacement (Znth day table []) in
    let table' := replace_Znth day row' table in
    StockSellCellValue bid sell table' max_stock day source stock value.
Proof.
  intros bid sell table max_stock day source stock value col replacement days
    Hshape Hday Hsourceidx Hprevidx Hcol Hsource Hprev Hcell row' table'.
  unfold StockTableShape in Hshape.
  destruct Hshape as [Htablelen Hrowlen].
  assert (Hsource_eq : Znth source table' [] = Znth source table []).
  { unfold table'. rewrite Znth_replace_Znth_Diff by
      (try rewrite Htablelen; lia). reflexivity. }
  assert (Hprev_eq : Znth (day - 1) table' [] = Znth (day - 1) table []).
  { unfold table'. rewrite Znth_replace_Znth_Diff by
      (try rewrite Htablelen; lia). reflexivity. }
  unfold StockSellCellValue, StockSellCandidate in *.
  rewrite Hsource_eq, Hprev_eq. exact Hcell.
Qed.

Lemma StockBuyCellValue_replace_current_row__buy_semantics :
  forall ask bid buy sell table max_stock day source stock value col replacement days,
    StockTableShape table days max_stock ->
    0 <= day < days + 1 ->
    0 <= source < days + 1 ->
    0 <= day - 1 < days + 1 ->
    0 <= col < max_stock + 1 ->
    source <> day ->
    day - 1 <> day ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value ->
    let row' := replace_Znth col replacement (Znth day table []) in
    let table' := replace_Znth day row' table in
    StockBuyCellValue ask bid buy sell table' max_stock day source stock value.
Proof.
  intros ask bid buy sell table max_stock day source stock value col replacement
    days Hshape Hday Hsourceidx Hprevidx Hcol Hsource Hprev Hcell row' table'.
  unfold StockTableShape in Hshape.
  destruct Hshape as [Htablelen Hrowlen].
  assert (Hsource_eq : Znth source table' [] = Znth source table []).
  { unfold table'. rewrite Znth_replace_Znth_Diff by
      (try rewrite Htablelen; lia). reflexivity. }
  assert (Hprev_eq : Znth (day - 1) table' [] = Znth (day - 1) table []).
  { unfold table'. rewrite Znth_replace_Znth_Diff by
      (try rewrite Htablelen; lia). reflexivity. }
  unfold StockBuyCellValue, StockBuyCandidate, StockSellCellValue,
    StockSellCandidate in *.
  rewrite Hsource_eq, Hprev_eq. exact Hcell.
Qed.

Lemma StockBuyProgress_replace_step__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock ->
    StockTableShape table days max_stock ->
    StockBuyProgress ask bid buy sell table max_stock wait day source stock ->
    stock <= max_stock ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value ->
    STOCK_NEG_INF <= value <= STOCK_MAX_PROFIT ->
    let row' := replace_Znth stock value (Znth day table []) in
    let table' := replace_Znth day row' table in
    StockBuyProgress ask bid buy sell table' max_stock wait day source (stock + 1) /\
    StockTableShape table' days max_stock.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hshape Hprogress Hstockmax Hcell Hvalue row' table'.
  unfold StockInputsBounded in Hinputs.
  destruct Hinputs as [Hasklen [Hbidlen [Hbuylen [Hselllen [Hdays [Hmax Hdayinput]]]]]].
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hdayrange [Hsource [Hsourcerange
    [Hstockrange [Hbuy Hsell]]]]]].
  pose proof Hshape as Hshape_base.
  unfold StockTableShape in Hshape.
  destruct Hshape as [Htablelen Hrowlen].
  assert (Hdayidx : 0 <= day < days + 1) by (rewrite <- Hasklen; lia).
  assert (Hstockidx : 0 <= stock < max_stock + 1) by lia.
  assert (Hrowlength : Zlength (Znth day table []) = max_stock + 1).
  { apply Hrowlen. exact Hdayidx. }
  assert (Hrow'length : Zlength row' = max_stock + 1).
  { unfold row'. rewrite Zlength_replace_Znth. exact Hrowlength. }
  assert (Hshape' : StockTableShape table' days max_stock).
  { unfold StockTableShape. split.
    - unfold table'. rewrite Zlength_replace_Znth. exact Htablelen.
    - intros r Hr. unfold table'. destruct (Z.eq_dec r day) as [-> | Hneq].
      + rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
        exact Hrow'length.
      + rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
        apply Hrowlen. exact Hr. }
  assert (Hdone' : StockDaysDone ask bid buy sell table' max_stock wait day).
  { unfold StockDaysDone in Hdone |-.
    destruct Hdone as [Hshape0 [Hbounded [Hnext Hportfolio]]].
    split.
    - rewrite Hasklen. exact Hshape'.
    - split.
      + unfold StockTableValuesBounded in *.
        intros r k Hr Hk. unfold table'.
        destruct (Z.eq_dec r day) as [-> | Hrday].
        * rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
          unfold row'. destruct (Z.eq_dec k stock) as [-> | Hneq].
          -- rewrite Znth_replace_Znth_Same by (rewrite Hrowlength; exact Hstockidx).
             exact Hvalue.
          -- rewrite Znth_replace_Znth_Diff by (try rewrite Hrowlength; lia).
             apply Hbounded; [rewrite Hasklen; exact Hdayidx | exact Hk].
        * rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
          apply Hbounded; [exact Hr | exact Hk].
      + split; [exact Hnext|].
        intros r k Hr Hk. unfold table'.
        rewrite Znth_replace_Znth_Diff by (try rewrite Htablelen; lia).
        apply Hportfolio; assumption. }
  split; [|exact Hshape'].
  unfold StockBuyProgress.
  split; [exact Hdone'|].
  split; [exact Hdayrange|].
  split; [exact Hsource|].
  split; [exact Hsourcerange|].
  split; [lia|]. split.
  - intros k Hk. destruct (Z_lt_ge_dec k stock) as [Hlt | Hge].
    + unfold table', row'.
      rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
      rewrite Znth_replace_Znth_Diff by (try rewrite Hrowlength; lia).
      exact (StockBuyCellValue_replace_current_row__buy_semantics
        ask bid buy sell table max_stock day source k
        (Znth k (Znth day table []) 0) stock value days
        Hshape_base Hdayidx ltac:(lia) ltac:(lia) Hstockidx
        ltac:(lia) ltac:(lia) (Hbuy k ltac:(lia))).
    + assert (Hkeq : k = stock) by lia. subst k.
      unfold table', row'.
      rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
      rewrite Znth_replace_Znth_Same by (rewrite Hrowlength; exact Hstockidx).
      exact (StockBuyCellValue_replace_current_row__buy_semantics
        ask bid buy sell table max_stock day source stock value stock value days
        Hshape_base Hdayidx ltac:(lia) ltac:(lia) Hstockidx
        ltac:(lia) ltac:(lia) Hcell).
  - intros k Hk.
    unfold table', row'.
    rewrite Znth_replace_Znth_Same by (rewrite Htablelen; exact Hdayidx).
    rewrite Znth_replace_Znth_Diff by (try rewrite Hrowlength; lia).
    exact (StockSellCellValue_replace_current_row__buy_semantics
      bid sell table max_stock day source k
      (Znth k (Znth day table []) 0) stock value days
      Hshape_base Hdayidx ltac:(lia) ltac:(lia) Hstockidx
      ltac:(lia) ltac:(lia) (Hsell k ltac:(lia))).
Qed.

Lemma StockBuyProgress_replace_improved_step__buy_semantics :
  forall ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock ->
    0 <= wait ->
    StockTableShape table days max_stock ->
    StockBuyProgress ask bid buy sell table max_stock wait day source stock ->
    stock <= max_stock ->
    Znth stock (Znth day table []) 0 < value ->
    StockBuyCellValue ask bid buy sell table max_stock day source stock value ->
    let row' := replace_Znth stock value (Znth day table []) in
    let table' := replace_Znth day row' table in
    StockBuyProgress ask bid buy sell table' max_stock wait day source (stock + 1) /\
    StockTableShape table' days max_stock.
Proof.
  intros ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hwait Hshape Hprogress Hstockmax Himprove Hcell.
  pose proof Hprogress as Hprogress0.
  unfold StockBuyProgress in Hprogress.
  destruct Hprogress as [Hdone [Hdayrange [Hsource [Hsourcerange
    [Hstockrange [Hbuy Hsell]]]]]].
  assert (Hdaydays : day <= days).
  { pose proof Hinputs as Hinputs0. unfold StockInputsBounded in Hinputs0. lia. }
  pose proof (StockDaysDone_cell_bounded__safety_buy
    ask bid buy sell table days max_stock wait day day stock []
    Hinputs Hdone Hshape ltac:(lia)
    ltac:(lia)) as Holdrange.
  assert (Hvaluerange : STOCK_NEG_INF <= value <= STOCK_MAX_PROFIT).
  { pose proof (StockBuyCellValue_sound__buy_semantics
      ask bid buy sell table days max_stock wait day source stock value
      Hinputs Hwait ltac:(lia) Hdaydays
      Hsource Hsourcerange ltac:(lia) Hdone Hcell) as Hsound.
    destruct Hsound as [Hneg | Hfeasible].
    - lia.
    - pose proof (StockFeasiblePortfolio_profit_range__buy_semantics
        ask bid buy sell days max_stock wait day stock value
        Hinputs Hwait Hdaydays Hfeasible) as Hrange.
      lia. }
  exact (StockBuyProgress_replace_step__buy_semantics
    ask bid buy sell table days max_stock wait day source stock value
    Hinputs Hshape Hprogress0 Hstockmax Hcell Hvaluerange).
Qed.
