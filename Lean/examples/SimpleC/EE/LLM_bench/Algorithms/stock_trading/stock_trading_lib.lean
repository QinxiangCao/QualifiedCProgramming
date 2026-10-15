import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
open AUXLib

-- Type spelling emitted for an arbitrary nested-list lookup default.
abbrev _List_Z := List Int

def STOCK_NEG_INF : Int := -1000000000

def STOCK_MAX_PROFIT : Int := 1000000000

def StockInitialCell (day stock : Int) : Int :=
  if day = 0 then
    if stock = 0 then 0 else STOCK_NEG_INF
  else STOCK_NEG_INF

def StockTableShape
    (table : List (List Int)) (days max_stock : Int) : Prop :=
  Zlength table = days + 1 ∧
  ∀ row,( 0 ≤ row ∧ row < days + 1) →
    Zlength (Znth row table []) = max_stock + 1

def StockTableValuesBounded
    (table : List (List Int)) (days max_stock : Int) : Prop :=
  ∀ row stock,
    (0 ≤ row ∧ row < days + 1) →
    (0 ≤ stock ∧ stock < max_stock + 1) →
    (STOCK_NEG_INF ≤ Znth stock (Znth row table []) 0 ∧ Znth stock (Znth row table []) 0 ≤ STOCK_MAX_PROFIT) 

def StockInputsBounded
    (ask bid buy sell : List Int) (days max_stock : Int) : Prop :=
  Zlength ask = days ∧
  Zlength bid = days ∧
  Zlength buy = days ∧
  Zlength sell = days ∧
  (1 ≤ days ∧ days ≤ 990) ∧
  (1 ≤ max_stock ∧ max_stock ≤ 990) ∧
  (∀ day,( 1 ≤ day ∧ day ≤ days) →
     (1 ≤ Znth (day - 1) bid 0 ∧ Znth (day - 1) bid 0 ≤ Znth (day - 1) ask 0) ∧
     Znth (day - 1) ask 0 ≤ 1000 ∧
     (1 ≤ Znth (day - 1) buy 0 ∧ Znth (day - 1) buy 0 ≤ max_stock) ∧
     (1 ≤ Znth (day - 1) sell 0 ∧ Znth (day - 1) sell 0 ≤ max_stock)) 

inductive StockTradingHistory
    (ask bid buy sell : List Int) (max_stock wait : Int)
    : Int → Int → Int → Prop where
  | StockTradingHistory_first_buy :
      ∀ day amount,
        1 ≤ day →
        (1 ≤ amount ∧ amount ≤ Znth (day - 1) buy 0) →
        amount ≤ max_stock →
        StockTradingHistory ask bid buy sell max_stock wait
          day amount (- amount * Znth (day - 1) ask 0)
  | StockTradingHistory_buy :
      ∀ previous_day previous_stock previous_profit day amount,
        StockTradingHistory ask bid buy sell max_stock wait
          previous_day previous_stock previous_profit →
        previous_day + wait < day →
        (1 ≤ amount ∧ amount ≤ Znth (day - 1) buy 0) →
        previous_stock + amount ≤ max_stock →
        StockTradingHistory ask bid buy sell max_stock wait
          day (previous_stock + amount)
          (previous_profit - amount * Znth (day - 1) ask 0)
  | StockTradingHistory_sell :
      ∀ previous_day previous_stock previous_profit day amount,
        StockTradingHistory ask bid buy sell max_stock wait
          previous_day previous_stock previous_profit →
        previous_day + wait < day →
        (1 ≤ amount ∧ amount ≤ Znth (day - 1) sell 0) →
        amount ≤ previous_stock →
        StockTradingHistory ask bid buy sell max_stock wait
          day (previous_stock - amount)
          (previous_profit + amount * Znth (day - 1) bid 0)

def StockFeasiblePortfolio
    (ask bid buy sell : List Int) (max_stock wait horizon stock profit : Int) : Prop :=
  (stock = 0 ∧ profit = 0) ∨
  ∃ last_day,
    (1 ≤ last_day ∧ last_day ≤ horizon) ∧
    StockTradingHistory ask bid buy sell max_stock wait
      last_day stock profit

def StockPortfolioValue
    (ask bid buy sell : List Int)
    (max_stock wait horizon stock value : Int) : Prop :=
  (0 ≤ stock ∧ stock ≤ max_stock) ∧
  ((value = STOCK_NEG_INF ∧
    ¬ ∃ profit,
        StockFeasiblePortfolio
          ask bid buy sell max_stock wait horizon stock profit) ∨
   (StockFeasiblePortfolio
      ask bid buy sell max_stock wait horizon stock value ∧
    ∀ profit,
      StockFeasiblePortfolio
        ask bid buy sell max_stock wait horizon stock profit →
      profit ≤ value))

def StockMaximumProfit
    (ask bid buy sell : List Int)
    (days max_stock wait answer : Int) : Prop :=
  ∃ stock,
    (0 ≤ stock ∧ stock ≤ max_stock) ∧
    StockFeasiblePortfolio
      ask bid buy sell max_stock wait days stock answer ∧
    ∀ stock' profit,
      (0 ≤ stock' ∧ stock' ≤ max_stock) →
      StockFeasiblePortfolio
        ask bid buy sell max_stock wait days stock' profit →
      profit ≤ answer

def StockFillRows
    (table : List (List Int)) (days max_stock row : Int) : Prop :=
  (0 ≤ row ∧ row ≤ days + 1) ∧
  StockTableShape table days max_stock ∧
  ∀ d stock,
    (0 ≤ d ∧ d < row) →
    (0 ≤ stock ∧ stock < max_stock + 1) →
    Zlength (Znth d table []) = max_stock + 1 ∧
    Znth stock (Znth d table []) 0 = StockInitialCell d stock

def StockFillCells
    (current_row : List Int) (max_stock row col : Int) : Prop :=
  (0 ≤ col ∧ col ≤ max_stock + 1) ∧
  Zlength current_row = max_stock + 1 ∧
  ∀ stock,
    (0 ≤ stock ∧ stock < col) →
    Znth stock current_row 0 = StockInitialCell row stock

def StockDaysDone
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait next_day : Int) : Prop :=
  StockTableShape table (Zlength ask) max_stock ∧
  StockTableValuesBounded table (Zlength ask) max_stock ∧
  0 ≤ next_day ∧
  ∀ day stock,
    (0 ≤ day ∧ day < next_day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (Znth stock (Znth day table []) 0)

def StockCopyProgress
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait day col : Int) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day ∧
  1 ≤ day ∧
  (0 ≤ col ∧ col ≤ max_stock + 1) ∧
  ∀ stock,
    (0 ≤ stock ∧ stock < col) →
    Znth stock (Znth day table []) 0 =
    Znth stock (Znth (day - 1) table []) 0

def StockEarlyBuyProgress
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait day next_stock : Int) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day ∧
  1 ≤ day ∧
  (1 ≤ next_stock ∧ next_stock ≤ Znth (day - 1) buy 0 + 1) ∧
  Znth 0 (Znth day table []) 0 =
    Znth 0 (Znth (day - 1) table []) 0 ∧
  ∀ stock,
    (1 ≤ stock ∧ stock ≤ max_stock) →
    if stock < next_stock then
      Znth stock (Znth day table []) 0 =
      max (Znth stock (Znth (day - 1) table []) 0)
            (- stock * Znth (day - 1) ask 0)
    else
      Znth stock (Znth day table []) 0 =
      Znth stock (Znth (day - 1) table []) 0

def StockSellScore
    (table : List (List Int)) (source price stock : Int) : Int :=
  Znth stock (Znth source table []) 0 + stock * price

def StockBuyScore
    (table : List (List Int)) (source price stock : Int) : Int :=
  Znth stock (Znth source table []) 0 + stock * price

def StockFiniteTableIndex
    (table : List (List Int)) (source stock : Int) : Prop :=
  0 ≤ stock ∧
  stock < Zlength (Znth source table []) ∧
  Znth stock (Znth source table []) 0 ≠ STOCK_NEG_INF

def StockFiniteIndexInWindow
    (table : List (List Int)) (source lower upper stock : Int) : Prop :=
  0 ≤ stock ∧
  stock < Zlength (Znth source table []) ∧
  Znth stock (Znth source table []) 0 ≠ STOCK_NEG_INF ∧
  (lower ≤ stock ∧ stock ≤ upper) 

def StockSellQueue
    (table : List (List Int)) (queue : List Int)
    (source price lower upper head tail : Int) : Prop :=
  (0 ≤ head ∧ head ≤ tail) ∧
  (∀ pos,( head ≤ pos ∧ pos < tail) →
     StockFiniteIndexInWindow table source lower upper
       (Znth pos queue 0)) ∧
  (∀ left right,( head ≤ left ∧ left < right) ∧ right < tail →
     Znth left queue 0 > Znth right queue 0 ∧
     StockSellScore table source price (Znth left queue 0) >
     StockSellScore table source price (Znth right queue 0)) ∧
  (∀ candidate,
     StockFiniteIndexInWindow table source lower upper candidate →
     ∃ pos,( head ≤ pos ∧ pos < tail) ∧
       Znth pos queue 0 ≤ candidate ∧
       StockSellScore table source price candidate ≤ StockSellScore table source price (Znth pos queue 0))

def StockSellQueueExpiring
    (table : List (List Int)) (queue : List Int)
    (source price lower current_upper head tail : Int) : Prop :=
  StockSellQueue table queue source price
    lower (current_upper + 1) head tail ∨
  StockSellQueue table queue source price
    lower current_upper head tail

def StockSellQueuePopping
    (table : List (List Int)) (queue : List Int)
    (source price incoming upper head tail : Int) : Prop :=
  StockFiniteTableIndex table source incoming ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  (∀ pos,( head ≤ pos ∧ pos < tail) →
     StockFiniteIndexInWindow table source (incoming + 1) upper
       (Znth pos queue 0)) ∧
  (∀ left right,( head ≤ left ∧ left < right) ∧ right < tail →
     Znth left queue 0 > Znth right queue 0 ∧
     StockSellScore table source price (Znth left queue 0) >
     StockSellScore table source price (Znth right queue 0)) ∧
  (∀ candidate,
     StockFiniteIndexInWindow table source incoming upper candidate →
     StockSellScore table source price candidate ≤ StockSellScore table source price incoming ∨
     ∃ pos,( head ≤ pos ∧ pos < tail) ∧
       Znth pos queue 0 ≤ candidate ∧
       StockSellScore table source price candidate ≤ StockSellScore table source price (Znth pos queue 0))

def StockSellQueuePending
    (table : List (List Int)) (queue : List Int)
    (source price incoming upper head tail : Int) : Prop :=
  StockSellQueuePopping table queue source price incoming upper head tail ∧
  tail < Zlength queue ∧
  (head < tail →
   StockSellScore table source price incoming < StockSellScore table source price (Znth (tail - 1) queue 0))

def StockBuyQueue
    (table : List (List Int)) (queue : List Int)
    (source price lower upper head tail : Int) : Prop :=
  (0 ≤ head ∧ head ≤ tail) ∧
  (∀ pos,( head ≤ pos ∧ pos < tail) →
     StockFiniteIndexInWindow table source lower upper
       (Znth pos queue 0)) ∧
  (∀ left right,( head ≤ left ∧ left < right) ∧ right < tail →
     Znth left queue 0 < Znth right queue 0 ∧
     StockBuyScore table source price (Znth left queue 0) >
     StockBuyScore table source price (Znth right queue 0)) ∧
  (∀ candidate,
     StockFiniteIndexInWindow table source lower upper candidate →
     ∃ pos,( head ≤ pos ∧ pos < tail) ∧
       candidate ≤ Znth pos queue 0 ∧
       StockBuyScore table source price candidate ≤ StockBuyScore table source price (Znth pos queue 0))

def StockBuyQueueExpiring
    (table : List (List Int)) (queue : List Int)
    (source price current_lower upper head tail : Int) : Prop :=
  StockBuyQueue table queue source price
    (current_lower - 1) upper head tail ∨
  StockBuyQueue table queue source price
    current_lower upper head tail

def StockBuyQueuePopping
    (table : List (List Int)) (queue : List Int)
    (source price lower incoming head tail : Int) : Prop :=
  StockFiniteTableIndex table source incoming ∧
  (0 ≤ head ∧ head ≤ tail) ∧
  (∀ pos,( head ≤ pos ∧ pos < tail) →
     StockFiniteIndexInWindow table source lower (incoming - 1)
       (Znth pos queue 0)) ∧
  (∀ left right,( head ≤ left ∧ left < right) ∧ right < tail →
     Znth left queue 0 < Znth right queue 0 ∧
     StockBuyScore table source price (Znth left queue 0) >
     StockBuyScore table source price (Znth right queue 0)) ∧
  (∀ candidate,
     StockFiniteIndexInWindow table source lower incoming candidate →
     StockBuyScore table source price candidate ≤ StockBuyScore table source price incoming ∨
     ∃ pos,( head ≤ pos ∧ pos < tail) ∧
       candidate ≤ Znth pos queue 0 ∧
       StockBuyScore table source price candidate ≤ StockBuyScore table source price (Znth pos queue 0))

def StockBuyQueuePending
    (table : List (List Int)) (queue : List Int)
    (source price lower incoming head tail : Int) : Prop :=
  StockBuyQueuePopping table queue source price lower incoming head tail ∧
  tail < Zlength queue ∧
  (head < tail →
   StockBuyScore table source price incoming < StockBuyScore table source price (Znth (tail - 1) queue 0))

def StockSellCandidate
    (bid sell : List Int) (table : List (List Int))
    (max_stock day source stock amount value : Int) : Prop :=
  (amount = 0 ∧
   value = Znth stock (Znth (day - 1) table []) 0) ∨
  ((1 ≤ amount ∧ amount ≤ Znth (day - 1) sell 0) ∧
   stock + amount ≤ max_stock ∧
   Znth (stock + amount) (Znth source table []) 0 ≠ STOCK_NEG_INF ∧
   value =
     Znth (stock + amount) (Znth source table []) 0 +
     amount * Znth (day - 1) bid 0)

def StockSellCellValue
    (bid sell : List Int) (table : List (List Int))
    (max_stock day source stock value : Int) : Prop :=
  (∃ amount,
     StockSellCandidate
       bid sell table max_stock day source stock amount value) ∧
  (∀ amount candidate,
     StockSellCandidate
       bid sell table max_stock day source stock amount candidate →
     candidate ≤ value)

def StockBuyCandidate
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock day source stock amount value : Int) : Prop :=
  (amount = 0 ∧
   StockSellCellValue bid sell table max_stock day source stock value) ∨
  ((1 ≤ amount ∧ amount ≤ Znth (day - 1) buy 0) ∧
   amount ≤ stock ∧
   Znth (stock - amount) (Znth source table []) 0 ≠ STOCK_NEG_INF ∧
   value =
     Znth (stock - amount) (Znth source table []) 0 -
     amount * Znth (day - 1) ask 0)

def StockBuyCellValue
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock day source stock value : Int) : Prop :=
  ((∃ amount,
      StockBuyCandidate
        ask bid buy sell table max_stock day source stock amount value) ∧
   (∀ amount candidate,
      StockBuyCandidate
        ask bid buy sell table max_stock day source stock amount candidate →
      candidate ≤ value)) ∧
  ∃ zero_value,
    StockSellCellValue
      bid sell table max_stock day source stock zero_value

def StockSellProgress
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait day source next_stock : Int) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day ∧
  (1 ≤ day ∧ day ≤ Zlength ask) ∧
  source = day - wait - 1 ∧
  (0 < source ∧ source < day) ∧
  (-1 ≤ next_stock ∧ next_stock < max_stock) ∧
  (∀ stock,
     (0 ≤ stock ∧ stock ≤ next_stock) →
     Znth stock (Znth day table []) 0 =
       Znth stock (Znth (day - 1) table []) 0) ∧
  (∀ stock,
     (next_stock < stock ∧ stock < max_stock) →
     StockSellCellValue bid sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)) ∧
  Znth max_stock (Znth day table []) 0 =
    Znth max_stock (Znth (day - 1) table []) 0

def StockBuyProgress
    (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait day source next_stock : Int) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait day ∧
  (1 ≤ day ∧ day ≤ Zlength ask) ∧
  source = day - wait - 1 ∧
  (0 < source ∧ source < day) ∧
  (1 ≤ next_stock ∧ next_stock ≤ max_stock + 1) ∧
  (∀ stock,
     (0 ≤ stock ∧ stock < next_stock) →
     StockBuyCellValue ask bid buy sell table max_stock day source stock
       (Znth stock (Znth day table []) 0)) ∧
  (∀ stock,
     (next_stock ≤ stock ∧ stock ≤ max_stock) →
     StockSellCellValue bid sell table max_stock day source stock
       (Znth stock (Znth day table []) 0))

def StockAnswerProgress
    (ask bid buy sell : List Int) (table : List (List Int))
    (days max_stock wait next_stock answer : Int) : Prop :=
  StockDaysDone ask bid buy sell table max_stock wait (days + 1) ∧
  (0 ≤ next_stock ∧ next_stock ≤ max_stock + 1) ∧
  0 ≤ answer ∧
  ((next_stock = 0 ∧ answer = 0) ∨
   (0 < next_stock ∧
    (∃ stock,
       (0 ≤ stock ∧ stock < next_stock) ∧
       StockFeasiblePortfolio
         ask bid buy sell max_stock wait days stock answer) ∧
    (∀ stock profit,
       (0 ≤ stock ∧ stock < next_stock) →
       StockFeasiblePortfolio
         ask bid buy sell max_stock wait days stock profit →
       profit ≤ answer)))

@[match_pattern] abbrev StockTradingHistory_first_buy (ask bid buy sell : List Int) (max_stock wait : Int) :=
  @StockTradingHistory.StockTradingHistory_first_buy ask bid buy sell max_stock wait

@[match_pattern] abbrev StockTradingHistory_buy (ask bid buy sell : List Int) (max_stock wait : Int) :=
  @StockTradingHistory.StockTradingHistory_buy ask bid buy sell max_stock wait

@[match_pattern] abbrev StockTradingHistory_sell (ask bid buy sell : List Int) (max_stock wait : Int) :=
  @StockTradingHistory.StockTradingHistory_sell ask bid buy sell max_stock wait


private theorem table_shape_replace (table : List (List Int)) (days max_stock row : Int)
    (newrow : List Int) (hs : StockTableShape table days max_stock)
    (hr : 0 ≤ row ∧ row < days+1) (hl : Zlength newrow = max_stock+1) :
    StockTableShape (replace_Znth row newrow table) days max_stock := by
  refine ⟨?_,?_⟩
  · rw [Zlength_replace_Znth]; exact hs.1
  · intro r h
    by_cases he : r = row
    · subst r; rw [Znth_replace_Znth_Same [] table row newrow (by rw [hs.1]; exact hr)]; exact hl
    · rw [Znth_replace_Znth_Diff [] table row r newrow (by rw [hs.1]; exact hr) (by rw [hs.1]; exact h) (Ne.symm he)]
      exact hs.2 r h

private theorem table_bounded_replace (table : List (List Int)) (days max_stock row : Int)
    (newrow : List Int) (hs : StockTableShape table days max_stock)
    (hb : StockTableValuesBounded table days max_stock)
    (hr : 0 ≤ row ∧ row < days+1)
    (hn : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock newrow 0 ∧ Znth stock newrow 0 ≤ STOCK_MAX_PROFIT) :
    StockTableValuesBounded (replace_Znth row newrow table) days max_stock := by
  intro r stock h hk
  by_cases he : r = row
  · subst r; rw [Znth_replace_Znth_Same [] table row newrow (by rw [hs.1]; exact hr)]; exact hn stock hk
  · rw [Znth_replace_Znth_Diff [] table row r newrow (by rw [hs.1]; exact hr) (by rw [hs.1]; exact h) (Ne.symm he)]
    exact hb r stock h hk

private theorem row_bounded_replace (row : List Int) (max_stock col value : Int)
    (hl : Zlength row = max_stock+1)
    (hc : 0 ≤ col ∧ col < max_stock+1)
    (hv : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT)
    (hb : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock row 0 ∧ Znth stock row 0 ≤ STOCK_MAX_PROFIT) :
    ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock (replace_Znth col value row) 0 ∧ Znth stock (replace_Znth col value row) 0 ≤ STOCK_MAX_PROFIT := by
  intro stock hs
  by_cases he : stock = col
  · subst stock; rw [Znth_replace_Znth_Same 0 row col value (by omega)]; exact hv
  · rw [Znth_replace_Znth_Diff 0 row col stock value (by omega) (by omega) (Ne.symm he)]
    exact hb stock hs

private theorem days_done_replace (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait next_day row : Int) (newrow : List Int)
    (hd : StockDaysDone ask bid buy sell table max_stock wait next_day)
    (hr : 0 ≤ row ∧ row < Zlength ask+1) (hnr : next_day ≤ row)
    (hl : Zlength newrow = max_stock+1)
    (hb : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock newrow 0 ∧ Znth stock newrow 0 ≤ STOCK_MAX_PROFIT) :
    StockDaysDone ask bid buy sell (replace_Znth row newrow table) max_stock wait next_day := by
  refine ⟨table_shape_replace table (Zlength ask) max_stock row newrow hd.1 hr hl,
    table_bounded_replace table (Zlength ask) max_stock row newrow hd.1 hd.2.1 hr hb,hd.2.2.1,?_⟩
  intro day stock hday hs
  rw [Znth_replace_Znth_Diff [] table row day newrow (by rw [hd.1.1]; exact hr) (by rw [hd.1.1]; omega) (by omega)]
  exact hd.2.2.2 day stock hday hs

private theorem trade_product_bounded (amount price max_stock : Int)
    (ha : 0 ≤ amount ∧ amount ≤ max_stock) (hp : 0 ≤ price ∧ price ≤ 1000) :
    0 ≤ amount*price ∧ amount*price ≤ max_stock*1000 :=
  ⟨Int.mul_nonneg ha.1 hp.1,Int.mul_le_mul ha.2 hp.2 hp.1 (by omega)⟩

private theorem first_buy_bounded (amount price max_stock : Int)
    (ha : 0 ≤ amount ∧ amount ≤ max_stock) (hp : 0 ≤ price ∧ price ≤ 1000)
    (hm : max_stock ≤ 990) :
    STOCK_NEG_INF ≤ -amount*price ∧ -amount*price ≤ STOCK_MAX_PROFIT := by
  have ht := trade_product_bounded amount price max_stock ha hp
  simp only [Int.neg_mul]
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT
  omega

theorem StockBuyQueue_replace_other_row__buy_cell_progress :
  ∀ table queue source price lower upper head tail row_index row,
    (0 ≤ source ∧ source < Zlength table) →
    (0 ≤ row_index ∧ row_index < Zlength table) →
    source ≠ row_index →
    StockBuyQueue table queue source price lower upper head tail →
    StockBuyQueue (replace_Znth row_index row table) queue source price
      lower upper head tail := by
  intro table queue source price lower upper head tail row_index row hs hr hne hq
  unfold StockBuyQueue StockFiniteIndexInWindow StockBuyScore at *
  simpa only [Znth_replace_Znth_Diff ([] : List Int) table row_index source row hr hs (Ne.symm hne)] using hq

theorem same_index_different_default:
  ∀ (i : Int) (dp_l_2 : List (List Int)) (__default__List_Z : List Int),
    (0 ≤ i ∧ i < Zlength dp_l_2) →
    (Znth i dp_l_2 []) = (Znth i dp_l_2 __default__List_Z) := by
  intro i table d hi
  exact Znth_indep table i [] d hi

theorem StockDaysDone_cell_bounded__safety_sell :
  ∀ ask bid buy sell table days max_stock wait next_day row stock
         (default_row : List Int),
    StockInputsBounded ask bid buy sell days max_stock →
    StockDaysDone ask bid buy sell table max_stock wait next_day →
    StockTableShape table days max_stock →
    (0 ≤ row ∧ row < days + 1) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    (STOCK_NEG_INF ≤ Znth stock (Znth row table default_row) 0 ∧ Znth stock (Znth row table default_row) 0 ≤ STOCK_MAX_PROFIT)  := by
  intro ask bid buy sell table days max_stock wait next_day row stock d hi hd hs hr hk
  have hb := hd.2.1
  unfold StockTableValuesBounded at hb
  rw [hi.1] at hb
  rw [← same_index_different_default row table d (by rw [hs.1]; exact hr)]
  exact hb row stock hr (by omega)

theorem StockDaysDone_cell_bounded__safety_buy :
  ∀ ask bid buy sell table days max_stock wait next_day row stock
         (default_row : List Int),
    StockInputsBounded ask bid buy sell days max_stock →
    StockDaysDone ask bid buy sell table max_stock wait next_day →
    StockTableShape table days max_stock →
    (0 ≤ row ∧ row < days + 1) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    (STOCK_NEG_INF ≤ Znth stock (Znth row table default_row) 0 ∧ Znth stock (Znth row table default_row) 0 ≤ STOCK_MAX_PROFIT)  := by
  intro ask bid buy sell table days max_stock wait next_day row stock d hi hd hs hr hk
  have hb := hd.2.1
  unfold StockTableValuesBounded at hb
  rw [hi.1] at hb
  rw [← same_index_different_default row table d (by rw [hs.1]; exact hr)]
  exact hb row stock hr (by omega)

theorem stock_fill_cells_snoc__init_copy :
  ∀ current max_stock row col value,
    StockFillCells current max_stock row col →
    col < max_stock + 1 →
    value = StockInitialCell row col →
    StockFillCells (replace_Znth col value current)
      max_stock row (col + 1) := by
  intro current max_stock row col value hf hc hv
  rcases hf with ⟨hr,hl,hf⟩
  refine ⟨by omega,?_,?_⟩
  · rw [Zlength_replace_Znth]; exact hl
  · intro stock hs
    by_cases he : stock = col
    · subst stock
      rw [Znth_replace_Znth_Same 0 current col value (by omega)]
      exact hv
    · rw [Znth_replace_Znth_Diff 0 current col stock value (by omega) (by omega) (Ne.symm he)]
      exact hf stock (by omega)

theorem stock_initial_cell_bounded__init_copy :
  ∀ row stock,
    (STOCK_NEG_INF ≤ StockInitialCell row stock ∧ StockInitialCell row stock ≤ STOCK_MAX_PROFIT)  := by
  intro row stock
  unfold StockInitialCell STOCK_NEG_INF STOCK_MAX_PROFIT
  split <;> (try split) <;> omega

theorem stock_trading_history_day_positive__init_copy :
  ∀ ask bid buy sell max_stock wait day stock profit,
    0 ≤ wait →
    StockTradingHistory ask bid buy sell max_stock wait day stock profit →
    1 ≤ day := by
  intro ask bid buy sell max_stock wait day stock profit hw hh
  induction hh <;> omega

theorem stock_initial_portfolio_value__init_copy :
  ∀ ask bid buy sell max_stock wait stock,
    0 ≤ wait →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockPortfolioValue ask bid buy sell max_stock wait 0 stock
      (StockInitialCell 0 stock) := by
  intro ask bid buy sell max_stock wait stock hw hs
  refine ⟨hs,?_⟩
  by_cases he : stock = 0
  · subst stock
    simp only [StockInitialCell,ite_true]
    refine Or.inr ⟨Or.inl ⟨rfl,rfl⟩,?_⟩
    intro profit hf
    rcases hf with ⟨_,hp⟩ | ⟨last,hl,hh⟩
    · omega
    · omega
  · simp only [StockInitialCell,ite_true,if_neg he]
    refine Or.inl ⟨by trivial,?_⟩
    rintro ⟨profit,hf⟩
    rcases hf with ⟨hz,_⟩ | ⟨last,hl,hh⟩ <;> omega

theorem stock_completed_initial_table_days_done__init_copy :
  ∀ ask bid buy sell table days max_stock wait,
    0 ≤ wait →
    StockInputsBounded ask bid buy sell days max_stock →
    StockFillRows table days max_stock (days + 1) →
    StockDaysDone ask bid buy sell table max_stock wait 1 ∧
    StockTableShape table days max_stock := by
  intro ask bid buy sell table days max_stock wait hw hi hf
  rcases hf with ⟨hrow,hshape,hcells⟩
  refine ⟨?_,hshape⟩
  unfold StockDaysDone
  rw [hi.1]
  refine ⟨hshape,?_,by omega,?_⟩
  · intro row stock hr hs
    rw [(hcells row stock hr hs).2]
    exact stock_initial_cell_bounded__init_copy row stock
  · intro day stock hd hs
    have he : day = 0 := by omega
    subst day
    have hlo := hi.2.2.2.2.1
    rw [(hcells 0 stock (by omega) (by omega)).2]
    exact stock_initial_portfolio_value__init_copy ask bid buy sell max_stock wait stock hw hs

theorem stock_fill_update_step__init_copy :
  ∀ table days max_stock row col value d,
    StockFillRows table days max_stock row →
    StockFillCells (Znth row table d) max_stock row col →
    (0 ≤ row ∧ row < days + 1) →
    col < max_stock + 1 →
    value = StockInitialCell row col →
    let row' := replace_Znth col value (Znth row table d) ;
    let table' := replace_Znth row row' table ;
    StockFillRows table' days max_stock row ∧
    StockFillCells (Znth row table' d) max_stock row (col + 1) := by
  intro table days max_stock row col value d hr hc hrow hcol hv
  rcases hr with ⟨hrange,hshape,hcells⟩
  have hrl : 0 ≤ row ∧ row < Zlength table := by rw [hshape.1]; exact hrow
  have hnewcells := stock_fill_cells_snoc__init_copy (Znth row table d) max_stock row col value hc hcol hv
  have hlen : Zlength (replace_Znth col value (Znth row table d)) = max_stock+1 := by rw [Zlength_replace_Znth]; exact hc.2.1
  dsimp only
  constructor
  · refine ⟨hrange,table_shape_replace table days max_stock row _ hshape hrow hlen,?_⟩
    intro day stock hd hs
    rw [Znth_replace_Znth_Diff [] table row day _ hrl (by rw [hshape.1]; omega) (by omega)]
    exact hcells day stock hd hs
  · rw [Znth_replace_Znth_Same d table row _ hrl]
    exact hnewcells

theorem stock_copy_update_step__init_copy :
  ∀ ask bid buy sell table max_stock wait day col value,
    StockTableShape table (Zlength ask) max_stock →
    StockCopyProgress ask bid buy sell table max_stock wait day col →
    value = Znth col (Znth (day - 1) table []) 0 →
    (0 ≤ day ∧ day < Zlength ask + 1) →
    (0 ≤ col ∧ col < max_stock + 1) → col ≤ max_stock →
    let row' := replace_Znth col value (Znth day table []) ;
    let table' := replace_Znth day row' table ;
    StockCopyProgress ask bid buy sell table' max_stock wait day (col + 1) ∧
    StockTableShape table' (Zlength ask) max_stock := by
  intro ask bid buy sell table max_stock wait day col value hshape hcopy hv hday hcol hc
  rcases hcopy with ⟨hd,hday1,hcr,hcop⟩
  have hlen := hshape.2 day hday
  have hrowlen : 0 ≤ day ∧ day < Zlength table := by rw [hshape.1]; exact hday
  have hvb : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT := by
    rw [hv]
    exact hd.2.1 (day-1) col (by omega) hcol
  have hnewlen : Zlength (replace_Znth col value (Znth day table [])) = max_stock+1 := by rw [Zlength_replace_Znth]; exact hlen
  have hnewbound := row_bounded_replace (Znth day table []) max_stock col value hlen hcol hvb (hd.2.1 day · hday)
  have hdone := days_done_replace ask bid buy sell table max_stock wait day day _ hd hday (by omega) hnewlen hnewbound
  dsimp only
  refine ⟨⟨hdone,hday1,by omega,?_⟩,hdone.1⟩
  intro stock hs
  rw [Znth_replace_Znth_Same [] table day _ hrowlen,
    Znth_replace_Znth_Diff [] table day (day-1) _ hrowlen (by rw [hshape.1]; omega) (by omega)]
  by_cases he : stock = col
  · subst stock
    rw [Znth_replace_Znth_Same 0 (Znth day table []) col value (by omega)]
    exact hv
  · rw [Znth_replace_Znth_Diff 0 (Znth day table []) col stock value (by omega) (by omega) (Ne.symm he)]
    exact hcop stock (by omega)

theorem stock_trading_history_day_positive__early_buy :
  ∀ ask bid buy sell max_stock wait day stock profit,
    0 ≤ wait →
    StockTradingHistory ask bid buy sell max_stock wait day stock profit →
    1 ≤ day := by
  intro ask bid buy sell max_stock wait day stock profit hw hh
  induction hh <;> omega

theorem stock_feasible_early_day_iff__early_buy :
  ∀ ask bid buy sell max_stock wait day stock profit,
    0 ≤ wait → 1 ≤ day → day - 1 ≤ wait →
    (StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit ↔
    StockFeasiblePortfolio ask bid buy sell max_stock wait (day - 1) stock profit ∨
    ((1 ≤ stock ∧ stock ≤ Znth (day - 1) buy 0) ∧ stock ≤ max_stock ∧
     profit = - stock * Znth (day - 1) ask 0)) := by
  intro ask bid buy sell max_stock wait day stock profit hw hd hearly
  constructor
  · intro hf
    rcases hf with hz | ⟨last,hl,hh⟩
    · exact Or.inl (Or.inl hz)
    · by_cases he : last < day
      · exact Or.inl (Or.inr ⟨last,by omega,hh⟩)
      · have heq : last = day := by omega
        subst last
        cases hh with
        | StockTradingHistory_first_buy day amount hd ha hm => exact Or.inr ⟨ha,hm,rfl⟩
        | StockTradingHistory_buy pd ps pp day amount hp hwait ha hm =>
          have hdpos := stock_trading_history_day_positive__early_buy ask bid buy sell max_stock wait pd ps pp hw hp
          omega
        | StockTradingHistory_sell pd ps pp day amount hp hwait ha hm =>
          have hdpos := stock_trading_history_day_positive__early_buy ask bid buy sell max_stock wait pd ps pp hw hp
          omega
  · rintro (hf | ⟨ha,hm,hp⟩)
    · rcases hf with hz | ⟨last,hl,hh⟩
      · exact Or.inl hz
      · exact Or.inr ⟨last,by omega,hh⟩
    · subst profit
      exact Or.inr ⟨day,by omega,StockTradingHistory_first_buy ask bid buy sell max_stock wait day stock hd ha hm⟩

theorem stock_portfolio_extend_first_buy__early_buy :
  ∀ ask bid buy sell max_stock wait day stock old candidate,
    0 ≤ wait → 1 ≤ day → day - 1 ≤ wait →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    (1 ≤ stock ∧ stock ≤ Znth (day - 1) buy 0) →
    candidate = - stock * Znth (day - 1) ask 0 →
    STOCK_NEG_INF ≤ candidate →
    StockPortfolioValue ask bid buy sell max_stock wait (day - 1) stock old →
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (max old candidate) := by
  intro ask bid buy sell max_stock wait day stock old candidate hw hd he hs hb hc hlo ho
  have hiff := stock_feasible_early_day_iff__early_buy ask bid buy sell max_stock wait day stock
  have hcf : StockFeasiblePortfolio ask bid buy sell max_stock wait day stock candidate := (hiff candidate hw hd he).2 (Or.inr ⟨hb,hs.2,hc⟩)
  refine ⟨hs,Or.inr ⟨?_,?_⟩⟩
  · rcases ho.2 with ⟨ho,_⟩ | ⟨hf,hm⟩
    · rw [ho,Int.max_eq_right hlo]; exact hcf
    · by_cases hle : old ≤ candidate
      · rw [Int.max_eq_right hle]; exact hcf
      · rw [Int.max_eq_left (by omega)]; exact (hiff old hw hd he).2 (Or.inl hf)
  · intro profit hp
    rcases (hiff profit hw hd he).1 hp with hprev | ⟨_,_,hprofit⟩
    · rcases ho.2 with ⟨_,hn⟩ | ⟨_,hm⟩
      · exact False.elim (hn ⟨profit,hprev⟩)
      · exact Int.le_trans (hm profit hprev) (Int.le_max_left _ _)
    · rw [← hc] at hprofit
      rw [hprofit]; exact Int.le_max_right _ _

theorem stock_portfolio_no_first_buy__early_buy :
  ∀ ask bid buy sell max_stock wait day stock value,
    0 ≤ wait → 1 ≤ day → day - 1 ≤ wait →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    (stock = 0 ∨ Znth (day - 1) buy 0 < stock) →
    StockPortfolioValue ask bid buy sell max_stock wait (day - 1) stock value →
    StockPortfolioValue ask bid buy sell max_stock wait day stock value := by
  intro ask bid buy sell max_stock wait day stock value hw hd he hs hn ho
  have hiff (profit : Int) : StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit ↔ StockFeasiblePortfolio ask bid buy sell max_stock wait (day-1) stock profit := by
    constructor
    · intro hf
      rcases (stock_feasible_early_day_iff__early_buy ask bid buy sell max_stock wait day stock profit hw hd he).1 hf with hp | ⟨ha,_,_⟩
      · exact hp
      · omega
    · intro hp
      exact (stock_feasible_early_day_iff__early_buy ask bid buy sell max_stock wait day stock profit hw hd he).2 (Or.inl hp)
  refine ⟨hs,?_⟩
  rcases ho.2 with ⟨heq,hnone⟩ | ⟨hf,hm⟩
  · exact Or.inl ⟨heq,fun ⟨p,hp⟩ => hnone ⟨p,(hiff p).1 hp⟩⟩
  · exact Or.inr ⟨(hiff value).2 hf,fun p hp => hm p ((hiff p).1 hp)⟩

theorem stock_early_buy_complete__early_buy :
  ∀ ask bid buy sell table days max_stock wait day next_stock,
    StockInputsBounded ask bid buy sell days max_stock →
    StockEarlyBuyProgress ask bid buy sell table max_stock wait day next_stock →
    (1 ≤ day ∧ day ≤ days) → day - 1 ≤ wait →
    Znth (day - 1) buy 0 < next_stock →
    StockDaysDone ask bid buy sell table max_stock wait (day + 1) := by
  intro ask bid buy sell table days max_stock wait day next_stock hi hp hday he hf
  have hm := hi.2.2.2.2.2.1
  obtain ⟨hba,hask,hbuy,hsell⟩ := hi.2.2.2.2.2.2 day hday
  rcases hp with ⟨hd,hd1,hnext,hzero,hcells⟩
  refine ⟨hd.1,hd.2.1,by omega,?_⟩
  intro d stock hdr hs
  by_cases hlt : d < day
  · exact hd.2.2.2 d stock (by omega) hs
  · have heq : d = day := by omega
    subst d
    have hold := hd.2.2.2 (day-1) stock (by omega) hs
    by_cases heq : stock = 0
    · subst stock
      rw [hzero]
      exact stock_portfolio_no_first_buy__early_buy ask bid buy sell max_stock wait day 0 _ (by omega) hd1 he hs (Or.inl rfl) hold
    · have hc := hcells stock (by omega)
      by_cases hproc : stock < next_stock
      · rw [if_pos hproc] at hc
        rw [hc]
        have hbound := first_buy_bounded stock (Znth (day-1) ask 0) max_stock hs (by omega) hm.2
        exact stock_portfolio_extend_first_buy__early_buy ask bid buy sell max_stock wait day stock _ _ (by omega) hd1 he hs (by omega) rfl hbound.1 hold
      · rw [if_neg hproc] at hc
        rw [hc]
        exact stock_portfolio_no_first_buy__early_buy ask bid buy sell max_stock wait day stock _ (by omega) hd1 he hs (Or.inr (by omega)) hold

theorem stock_early_buy_update_step__early_buy :
  ∀ ask bid buy sell table max_stock wait day next_stock value days,
    StockInputsBounded ask bid buy sell days max_stock →
    StockEarlyBuyProgress ask bid buy sell table max_stock wait day next_stock →
    (1 ≤ day ∧ day ≤ days) →
    (1 ≤ next_stock ∧ next_stock ≤ Znth (day - 1) buy 0) →
    value = max (Znth next_stock (Znth (day - 1) table []) 0)
                  (- next_stock * Znth (day - 1) ask 0) →
    let row' := replace_Znth next_stock value (Znth day table []) ;
    let table' := replace_Znth day row' table ;
    StockEarlyBuyProgress ask bid buy sell table' max_stock wait day
      (next_stock + 1) ∧ StockTableShape table' days max_stock := by
  intro ask bid buy sell table max_stock wait day next_stock value days hi hp hday hn hv
  have hm := hi.2.2.2.2.2.1
  obtain ⟨hba,hask,hbuy,hsell⟩ := hi.2.2.2.2.2.2 day hday
  rcases hp with ⟨hd,hd1,hnext,hzero,hcells⟩
  have hdayidx : 0 ≤ day ∧ day < Zlength ask+1 := by rw [hi.1]; omega
  have hrowidx : 0 ≤ day ∧ day < Zlength table := by rw [hd.1.1]; exact hdayidx
  have hnidx : 0 ≤ next_stock ∧ next_stock < max_stock+1 := by omega
  have hrowlen := hd.1.2 day hdayidx
  have hnewlen : Zlength (replace_Znth next_stock value (Znth day table [])) = max_stock+1 := by rw [Zlength_replace_Znth]; exact hrowlen
  have hvalue : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT := by
    rw [hv]
    have hold := hd.2.1 (day-1) next_stock (by omega) hnidx
    have hnew := first_buy_bounded next_stock (Znth (day-1) ask 0) max_stock (by omega) (by omega) hm.2
    by_cases he : Znth next_stock (Znth (day-1) table []) 0 ≤ -next_stock*Znth (day-1) ask 0
    · rw [Int.max_eq_right he]; exact hnew
    · rw [Int.max_eq_left (by omega)]; exact hold
  have hbound := row_bounded_replace (Znth day table []) max_stock next_stock value hrowlen hnidx hvalue (hd.2.1 day · hdayidx)
  have hdone := days_done_replace ask bid buy sell table max_stock wait day day _ hd hdayidx (by omega) hnewlen hbound
  have hprev := Znth_replace_Znth_Diff ([] : List Int) table day (day-1) (replace_Znth next_stock value (Znth day table [])) hrowidx (by rw [hd.1.1]; omega) (by omega)
  have hrow := Znth_replace_Znth_Same ([] : List Int) table day (replace_Znth next_stock value (Znth day table [])) hrowidx
  dsimp only
  refine ⟨⟨hdone,hd1,by omega,?_,?_⟩,?_⟩
  · rw [hprev,hrow,Znth_replace_Znth_Diff 0 (Znth day table []) next_stock 0 value (by omega) (by omega) (by omega)]
    exact hzero
  · intro stock hs
    rw [hprev,hrow]
    by_cases heq : stock = next_stock
    · subst stock
      rw [Znth_replace_Znth_Same 0 (Znth day table []) next_stock value (by omega),if_pos (by omega)]
      exact hv
    · rw [Znth_replace_Znth_Diff 0 (Znth day table []) next_stock stock value (by omega) (by omega) (Ne.symm heq)]
      have hc := hcells stock hs
      by_cases hh : stock < next_stock
      · simpa only [if_pos hh,if_pos (by omega : stock < next_stock+1)] using hc
      · simpa only [if_neg hh,if_neg (by omega : ¬ stock < next_stock+1)] using hc
  · rw [← hi.1]; exact hdone.1

theorem StockSellQueueExpiring_empty__sell_expire:
  ∀ table queue source price lower upper head tail,
    StockSellQueueExpiring table queue source price lower upper head tail →
    head ≥ tail →
    StockSellQueue table queue source price lower upper head tail := by
  intro table queue source price lower upper head tail he hempty
  rcases he with ⟨hb,hv,hm,hc⟩ | hn
  · refine ⟨hb,?_,?_,?_⟩
    · intro pos hp; omega
    · intro l r hr; omega
    · intro candidate hh
      rcases hh with ⟨h0,hlen,hne,hr⟩
      obtain ⟨pos,hp,_⟩ := hc candidate ⟨h0,hlen,hne,by omega⟩
      omega
  · exact hn

theorem StockSellQueueExpiring_head_bounded__sell_expire:
  ∀ table queue source price lower upper head tail,
    StockSellQueueExpiring table queue source price lower upper head tail →
    head < tail →
    Znth head queue 0 ≤ upper →
    StockSellQueue table queue source price lower upper head tail := by
  intro table queue source price lower upper head tail he hht hhead
  rcases he with ⟨hb,hv,hm,hc⟩ | hn
  · refine ⟨hb,?_,hm,?_⟩
    · intro pos hp
      obtain ⟨h0,hl,hn,hr⟩ := hv pos hp
      refine ⟨h0,hl,hn,hr.1,?_⟩
      by_cases he : pos = head
      · subst pos; exact hhead
      · have ho := (hm head pos (by omega)).1; omega
    · intro candidate hh
      rcases hh with ⟨h0,hlen,hne,hr⟩
      exact hc candidate ⟨h0,hlen,hne,by omega⟩
  · exact hn

theorem StockSellQueue_drop_expired__sell_expire:
  ∀ table queue source price lower upper head tail,
    StockSellQueueExpiring table queue source price lower upper head tail →
    head < tail →
    Znth head queue 0 > upper →
    StockSellQueue table queue source price lower upper (head + 1) tail := by
  intro table queue source price lower upper head tail he hht hexp
  rcases he with ⟨hb,hv,hm,hc⟩ | hn
  · refine ⟨by omega,?_,?_,?_⟩
    · intro pos hp
      have hhead := (hv head (by omega)).2.2.2.2
      obtain ⟨h0,hl,hn,hr⟩ := hv pos (by omega)
      have ho := (hm head pos (by omega)).1
      exact ⟨h0,hl,hn,hr.1,by omega⟩
    · intro l r hr; exact hm l r (by omega)
    · intro candidate hh
      rcases hh with ⟨h0,hlen,hne,hr⟩
      obtain ⟨pos,hp,hi,hs⟩ := hc candidate ⟨h0,hlen,hne,by omega⟩
      have hn : pos ≠ head := by intro he; subst pos; omega
      exact ⟨pos,by omega,hi,hs⟩
  · have h := (hn.2.1 head (by omega)).2.2.2.2
    omega

theorem StockSellQueue_begin_popping__sell_pop_append :
  ∀ table queue source price incoming upper head tail,
    0 ≤ incoming →
    incoming < Zlength (Znth source table []) →
    Znth incoming (Znth source table []) 0 ≠ STOCK_NEG_INF →
    StockSellQueue table queue source price (incoming + 1) upper head tail →
    StockSellQueuePopping table queue source price incoming upper head tail := by
  intro table queue source price incoming upper head tail hi hl hn hq
  rcases hq with ⟨hb,hv,hm,hc⟩
  refine ⟨⟨hi,hl,hn⟩,hb,hv,hm,?_⟩
  intro candidate hh
  rcases hh with ⟨h0,hlen,hne,hr⟩
  by_cases he : candidate = incoming
  · subst candidate; exact Or.inl (by omega)
  · exact Or.inr (hc candidate ⟨h0,hlen,hne,by omega⟩)

theorem StockSellQueuePopping_drop_tail__sell_pop_append :
  ∀ table queue source price incoming upper head tail,
    StockSellQueuePopping table queue source price incoming upper head tail →
    head < tail →
    StockSellScore table source price (Znth (tail - 1) queue 0) ≤ StockSellScore table source price incoming →
    StockSellQueuePopping table queue source price incoming upper head (tail - 1) := by
  intro table queue source price incoming upper head tail hp hht hlast
  rcases hp with ⟨hi,hb,hv,hm,hc⟩
  refine ⟨hi,by omega,?_,?_,?_⟩
  · intro pos hp; exact hv pos (by omega)
  · intro l r hr; exact hm l r (by omega)
  · intro candidate hh
    rcases hc candidate hh with hn | ⟨pos,hpos,hidx,hscore⟩
    · exact Or.inl hn
    · by_cases he : pos = tail-1
      · subst pos; exact Or.inl (by omega)
      · exact Or.inr ⟨pos,by omega,hidx,hscore⟩

theorem StockBuyQueue_begin_popping__buy_pop_append :
  ∀ table queue source price lower incoming head tail,
    0 ≤ incoming →
    incoming < Zlength (Znth source table []) →
    Znth incoming (Znth source table []) 0 ≠ STOCK_NEG_INF →
    StockBuyQueue table queue source price lower (incoming - 1) head tail →
    StockBuyQueuePopping table queue source price lower incoming head tail := by
  intro table queue source price lower incoming head tail hi hl hn hq
  rcases hq with ⟨hb,hv,hm,hc⟩
  refine ⟨⟨hi,hl,hn⟩,hb,hv,hm,?_⟩
  intro candidate hh
  rcases hh with ⟨h0,hlen,hne,hr⟩
  by_cases he : candidate = incoming
  · subst candidate; exact Or.inl (by omega)
  · exact Or.inr (hc candidate ⟨h0,hlen,hne,by omega⟩)

theorem StockBuyQueuePopping_drop_tail__buy_pop_append :
  ∀ table queue source price lower incoming head tail,
    StockBuyQueuePopping table queue source price lower incoming head tail →
    head < tail →
    StockBuyScore table source price (Znth (tail - 1) queue 0) ≤ StockBuyScore table source price incoming →
    StockBuyQueuePopping table queue source price lower incoming head (tail - 1) := by
  intro table queue source price lower incoming head tail hp hht hlast
  rcases hp with ⟨hi,hb,hv,hm,hc⟩
  refine ⟨hi,by omega,?_,?_,?_⟩
  · intro pos hp; exact hv pos (by omega)
  · intro l r hr; exact hm l r (by omega)
  · intro candidate hh
    rcases hc candidate hh with hn | ⟨pos,hpos,hidx,hscore⟩
    · exact Or.inl hn
    · by_cases he : pos = tail-1
      · subst pos; exact Or.inl (by omega)
      · exact Or.inr ⟨pos,by omega,hidx,hscore⟩

theorem StockBuyQueue_extend_invalid__buy_cell_progress :
  ∀ table queue source price lower upper head tail,
    StockBuyQueue table queue source price lower (upper - 1) head tail →
    (0 ≤ upper ∧ upper < Zlength (Znth source table [])) →
    Znth upper (Znth source table []) 0 = STOCK_NEG_INF →
    StockBuyQueue table queue source price lower upper head tail := by
  intro table queue source price lower upper head tail hq hu hinv
  rcases hq with ⟨hb,hv,hm,hc⟩
  refine ⟨hb,?_,hm,?_⟩
  · intro pos hp
    obtain ⟨h0,hlen,hn,hr⟩ := hv pos hp
    exact ⟨h0,hlen,hn,by omega⟩
  · intro candidate hh
    rcases hh with ⟨h0,hlen,hn,hr⟩
    have he : candidate ≠ upper := by intro he; subst candidate; exact hn hinv
    exact hc candidate ⟨h0,hlen,hn,by omega⟩

theorem StockBuyCellValue_empty_queue__buy_cell_progress :
  ∀ ask bid buy sell table max_stock wait day source stock
         queue price buy_cap head tail,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock →
    stock ≤ max_stock →
    stock < Zlength (Znth source table []) →
    StockBuyQueue table queue source price
      (stock - buy_cap) (stock - 1) head tail →
    head ≥ tail →
    buy_cap = Znth (day - 1) buy 0 →
    StockBuyCellValue ask bid buy sell table max_stock day source stock
      (Znth stock (Znth day table []) 0) := by
  intro ask bid buy sell table max_stock wait day source stock queue price buy_cap head tail hp hs hl hq hempty hcap
  have hsell := hp.2.2.2.2.2.2 stock (by omega)
  refine ⟨⟨⟨0,Or.inl ⟨rfl,hsell⟩⟩,?_⟩,⟨_,hsell⟩⟩
  intro amount candidate hc
  rcases hc with ⟨_,hc⟩ | ⟨ha,hamt,hn,hv⟩
  · obtain ⟨sa,hsa⟩ := hc.1
    exact hsell.2 sa candidate hsa
  · obtain ⟨pos,hpos,_⟩ := hq.2.2.2 (stock-amount) ⟨by omega,by omega,hn,by omega⟩
    omega

theorem StockBuyProgress_step_same__buy_cell_progress :
  ∀ ask bid buy sell table max_stock wait day source stock,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock →
    stock ≤ max_stock →
    StockBuyCellValue ask bid buy sell table max_stock day source stock
      (Znth stock (Znth day table []) 0) →
    StockBuyProgress ask bid buy sell table max_stock wait day source (stock + 1) := by
  intro ask bid buy sell table max_stock wait day source stock hp hs hc
  rcases hp with ⟨hd,hday,hsource,hsr,hstock,hbuy,hsell⟩
  refine ⟨hd,hday,hsource,hsr,by omega,?_,?_⟩
  · intro k hk
    by_cases he : k < stock
    · exact hbuy k (by omega)
    · have heq : k = stock := by omega
      subst k; exact hc
  · intro k hk; exact hsell k (by omega)

theorem stock_answer_init__outer_answer :
  ∀ ask bid buy sell table days max_stock wait i,
    0 ≤ max_stock → i > days → i ≤ days + 1 →
    StockDaysDone ask bid buy sell table max_stock wait i →
    StockAnswerProgress ask bid buy sell table days max_stock wait 0 0 := by
  intro ask bid buy sell table days max_stock wait i hm hi hib hd
  have he : i = days+1 := by omega
  subst i
  exact ⟨hd,by omega,by omega,Or.inl ⟨rfl,rfl⟩⟩

theorem stock_answer_improve__outer_answer :
  ∀ ask bid buy sell table days max_stock wait j answer value,
    0 ≤ days → 0 ≤ answer → j ≤ max_stock →
    StockAnswerProgress ask bid buy sell table days max_stock wait j answer →
    value = Znth j (Znth days table []) 0 →
    value > answer →
    StockAnswerProgress ask bid buy sell table days max_stock wait (j + 1) value := by
  intro ask bid buy sell table days max_stock wait j answer value hdays hans hj hp hv hgt
  rcases hp with ⟨hd,hjr,han,hpref⟩
  have hcell : StockPortfolioValue ask bid buy sell max_stock wait days j value := by
    rw [hv]; exact hd.2.2.2 days j (by omega) (by omega)
  have hfeas : StockFeasiblePortfolio ask bid buy sell max_stock wait days j value := by
    rcases hcell.2 with ⟨hneg,_⟩ | ⟨hf,_⟩
    · unfold STOCK_NEG_INF at hneg; omega
    · exact hf
  have hmax (profit : Int) (hf : StockFeasiblePortfolio ask bid buy sell max_stock wait days j profit) : profit ≤ value := by
    rcases hcell.2 with ⟨_,hn⟩ | ⟨_,hm⟩
    · exact False.elim (hn ⟨profit,hf⟩)
    · exact hm profit hf
  refine ⟨hd,by omega,by omega,Or.inr ⟨by omega,⟨j,by omega,hfeas⟩,?_⟩⟩
  intro stock profit hs hf
  by_cases he : stock < j
  · rcases hpref with ⟨hz,_⟩ | ⟨_,_,hm⟩
    · omega
    · have h := hm stock profit (by omega) hf; omega
  · have heq : stock = j := by omega
    subst stock; exact hmax profit hf

theorem stock_answer_keep__outer_answer :
  ∀ ask bid buy sell table days max_stock wait j answer value,
    0 ≤ days → j ≤ max_stock →
    StockAnswerProgress ask bid buy sell table days max_stock wait j answer →
    value = Znth j (Znth days table []) 0 →
    value ≤ answer →
    StockAnswerProgress ask bid buy sell table days max_stock wait (j + 1) answer := by
  intro ask bid buy sell table days max_stock wait j answer value hdays hj hp hv hle
  rcases hp with ⟨hd,hjr,hans,hpref⟩
  have hcell : StockPortfolioValue ask bid buy sell max_stock wait days j value := by
    rw [hv]; exact hd.2.2.2 days j (by omega) (by omega)
  have hmax (profit : Int) (hf : StockFeasiblePortfolio ask bid buy sell max_stock wait days j profit) : profit ≤ answer := by
    rcases hcell.2 with ⟨_,hn⟩ | ⟨_,hm⟩
    · exact False.elim (hn ⟨profit,hf⟩)
    · have h := hm profit hf; omega
  refine ⟨hd,by omega,hans,Or.inr ⟨by omega,?_⟩⟩
  rcases hpref with ⟨hj0,ha0⟩ | ⟨_,⟨stock,hs,hf⟩,hm⟩
  · subst j answer
    refine ⟨⟨0,by omega,Or.inl ⟨rfl,rfl⟩⟩,?_⟩
    intro stock profit hs hf
    have he : stock = 0 := by omega
    subst stock; exact hmax profit hf
  · refine ⟨⟨stock,by omega,hf⟩,?_⟩
    intro k profit hk hf
    by_cases he : k < j
    · exact hm k profit (by omega) hf
    · have heq : k = j := by omega
      subst k; exact hmax profit hf

theorem stock_answer_finish__outer_answer :
  ∀ ask bid buy sell table days max_stock wait j answer,
    0 ≤ max_stock → j > max_stock → j ≤ max_stock + 1 →
    StockAnswerProgress ask bid buy sell table days max_stock wait j answer →
    StockMaximumProfit ask bid buy sell days max_stock wait answer := by
  intro ask bid buy sell table days max_stock wait j answer hm hj hjb hp
  rcases hp.2.2.2 with ⟨hz,_⟩ | ⟨_,⟨stock,hs,hf⟩,hmax⟩
  · omega
  · refine ⟨stock,by omega,hf,?_⟩
    intro k profit hk hf
    exact hmax k profit (by omega) hf

theorem StockSellCellValue_empty_queue :
  ∀ bid sell sell_cap table max_stock day source stock queue head tail,
    0 ≤ stock →
    stock < max_stock →
    head ≥ tail →
    Znth (day - 1) sell 0 = sell_cap →
    (0 ≤ source ∧ source < day) →
    StockTableShape table day max_stock →
    (∀ k,( 0 ≤ k ∧ k ≤ stock) →
      Znth k (Znth day table []) 0 = Znth k (Znth (day - 1) table []) 0) →
    StockSellQueue table queue source (Znth (day - 1) bid 0) (stock + 1) (stock + sell_cap) head tail →
    StockSellCellValue bid sell table max_stock day source stock
      (Znth stock (Znth day table []) 0) := by
  intro bid sell sell_cap table max_stock day source stock queue head tail hs hsm hempty hcap hsource hshape hcopy hq
  have hcop := hcopy stock (by omega)
  refine ⟨⟨0,Or.inl ⟨rfl,hcop⟩⟩,?_⟩
  intro amount candidate hc
  rcases hc with ⟨_,he⟩ | ⟨ha,hmax,hn,hv⟩
  · omega
  · have hl := hshape.2 source (by omega)
    obtain ⟨pos,hp,_⟩ := hq.2.2.2 (stock+amount) ⟨by omega,by omega,hn,by omega⟩
    omega

theorem StockSellQueuePending_append__sell_pop_append :
  ∀ table queue source price incoming upper head tail,
    incoming ≤ upper →
    StockSellQueuePending table queue source price incoming upper head tail →
    StockSellQueue table (replace_Znth tail incoming queue)
      source price incoming upper head (tail + 1) := by
  intro table queue source price incoming upper head tail hlim hp
  rcases hp with ⟨⟨hi,hb,hv,hm,hc⟩,hlen,hlast⟩
  have htail : 0 ≤ tail ∧ tail < Zlength queue := by omega
  have hsame := Znth_replace_Znth_Same 0 queue tail incoming htail
  have hdiff (pos : Int) (hp : head ≤ pos ∧ pos < tail) := Znth_replace_Znth_Diff 0 queue tail pos incoming htail (by omega) (by omega)
  refine ⟨by omega,?_,?_,?_⟩
  · intro pos hp
    by_cases he : pos = tail
    · subst pos; rw [hsame]; exact ⟨hi.1,hi.2.1,hi.2.2,by omega⟩
    · rw [hdiff pos (by omega)]
      obtain ⟨h0,hl,hn,hr⟩ := hv pos (by omega)
      exact ⟨h0,hl,hn,by omega⟩
  · intro l r hr
    by_cases he : r = tail
    · subst r
      rw [hsame,hdiff l (by omega)]
      have hvr := (hv l (by omega)).2.2.2
      have hls := hlast (by omega)
      constructor
      · omega
      · by_cases he : l = tail-1
        · subst l; omega
        · have hms := (hm l (tail-1) (by omega)).2
          omega
    · rw [hdiff l (by omega),hdiff r (by omega)]
      exact hm l r (by omega)
  · intro candidate hh
    rcases hc candidate hh with hn | ⟨pos,hp,hidx,hscore⟩
    · refine ⟨tail,by omega,?_,?_⟩
      · rw [hsame]; have hr := hh.2.2.2; omega
      · rw [hsame]; exact hn
    · refine ⟨pos,by omega,?_,?_⟩
      · rw [hdiff pos hp]; exact hidx
      · rw [hdiff pos hp]; exact hscore

theorem stock_sell_queue_extend_lower_neg_inf__sell_cell_progress :
  ∀ table queue source price lower upper head tail,
    Znth lower (Znth source table []) 0 = STOCK_NEG_INF →
    StockSellQueue table queue source price (lower + 1) upper head tail →
    StockSellQueue table queue source price lower upper head tail := by
  intro table queue source price lower upper head tail hinv hq
  rcases hq with ⟨hb,hv,hm,hc⟩
  refine ⟨hb,?_,hm,?_⟩
  · intro pos hp
    obtain ⟨h0,hlen,hn,hr⟩ := hv pos hp
    exact ⟨h0,hlen,hn,by omega⟩
  · intro candidate hh
    rcases hh with ⟨h0,hlen,hn,hr⟩
    have he : candidate ≠ lower := by intro he; subst candidate; exact hn hinv
    exact hc candidate ⟨h0,hlen,hn,by omega⟩

theorem stock_trading_history_profit_bound__sell_cell_progress :
  ∀ ask bid buy sell max_stock wait day stock profit days,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    day ≤ days →
    StockTradingHistory ask bid buy sell max_stock wait day stock profit →
    (- (day * max_stock * 1000) ≤ profit ∧ profit ≤ day * max_stock * 1000)  := by
  intro ask bid buy sell max_stock wait day stock profit days hi hw hday hh
  have hm := hi.2.2.2.2.2.1
  have hvals := hi.2.2.2.2.2.2
  revert hday
  induction hh with
  | StockTradingHistory_first_buy day amount hd ha ham =>
    intro hday
    obtain ⟨hba,hask,hbuy,hsell⟩ := hvals day (by omega)
    have ht := trade_product_bounded amount (Znth (day-1) ask 0) max_stock (by omega) (by omega)
    have hscale := Int.mul_le_mul_of_nonneg_right hd (by omega : 0 ≤ max_stock*1000)
    simp only [Int.one_mul,← Int.mul_assoc] at hscale
    simp only [Int.neg_mul]
    omega
  | StockTradingHistory_buy pd ps pp day amount hp hwait ha ham ih =>
    intro hday
    have hdpos := stock_trading_history_day_positive__init_copy ask bid buy sell max_stock wait pd ps pp hw hp
    have hprev := ih (by omega)
    obtain ⟨hba,hask,hbuy,hsell⟩ := hvals day (by omega)
    have ht := trade_product_bounded amount (Znth (day-1) ask 0) max_stock (by omega) (by omega)
    have hstep := Int.mul_le_mul_of_nonneg_right (by omega : pd+1 ≤ day) (by omega : 0 ≤ max_stock*1000)
    simp only [Int.add_mul,Int.one_mul,← Int.mul_assoc] at hstep
    omega
  | StockTradingHistory_sell pd ps pp day amount hp hwait ha ham ih =>
    intro hday
    have hdpos := stock_trading_history_day_positive__init_copy ask bid buy sell max_stock wait pd ps pp hw hp
    have hprev := ih (by omega)
    obtain ⟨hba,hask,hbuy,hsell⟩ := hvals day (by omega)
    have ht := trade_product_bounded amount (Znth (day-1) bid 0) max_stock (by omega) (by omega)
    have hstep := Int.mul_le_mul_of_nonneg_right (by omega : pd+1 ≤ day) (by omega : 0 ≤ max_stock*1000)
    simp only [Int.add_mul,Int.one_mul,← Int.mul_assoc] at hstep
    omega

theorem StockBuyQueuePending_append__buy_pop_append :
  ∀ table queue source price lower incoming head tail,
    StockBuyQueuePending table queue source price lower incoming head tail →
    lower ≤ incoming →
    StockBuyQueue table (replace_Znth tail incoming queue)
      source price lower incoming head (tail + 1) := by
  intro table queue source price lower incoming head tail hp hlim
  rcases hp with ⟨⟨hi,hb,hv,hm,hc⟩,hlen,hlast⟩
  have htail : 0 ≤ tail ∧ tail < Zlength queue := by omega
  have hsame := Znth_replace_Znth_Same 0 queue tail incoming htail
  have hdiff (pos : Int) (hp : head ≤ pos ∧ pos < tail) := Znth_replace_Znth_Diff 0 queue tail pos incoming htail (by omega) (by omega)
  refine ⟨by omega,?_,?_,?_⟩
  · intro pos hp
    by_cases he : pos = tail
    · subst pos; rw [hsame]; exact ⟨hi.1,hi.2.1,hi.2.2,by omega⟩
    · rw [hdiff pos (by omega)]
      obtain ⟨h0,hl,hn,hr⟩ := hv pos (by omega)
      exact ⟨h0,hl,hn,by omega⟩
  · intro l r hr
    by_cases he : r = tail
    · subst r
      rw [hsame,hdiff l (by omega)]
      have hvr := (hv l (by omega)).2.2.2
      have hls := hlast (by omega)
      constructor
      · omega
      · by_cases he : l = tail-1
        · subst l; omega
        · have hms := (hm l (tail-1) (by omega)).2
          omega
    · rw [hdiff l (by omega),hdiff r (by omega)]
      exact hm l r (by omega)
  · intro candidate hh
    rcases hc candidate hh with hn | ⟨pos,hp,hidx,hscore⟩
    · refine ⟨tail,by omega,?_,?_⟩
      · rw [hsame]; have hr := hh.2.2.2; omega
      · rw [hsame]; exact hn
    · refine ⟨pos,by omega,?_,?_⟩
      · rw [hdiff pos hp]; exact hidx
      · rw [hdiff pos hp]; exact hscore

theorem StockBuyCellValue_improve__buy_cell_progress :
  ∀ ask bid buy sell table max_stock wait day source stock
         queue price buy_cap head tail best value,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock →
    stock ≤ max_stock →
    StockBuyQueue table queue source price
      (stock - buy_cap) (stock - 1) head tail →
    head < tail →
    best = Znth head queue 0 →
    buy_cap = Znth (day - 1) buy 0 →
    price = Znth (day - 1) ask 0 →
    value = StockBuyScore table source price best - stock * price →
    Znth stock (Znth day table []) 0 < value →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value := by
  intro ask bid buy sell table max_stock wait day source stock queue price buy_cap head tail best value hp hs hq hht hbest hcap hprice hvalue hcompare
  rcases hp with ⟨hd,hday,hsource,hsr,hstock,hbuy,hsell⟩
  have hsellv := hsell stock (by omega)
  have hrowlen := hd.1.2 source (by omega)
  rcases hq with ⟨hb,hv,hm,hc⟩
  subst best
  have hhead := hv head (by omega)
  have hh0 := hhead.1
  have hcandidate : StockBuyCandidate ask bid buy sell table max_stock day source stock (stock-Znth head queue 0) value := by
    refine Or.inr ⟨by have hr := hhead.2.2.2; omega,by omega,?_,?_⟩
    · have he : stock-(stock-Znth head queue 0) = Znth head queue 0 := by omega
      rw [he]; exact hhead.2.2.1
    · have he : stock-(stock-Znth head queue 0) = Znth head queue 0 := by omega
      rw [he,← hprice,Int.sub_mul]
      unfold StockBuyScore at hvalue
      omega
  refine ⟨⟨⟨stock-Znth head queue 0,hcandidate⟩,?_⟩,⟨_,hsellv⟩⟩
  intro amount candidate hcan
  rcases hcan with ⟨_,hsc⟩ | ⟨ha,has,hn,he⟩
  · obtain ⟨sa,hsa⟩ := hsc.1
    have hh := hsellv.2 sa candidate hsa
    omega
  · obtain ⟨pos,hpos,_,hscore⟩ := hc (stock-amount) ⟨by omega,by omega,hn,by omega⟩
    have hheadscore : StockBuyScore table source price (Znth pos queue 0) ≤ StockBuyScore table source price (Znth head queue 0) := by
      by_cases he : pos = head
      · subst pos; omega
      · have h := (hm head pos (by omega)).2; omega
    unfold StockBuyScore at hscore hheadscore hvalue
    rw [Int.sub_mul] at hscore
    rw [← hprice] at he
    omega

theorem StockBuyCellValue_keep__buy_cell_progress :
  ∀ ask bid buy sell table max_stock wait day source stock
         queue price buy_cap head tail best value,
    StockBuyProgress ask bid buy sell table max_stock wait day source stock →
    stock ≤ max_stock →
    StockBuyQueue table queue source price
      (stock - buy_cap) (stock - 1) head tail →
    head < tail →
    best = Znth head queue 0 →
    buy_cap = Znth (day - 1) buy 0 →
    price = Znth (day - 1) ask 0 →
    value = StockBuyScore table source price best - stock * price →
    value ≤ Znth stock (Znth day table []) 0 →
    StockBuyCellValue ask bid buy sell table max_stock day source stock
      (Znth stock (Znth day table []) 0) := by
  intro ask bid buy sell table max_stock wait day source stock queue price buy_cap head tail best value hp hs hq hht hbest hcap hprice hvalue hcompare
  rcases hp with ⟨hd,hday,hsource,hsr,hstock,hbuy,hsell⟩
  have hsellv := hsell stock (by omega)
  have hrowlen := hd.1.2 source (by omega)
  rcases hq with ⟨hb,hv,hm,hc⟩
  subst best
  refine ⟨⟨⟨0,Or.inl ⟨rfl,hsellv⟩⟩,?_⟩,⟨_,hsellv⟩⟩
  intro amount candidate hcan
  rcases hcan with ⟨_,hsc⟩ | ⟨ha,has,hn,he⟩
  · obtain ⟨sa,hsa⟩ := hsc.1
    have hh := hsellv.2 sa candidate hsa
    omega
  · obtain ⟨pos,hpos,_,hscore⟩ := hc (stock-amount) ⟨by omega,by omega,hn,by omega⟩
    have hheadscore : StockBuyScore table source price (Znth pos queue 0) ≤ StockBuyScore table source price (Znth head queue 0) := by
      by_cases he : pos = head
      · subst pos; omega
      · have h := (hm head pos (by omega)).2; omega
    unfold StockBuyScore at hscore hheadscore hvalue
    rw [Int.sub_mul] at hscore
    rw [← hprice] at he
    omega

theorem StockDaysDone_lookup_portfolio__buy_semantics :
  ∀ ask bid buy sell table max_stock wait next_day day stock,
    StockDaysDone ask bid buy sell table max_stock wait next_day →
    (0 ≤ day ∧ day < next_day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockPortfolioValue ask bid buy sell max_stock wait day stock
      (Znth stock (Znth day table []) 0) := by
  intro ask bid buy sell table max_stock wait next_day day stock hd hr hs
  exact hd.2.2.2 day stock hr hs

theorem StockPortfolioValue_dominates__buy_semantics :
  ∀ ask bid buy sell max_stock wait day stock value profit,
    StockPortfolioValue ask bid buy sell max_stock wait day stock value →
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit →
    profit ≤ value := by
  intro ask bid buy sell max_stock wait day stock value profit hv hf
  rcases hv.2 with ⟨_,hn⟩ | ⟨_,hm⟩
  · exact False.elim (hn ⟨profit,hf⟩)
  · exact hm profit hf

theorem StockPortfolioValue_finite__buy_semantics :
  ∀ ask bid buy sell max_stock wait day stock value,
    StockPortfolioValue ask bid buy sell max_stock wait day stock value →
    value ≠ STOCK_NEG_INF →
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock value := by
  intro ask bid buy sell max_stock wait day stock value hv hn
  rcases hv.2 with ⟨he,_⟩ | ⟨hf,_⟩
  · exact False.elim (hn he)
  · exact hf

theorem StockTradingHistory_stock_bounded__buy_semantics :
  ∀ ask bid buy sell max_stock wait day stock profit,
    StockTradingHistory ask bid buy sell max_stock wait day stock profit →
    (0 ≤ stock ∧ stock ≤ max_stock)  := by
  intro ask bid buy sell max_stock wait day stock profit hh
  induction hh <;> omega

theorem StockTradingHistory_profit_range__buy_semantics :
  ∀ ask bid buy sell days max_stock wait day stock profit,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    day ≤ days →
    StockTradingHistory ask bid buy sell max_stock wait day stock profit →
    (STOCK_NEG_INF < profit ∧ profit < STOCK_MAX_PROFIT)  := by
  intro ask bid buy sell days max_stock wait day stock profit hi hw hday hh
  have hbound := stock_trading_history_profit_bound__sell_cell_progress ask bid buy sell max_stock wait day stock profit days hi hw hday hh
  have hm := hi.2.2.2.2.2.1
  have hd := hi.2.2.2.2.1
  have hprod : day*max_stock ≤ 990*990 := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
  unfold STOCK_NEG_INF STOCK_MAX_PROFIT
  omega

theorem StockFeasiblePortfolio_profit_range__buy_semantics :
  ∀ ask bid buy sell days max_stock wait horizon stock profit,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    horizon ≤ days →
    StockFeasiblePortfolio ask bid buy sell max_stock wait horizon stock profit →
    (STOCK_NEG_INF < profit ∧ profit < STOCK_MAX_PROFIT)  := by
  intro ask bid buy sell days max_stock wait horizon stock profit hi hw hh hf
  rcases hf with ⟨_,hp⟩ | ⟨last,hl,hist⟩
  · subst profit
    unfold STOCK_NEG_INF STOCK_MAX_PROFIT; omega
  · exact StockTradingHistory_profit_range__buy_semantics ask bid buy sell days max_stock wait last stock profit hi hw (by omega) hist

theorem StockFeasiblePortfolio_mono_horizon__buy_semantics :
  ∀ ask bid buy sell max_stock wait h1 h2 stock profit,
    h1 ≤ h2 →
    StockFeasiblePortfolio ask bid buy sell max_stock wait h1 stock profit →
    StockFeasiblePortfolio ask bid buy sell max_stock wait h2 stock profit := by
  intro ask bid buy sell max_stock wait h1 h2 stock profit he hf
  rcases hf with hz | ⟨last,hl,hh⟩
  · exact Or.inl hz
  · exact Or.inr ⟨last,by omega,hh⟩

theorem StockSellCellValue_sound__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    1 ≤ day →
    day ≤ days →
    source = day - wait - 1 →
    (0 < source ∧ source < day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockDaysDone ask bid buy sell table max_stock wait day →
    StockSellCellValue bid sell table max_stock day source stock value →
    value = STOCK_NEG_INF ∨
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock value := by
  intro ask bid buy sell table days max_stock wait day source stock value hi hw hdaypos hday hsource hsr hs hd hc
  obtain ⟨amount,ha⟩ := hc.1
  rcases ha with ⟨_,hv⟩ | ⟨ha,hsm,hn,hv⟩
  · have hp := hd.2.2.2 (day-1) stock (by omega) hs
    rcases hp.2 with ⟨he,_⟩ | ⟨hf,_⟩
    · exact Or.inl (hv.trans he)
    · rw [hv]
      exact Or.inr (StockFeasiblePortfolio_mono_horizon__buy_semantics ask bid buy sell max_stock wait (day-1) day stock _ (by omega) hf)
  · have hp := hd.2.2.2 source (stock+amount) (by omega) (by omega)
    have hf := StockPortfolioValue_finite__buy_semantics ask bid buy sell max_stock wait source (stock+amount) _ hp hn
    rcases hf with ⟨hz,_⟩ | ⟨last,hl,hh⟩
    · omega
    · refine Or.inr (Or.inr ⟨day,by omega,?_⟩)
      rw [hv]
      have hhnew := StockTradingHistory_sell ask bid buy sell max_stock wait last (stock+amount) _ day amount hh (by omega) ha (by omega)
      simpa only [Int.add_sub_cancel] using hhnew

theorem StockSellCellValue_dominates_old__buy_semantics :
  ∀ ask bid buy sell table max_stock wait day source stock value profit,
    1 ≤ day →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockDaysDone ask bid buy sell table max_stock wait day →
    StockSellCellValue bid sell table max_stock day source stock value →
    StockFeasiblePortfolio ask bid buy sell max_stock wait (day - 1)
      stock profit →
    profit ≤ value := by
  intro ask bid buy sell table max_stock wait day source stock value profit hdpos hs hd hc hf
  have hp := hd.2.2.2 (day-1) stock (by omega) hs
  have hdom := StockPortfolioValue_dominates__buy_semantics ask bid buy sell max_stock wait (day-1) stock _ profit hp hf
  have hmax := hc.2 0 (Znth stock (Znth (day-1) table []) 0) (Or.inl ⟨rfl,rfl⟩)
  omega

theorem StockSellCellValue_dominates_sell__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value
         previous_day previous_stock previous_profit amount profit,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    day ≤ days →
    source = day - wait - 1 →
    (0 < source ∧ source < day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockDaysDone ask bid buy sell table max_stock wait day →
    StockSellCellValue bid sell table max_stock day source stock value →
    StockTradingHistory ask bid buy sell max_stock wait
      previous_day previous_stock previous_profit →
    previous_day + wait < day →
    (1 ≤ amount ∧ amount ≤ Znth (day - 1) sell 0) →
    amount ≤ previous_stock →
    stock = previous_stock - amount →
    profit = previous_profit + amount * Znth (day - 1) bid 0 →
    profit ≤ value := by
  intro ask bid buy sell table days max_stock wait day source stock value pd ps pp amount profit hi hw hday hsource hsr hs hd hc hh hgap ha hamt hstock hprofit
  have hps := StockTradingHistory_stock_bounded__buy_semantics ask bid buy sell max_stock wait pd ps pp hh
  have hpd := stock_trading_history_day_positive__init_copy ask bid buy sell max_stock wait pd ps pp hw hh
  have hf : StockFeasiblePortfolio ask bid buy sell max_stock wait source ps pp := Or.inr ⟨pd,by omega,hh⟩
  have hp := hd.2.2.2 source ps (by omega) hps
  have hdom := StockPortfolioValue_dominates__buy_semantics ask bid buy sell max_stock wait source ps _ pp hp hf
  have hfinite : Znth ps (Znth source table []) 0 ≠ STOCK_NEG_INF := by
    intro he
    rcases hp.2 with ⟨_,hn⟩ | ⟨hself,_⟩
    · exact hn ⟨pp,hf⟩
    · have hr := StockFeasiblePortfolio_profit_range__buy_semantics ask bid buy sell days max_stock wait source ps _ hi hw (by omega) hself
      omega
  have hcan : StockSellCandidate bid sell table max_stock day source stock amount (Znth ps (Znth source table []) 0 + amount*Znth (day-1) bid 0) := by
    have he : stock+amount = ps := by omega
    refine Or.inr ⟨ha,by omega,?_,?_⟩
    · rw [he]; exact hfinite
    · rw [he]
  have hmax := hc.2 amount _ hcan
  omega

theorem StockPortfolioValue_finite_if_feasible__buy_semantics :
  ∀ ask bid buy sell days max_stock wait horizon stock value profit,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    horizon ≤ days →
    StockPortfolioValue ask bid buy sell max_stock wait horizon stock value →
    StockFeasiblePortfolio ask bid buy sell max_stock wait horizon stock profit →
    value ≠ STOCK_NEG_INF := by
  intro ask bid buy sell days max_stock wait horizon stock value profit hi hw hh hv hf he
  rcases hv.2 with ⟨_,hn⟩ | ⟨hself,_⟩
  · exact hn ⟨profit,hf⟩
  · have hr := StockFeasiblePortfolio_profit_range__buy_semantics ask bid buy sell days max_stock wait horizon stock value hi hw hh hself
    omega

theorem StockBuyCellValue_sound__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    1 ≤ day →
    day ≤ days →
    source = day - wait - 1 →
    (0 < source ∧ source < day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockDaysDone ask bid buy sell table max_stock wait day →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value →
    value = STOCK_NEG_INF ∨
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock value := by
  intro ask bid buy sell table days max_stock wait day source stock value hi hw hdaypos hday hsource hsr hs hd hc
  obtain ⟨amount,ha⟩ := hc.1.1
  rcases ha with ⟨_,hsell⟩ | ⟨ha,hamt,hn,hv⟩
  · exact StockSellCellValue_sound__buy_semantics ask bid buy sell table days max_stock wait day source stock value hi hw hdaypos hday hsource hsr hs hd hsell
  · have hp := hd.2.2.2 source (stock-amount) (by omega) (by omega)
    have hf := StockPortfolioValue_finite__buy_semantics ask bid buy sell max_stock wait source (stock-amount) _ hp hn
    refine Or.inr (Or.inr ⟨day,by omega,?_⟩)
    rw [hv]
    rcases hf with ⟨hz,hp⟩ | ⟨last,hl,hh⟩
    · rw [hp]
      have he : stock = amount := by omega
      rw [he]
      simpa only [Int.zero_sub,Int.neg_mul] using StockTradingHistory_first_buy ask bid buy sell max_stock wait day amount hdaypos ha (by omega)
    · have hhnew := StockTradingHistory_buy ask bid buy sell max_stock wait last (stock-amount) _ day amount hh (by omega) ha (by omega)
      simpa only [Int.sub_add_cancel] using hhnew

theorem StockBuyCellValue_dominates_feasible__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value profit,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    1 ≤ day →
    day ≤ days →
    source = day - wait - 1 →
    (0 < source ∧ source < day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockDaysDone ask bid buy sell table max_stock wait day →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value →
    StockFeasiblePortfolio ask bid buy sell max_stock wait day stock profit →
    profit ≤ value := by
  intro ask bid buy sell table days max_stock wait day source stock value profit hi hw hdaypos hday hsource hsr hs hd hc hf
  rcases hc with ⟨⟨hach,hmax⟩,⟨zero,hsell⟩⟩
  have hold (p : Int) (hf : StockFeasiblePortfolio ask bid buy sell max_stock wait (day-1) stock p) : p ≤ value := by
    have h0 := StockSellCellValue_dominates_old__buy_semantics ask bid buy sell table max_stock wait day source stock zero p hdaypos hs hd hsell hf
    have hm := hmax 0 zero (Or.inl ⟨rfl,hsell⟩)
    omega
  rcases hf with hz | ⟨last,hl,hh⟩
  · exact hold profit (Or.inl hz)
  · by_cases he : last < day
    · exact hold profit (Or.inr ⟨last,by omega,hh⟩)
    · have heq : last = day := by omega
      subst last
      cases hh with
      | StockTradingHistory_first_buy day stock ha1 ha ham =>
        have hzero : StockFeasiblePortfolio ask bid buy sell max_stock wait source 0 0 := Or.inl ⟨rfl,rfl⟩
        have hp := hd.2.2.2 source 0 (by omega) (by omega)
        have hdom := StockPortfolioValue_dominates__buy_semantics ask bid buy sell max_stock wait source 0 _ 0 hp hzero
        have hn := StockPortfolioValue_finite_if_feasible__buy_semantics ask bid buy sell days max_stock wait source 0 _ 0 hi hw (by omega) hp hzero
        have hc : StockBuyCandidate ask bid buy sell table max_stock day source stock stock (Znth 0 (Znth source table []) 0 - stock*Znth (day-1) ask 0) := by
          refine Or.inr ⟨ha,by omega,?_,?_⟩
          · simpa only [Int.sub_self] using hn
          · simp only [Int.sub_self]
        have hm := hmax stock _ hc
        simp only [Int.neg_mul]
        omega
      | StockTradingHistory_buy pd ps pp day amount hh hgap ha ham =>
        have hps := StockTradingHistory_stock_bounded__buy_semantics ask bid buy sell max_stock wait pd ps pp hh
        have hpd := stock_trading_history_day_positive__init_copy ask bid buy sell max_stock wait pd ps pp hw hh
        have hf : StockFeasiblePortfolio ask bid buy sell max_stock wait source ps pp := Or.inr ⟨pd,by omega,hh⟩
        have hp := hd.2.2.2 source ps (by omega) hps
        have hdom := StockPortfolioValue_dominates__buy_semantics ask bid buy sell max_stock wait source ps _ pp hp hf
        have hn := StockPortfolioValue_finite_if_feasible__buy_semantics ask bid buy sell days max_stock wait source ps _ pp hi hw (by omega) hp hf
        have hc : StockBuyCandidate ask bid buy sell table max_stock day source (ps+amount) amount (Znth ps (Znth source table []) 0 - amount*Znth (day-1) ask 0) := by
          refine Or.inr ⟨ha,by omega,?_,?_⟩
          · simpa only [Int.add_sub_cancel] using hn
          · simp only [Int.add_sub_cancel]
        have hm := hmax amount _ hc
        omega
      | StockTradingHistory_sell pd ps pp day amount hh hgap ha ham =>
        have h0 := StockSellCellValue_dominates_sell__buy_semantics ask bid buy sell table days max_stock wait day source (ps-amount) zero pd ps pp amount (pp+amount*Znth (day-1) bid 0) hi hw hday hsource hsr hs hd hsell hh hgap ha ham rfl rfl
        have hm := hmax 0 zero (Or.inl ⟨rfl,hsell⟩)
        omega

theorem StockBuyCellValue_to_StockPortfolioValue__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    1 ≤ day →
    day ≤ days →
    source = day - wait - 1 →
    (0 < source ∧ source < day) →
    (0 ≤ stock ∧ stock ≤ max_stock) →
    StockDaysDone ask bid buy sell table max_stock wait day →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value →
    StockPortfolioValue ask bid buy sell max_stock wait day stock value := by
  intro ask bid buy sell table days max_stock wait day source stock value hi hw hdaypos hday hsource hsr hs hd hc
  have hsound := StockBuyCellValue_sound__buy_semantics ask bid buy sell table days max_stock wait day source stock value hi hw hdaypos hday hsource hsr hs hd hc
  refine ⟨hs,?_⟩
  rcases hsound with hneg | hf
  · refine Or.inl ⟨hneg,?_⟩
    rintro ⟨profit,hf⟩
    have hdom := StockBuyCellValue_dominates_feasible__buy_semantics ask bid buy sell table days max_stock wait day source stock value profit hi hw hdaypos hday hsource hsr hs hd hc hf
    have hr := StockFeasiblePortfolio_profit_range__buy_semantics ask bid buy sell days max_stock wait day stock profit hi hw hday hf
    omega
  · exact Or.inr ⟨hf,fun profit hp => StockBuyCellValue_dominates_feasible__buy_semantics ask bid buy sell table days max_stock wait day source stock value profit hi hw hdaypos hday hsource hsr hs hd hc hp⟩

theorem StockBuyProgress_complete_day__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source next_stock,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    day ≤ days →
    max_stock < next_stock →
    StockBuyProgress ask bid buy sell table max_stock wait day source next_stock →
    StockDaysDone ask bid buy sell table max_stock wait (day + 1) := by
  intro ask bid buy sell table days max_stock wait day source next_stock hi hw hday hcomp hp
  rcases hp with ⟨hd,hdayrange,hsource,hsr,hn,hbuy,hsell⟩
  refine ⟨hd.1,hd.2.1,by omega,?_⟩
  intro d stock hdr hs
  by_cases he : d < day
  · exact hd.2.2.2 d stock (by omega) hs
  · have heq : d = day := by omega
    subst d
    exact StockBuyCellValue_to_StockPortfolioValue__buy_semantics ask bid buy sell table days max_stock wait day source stock _ hi hw hdayrange.1 hday hsource hsr hs hd (hbuy stock (by omega))

theorem StockSellCellValue_replace_current_row__buy_semantics :
  ∀ bid sell table max_stock day source stock value col replacement days,
    StockTableShape table days max_stock →
    (0 ≤ day ∧ day < days + 1) →
    (0 ≤ source ∧ source < days + 1) →
    (0 ≤ day - 1 ∧ day - 1 < days + 1) →
    (0 ≤ col ∧ col < max_stock + 1) →
    source ≠ day →
    day - 1 ≠ day →
    StockSellCellValue bid sell table max_stock day source stock value →
    let row' := replace_Znth col replacement (Znth day table []) ;
    let table' := replace_Znth day row' table ;
    StockSellCellValue bid sell table' max_stock day source stock value := by
  intro bid sell table max_stock day source stock value col replacement days hshape hday hsource hpidx hcol hs hp hc
  dsimp only
  unfold StockSellCellValue StockSellCandidate at *
  rw [Znth_replace_Znth_Diff [] table day source _ (by rw [hshape.1]; exact hday) (by rw [hshape.1]; exact hsource) (Ne.symm hs),Znth_replace_Znth_Diff [] table day (day-1) _ (by rw [hshape.1]; exact hday) (by rw [hshape.1]; exact hpidx) (Ne.symm hp)]
  exact hc

theorem StockBuyCellValue_replace_current_row__buy_semantics :
  ∀ ask bid buy sell table max_stock day source stock value col replacement days,
    StockTableShape table days max_stock →
    (0 ≤ day ∧ day < days + 1) →
    (0 ≤ source ∧ source < days + 1) →
    (0 ≤ day - 1 ∧ day - 1 < days + 1) →
    (0 ≤ col ∧ col < max_stock + 1) →
    source ≠ day →
    day - 1 ≠ day →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value →
    let row' := replace_Znth col replacement (Znth day table []) ;
    let table' := replace_Znth day row' table ;
    StockBuyCellValue ask bid buy sell table' max_stock day source stock value := by
  intro ask bid buy sell table max_stock day source stock value col replacement days hshape hday hsource hpidx hcol hs hp hc
  dsimp only
  unfold StockBuyCellValue StockBuyCandidate StockSellCellValue StockSellCandidate at *
  rw [Znth_replace_Znth_Diff [] table day source _ (by rw [hshape.1]; exact hday) (by rw [hshape.1]; exact hsource) (Ne.symm hs),Znth_replace_Znth_Diff [] table day (day-1) _ (by rw [hshape.1]; exact hday) (by rw [hshape.1]; exact hpidx) (Ne.symm hp)]
  exact hc

theorem StockBuyProgress_replace_step__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock →
    StockTableShape table days max_stock →
    StockBuyProgress ask bid buy sell table max_stock wait day source stock →
    stock ≤ max_stock →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value →
    (STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT) →
    let row' := replace_Znth stock value (Znth day table []) ;
    let table' := replace_Znth day row' table ;
    StockBuyProgress ask bid buy sell table' max_stock wait day source (stock + 1) ∧
    StockTableShape table' days max_stock := by
  intro ask bid buy sell table days max_stock wait day source stock value hi hshape hp hs hc hv
  rcases hp with ⟨hd,hday,hsource,hsr,hsrange,hbuy,hsell⟩
  have hdayidx : 0 ≤ day ∧ day < days+1 := by rw [← hi.1]; omega
  have hrowidx : 0 ≤ day ∧ day < Zlength table := by rw [hshape.1]; exact hdayidx
  have hsourceidx : 0 ≤ source ∧ source < days+1 := by omega
  have hprevidx : 0 ≤ day-1 ∧ day-1 < days+1 := by omega
  have hstockidx : 0 ≤ stock ∧ stock < max_stock+1 := by omega
  have hrowlen := hshape.2 day hdayidx
  have hnewlen : Zlength (replace_Znth stock value (Znth day table [])) = max_stock+1 := by rw [Zlength_replace_Znth]; exact hrowlen
  have hdayask : 0 ≤ day ∧ day < Zlength ask+1 := by omega
  have hbound := row_bounded_replace (Znth day table []) max_stock stock value hrowlen hstockidx hv (hd.2.1 day · hdayask)
  have hdone := days_done_replace ask bid buy sell table max_stock wait day day _ hd hdayask (by omega) hnewlen hbound
  have hshape' := table_shape_replace table days max_stock day _ hshape hdayidx hnewlen
  have hrow := Znth_replace_Znth_Same ([] : List Int) table day (replace_Znth stock value (Znth day table [])) hrowidx
  dsimp only
  refine ⟨⟨hdone,hday,hsource,hsr,by omega,?_,?_⟩,hshape'⟩
  · intro k hk
    rw [hrow]
    by_cases he : k < stock
    · rw [Znth_replace_Znth_Diff 0 (Znth day table []) stock k value (by omega) (by omega) (by omega)]
      exact StockBuyCellValue_replace_current_row__buy_semantics ask bid buy sell table max_stock day source k _ stock value days hshape hdayidx hsourceidx hprevidx hstockidx (by omega) (by omega) (hbuy k (by omega))
    · have heq : k = stock := by omega
      subst k
      rw [Znth_replace_Znth_Same 0 (Znth day table []) stock value (by omega)]
      exact StockBuyCellValue_replace_current_row__buy_semantics ask bid buy sell table max_stock day source stock value stock value days hshape hdayidx hsourceidx hprevidx hstockidx (by omega) (by omega) hc
  · intro k hk
    rw [hrow,Znth_replace_Znth_Diff 0 (Znth day table []) stock k value (by omega) (by omega) (by omega)]
    exact StockSellCellValue_replace_current_row__buy_semantics bid sell table max_stock day source k _ stock value days hshape hdayidx hsourceidx hprevidx hstockidx (by omega) (by omega) (hsell k (by omega))

theorem StockBuyProgress_replace_improved_step__buy_semantics :
  ∀ ask bid buy sell table days max_stock wait day source stock value,
    StockInputsBounded ask bid buy sell days max_stock →
    0 ≤ wait →
    StockTableShape table days max_stock →
    StockBuyProgress ask bid buy sell table max_stock wait day source stock →
    stock ≤ max_stock →
    Znth stock (Znth day table []) 0 < value →
    StockBuyCellValue ask bid buy sell table max_stock day source stock value →
    let row' := replace_Znth stock value (Znth day table []) ;
    let table' := replace_Znth day row' table ;
    StockBuyProgress ask bid buy sell table' max_stock wait day source (stock + 1) ∧
    StockTableShape table' days max_stock := by
  intro ask bid buy sell table days max_stock wait day source stock value hi hw hshape hp hs himp hc
  have hday := hp.2.1
  have hsource := hp.2.2.1
  have hsr := hp.2.2.2.1
  have hsrange := hp.2.2.2.2.1
  have hdaydays : day ≤ days := by rw [← hi.1]; omega
  have hold := StockDaysDone_cell_bounded__safety_buy ask bid buy sell table days max_stock wait day day stock [] hi hp.1 hshape (by omega) (by omega)
  have hsound := StockBuyCellValue_sound__buy_semantics ask bid buy sell table days max_stock wait day source stock value hi hw hday.1 hdaydays hsource hsr (by omega) hp.1 hc
  have hv : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT := by
    rcases hsound with hn | hf
    · omega
    · have hr := StockFeasiblePortfolio_profit_range__buy_semantics ask bid buy sell days max_stock wait day stock value hi hw hdaydays hf
      omega
  exact StockBuyProgress_replace_step__buy_semantics ask bid buy sell table days max_stock wait day source stock value hi hshape hp hs hc hv

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib

namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading
export stock_trading_lib (_List_Z StockTradingHistory_first_buy StockTradingHistory_buy StockTradingHistory_sell STOCK_NEG_INF STOCK_MAX_PROFIT StockInitialCell StockTableShape StockTableValuesBounded StockInputsBounded StockTradingHistory StockFeasiblePortfolio StockPortfolioValue StockMaximumProfit StockFillRows StockFillCells StockDaysDone StockCopyProgress StockEarlyBuyProgress StockSellScore StockBuyScore StockFiniteTableIndex StockFiniteIndexInWindow StockSellQueue StockSellQueueExpiring StockSellQueuePopping StockSellQueuePending StockBuyQueue StockBuyQueueExpiring StockBuyQueuePopping StockBuyQueuePending StockSellCandidate StockSellCellValue StockBuyCandidate StockBuyCellValue StockSellProgress StockBuyProgress StockAnswerProgress)
end SimpleC.EE.LLM_bench.Algorithms.stock_trading

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
open AUXLib

abbrev StockRowLength : List Int → Int := Zlength

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.stock_trading_lib
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading
export stock_trading_lib (StockRowLength)
end SimpleC.EE.LLM_bench.Algorithms.stock_trading

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
namespace SimpleC.EE.LLM_bench.Algorithms.stock_trading.StockProofInternal
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2

theorem merge_cell (p n m r c v : Int) (rows : List (List Int)) (d : List Int)
    (hr : 0 ≤ r ∧ r < n) (hc : 0 ≤ c ∧ c < m) :
    (((p+(r*m+c)*sizeof(INT)) # Int |-> v) **
     intArray.missing_i (p+r*m*sizeof(INT)) c 0 m (Znth r rows d) **
     SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i p r 0 n m rows |--
     SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full p n m (replace_Znth r (replace_Znth c v (Znth r rows d)) rows)) := by
  have haddr : p+r*m*sizeof(INT)+c*sizeof(INT) = p+(r*m+c)*sizeof(INT) := by
    simp only [Int.add_mul]; omega
  rw [← haddr]
  have hrow : (((p+r*m*sizeof(INT)+c*sizeof(INT)) # Int |-> v) **
      intArray.missing_i (p+r*m*sizeof(INT)) c 0 m (Znth r rows d) |--
      intArray.full (p+r*m*sizeof(INT)) m (replace_Znth c v (Znth r rows d))) :=
    intArray.missing_i_merge_to_full (p+r*m*sizeof(INT)) c m v (Znth r rows d) hc
  sep_apply hrow
  have htable : (intArray.full (p+r*m*sizeof(INT)) m (replace_Znth c v (Znth r rows d)) **
      SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i p r 0 n m rows |--
      SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full p n m (replace_Znth r (replace_Znth c v (Znth r rows d)) rows)) :=
    intArray2.missing_i_merge_to_full p r n m rows (replace_Znth c v (Znth r rows d)) hr
  sep_apply htable
  cancel

theorem restore_cell (p n m r c : Int) (rows : List (List Int)) (d : List Int)
    (hr : 0 ≤ r ∧ r < n) (hc : 0 ≤ c ∧ c < m) :
    (((p+(r*m+c)*sizeof(INT)) # Int |-> Znth c (Znth r rows d) 0) **
     intArray.missing_i (p+r*m*sizeof(INT)) c 0 m (Znth r rows d) **
     SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.missing_i p r 0 n m rows |-- SimpleC.SL.SeparationLogic.naive_C_Rules.IntArray2.full p n m rows) := by
  sep_apply (merge_cell p n m r c (Znth c (Znth r rows d) 0) rows d hr hc)
  simp only [replace_Znth_Znth]
  cancel

open stock_trading_lib
private theorem table_shape_replace (table : List (List Int)) (days max_stock row : Int)
    (newrow : List Int) (hs : StockTableShape table days max_stock)
    (hr : 0 ≤ row ∧ row < days+1) (hl : Zlength newrow = max_stock+1) :
    StockTableShape (replace_Znth row newrow table) days max_stock := by
  refine ⟨?_,?_⟩
  · rw [Zlength_replace_Znth]; exact hs.1
  · intro r h
    by_cases he : r = row
    · subst r; rw [Znth_replace_Znth_Same [] table row newrow (by rw [hs.1]; exact hr)]; exact hl
    · rw [Znth_replace_Znth_Diff [] table row r newrow (by rw [hs.1]; exact hr) (by rw [hs.1]; exact h) (Ne.symm he)]
      exact hs.2 r h

private theorem table_bounded_replace (table : List (List Int)) (days max_stock row : Int)
    (newrow : List Int) (hs : StockTableShape table days max_stock)
    (hb : StockTableValuesBounded table days max_stock)
    (hr : 0 ≤ row ∧ row < days+1)
    (hn : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock newrow 0 ∧ Znth stock newrow 0 ≤ STOCK_MAX_PROFIT) :
    StockTableValuesBounded (replace_Znth row newrow table) days max_stock := by
  intro r stock h hk
  by_cases he : r = row
  · subst r; rw [Znth_replace_Znth_Same [] table row newrow (by rw [hs.1]; exact hr)]; exact hn stock hk
  · rw [Znth_replace_Znth_Diff [] table row r newrow (by rw [hs.1]; exact hr) (by rw [hs.1]; exact h) (Ne.symm he)]
    exact hb r stock h hk

private theorem row_bounded_replace (row : List Int) (max_stock col value : Int)
    (hl : Zlength row = max_stock+1)
    (hc : 0 ≤ col ∧ col < max_stock+1)
    (hv : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT)
    (hb : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock row 0 ∧ Znth stock row 0 ≤ STOCK_MAX_PROFIT) :
    ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock (replace_Znth col value row) 0 ∧ Znth stock (replace_Znth col value row) 0 ≤ STOCK_MAX_PROFIT := by
  intro stock hs
  by_cases he : stock = col
  · subst stock; rw [Znth_replace_Znth_Same 0 row col value (by omega)]; exact hv
  · rw [Znth_replace_Znth_Diff 0 row col stock value (by omega) (by omega) (Ne.symm he)]
    exact hb stock hs

private theorem days_done_replace (ask bid buy sell : List Int) (table : List (List Int))
    (max_stock wait next_day row : Int) (newrow : List Int)
    (hd : StockDaysDone ask bid buy sell table max_stock wait next_day)
    (hr : 0 ≤ row ∧ row < Zlength ask+1) (hnr : next_day ≤ row)
    (hl : Zlength newrow = max_stock+1)
    (hb : ∀ stock, (0 ≤ stock ∧ stock < max_stock+1) → STOCK_NEG_INF ≤ Znth stock newrow 0 ∧ Znth stock newrow 0 ≤ STOCK_MAX_PROFIT) :
    StockDaysDone ask bid buy sell (replace_Znth row newrow table) max_stock wait next_day := by
  refine ⟨table_shape_replace table (Zlength ask) max_stock row newrow hd.1 hr hl,
    table_bounded_replace table (Zlength ask) max_stock row newrow hd.1 hd.2.1 hr hb,hd.2.2.1,?_⟩
  intro day stock hday hs
  rw [Znth_replace_Znth_Diff [] table row day newrow (by rw [hd.1.1]; exact hr) (by rw [hd.1.1]; omega) (by omega)]
  exact hd.2.2.2 day stock hday hs

theorem sell_cell_queue (ask bid buy sell : List Int) (table : List (List Int))
    (days max_stock wait day source stock : Int) (queue : List Int)
    (price cap head tail best value : Int)
    (hi : StockInputsBounded ask bid buy sell days max_stock)
    (hp : StockSellProgress ask bid buy sell table max_stock wait day source stock)
    (hstock : 0 ≤ stock ∧ stock < max_stock)
    (hq : StockSellQueue table queue source price (stock+1) (stock+cap) head tail)
    (hht : head < tail) (hbest : best = Znth head queue 0)
    (hprice : price = Znth (day-1) bid 0) (hcap : cap = Znth (day-1) sell 0)
    (hv : value = StockSellScore table source price best - stock*price) :
    StockSellCellValue bid sell table max_stock day source stock
      (max (Znth stock (Znth day table []) 0) value) := by
  have hcopy := hp.2.2.2.2.2.1 stock (by omega)
  have hday := hp.2.1
  have hsrc := hp.2.2.2.1
  have hrow := hp.1.1.2 source (by omega)
  have hentry := hq.2.1 head (by omega)
  rw [← hbest] at hentry
  rcases hentry with ⟨hb0,hbl,hbf,hbr⟩
  have hcandidate : StockSellCandidate bid sell table max_stock day source stock (best-stock) value := by
    right
    refine ⟨by omega,by omega,?_,?_⟩
    · simpa only [show stock+(best-stock)=best by omega] using hbf
    · rw [show stock+(best-stock)=best by omega, ← hprice]
      simp only [Int.sub_mul]
      unfold StockSellScore at hv
      omega
  refine ⟨?_,?_⟩
  · by_cases he : Znth stock (Znth day table []) 0 ≤ value
    · rw [Int.max_eq_right he]; exact ⟨best-stock,hcandidate⟩
    · rw [Int.max_eq_left (by omega)]
      exact ⟨0,Or.inl ⟨rfl,hcopy⟩⟩
  · intro amount candidate hc
    rcases hc with ⟨ha,hc⟩ | ⟨ha,hb,hn,hc⟩
    · have hm := Int.le_max_left (Znth stock (Znth day table []) 0) value
      omega
    · obtain ⟨pos,hpos,hindex,hscore⟩ := hq.2.2.2 (stock+amount) ⟨by omega,by omega,hn,by omega⟩
      have hhead : StockSellScore table source price (Znth pos queue 0) ≤ StockSellScore table source price best := by
        by_cases he : pos = head
        · subst pos; rw [hbest] <;> omega
        · have hh := (hq.2.2.1 head pos (by omega)).2
          rw [← hbest] at hh
          omega
      have hm := Int.le_max_right (Znth stock (Znth day table []) 0) value
      unfold StockSellScore at hhead hscore hv
      rw [← hprice] at hc
      simp only [Int.add_mul] at hscore
      omega

theorem sell_replace_step (ask bid buy sell : List Int) (table : List (List Int))
    (days max_stock wait day source stock value : Int)
    (hi : StockInputsBounded ask bid buy sell days max_stock) (hw : 0 ≤ wait)
    (hp : StockSellProgress ask bid buy sell table max_stock wait day source stock)
    (hs : 0 ≤ stock ∧ stock < max_stock)
    (hc : StockSellCellValue bid sell table max_stock day source stock value) :
    let row := replace_Znth stock value (Znth day table [])
    let table' := replace_Znth day row table
    StockSellProgress ask bid buy sell table' max_stock wait day source (stock-1) ∧
    StockTableShape table' days max_stock := by
  have hday := hp.2.1
  have hsource := hp.2.2.1
  have hsr := hp.2.2.2.1
  have hdaydays : day ≤ days := by rw [← hi.1]; omega
  have hsound := StockSellCellValue_sound__buy_semantics ask bid buy sell table days max_stock wait day source stock value hi hw hday.1 hdaydays hsource hsr (by omega) hp.1 hc
  have hv : STOCK_NEG_INF ≤ value ∧ value ≤ STOCK_MAX_PROFIT := by
    rcases hsound with he | hf
    · unfold STOCK_NEG_INF STOCK_MAX_PROFIT at *; omega
    · have hr := StockFeasiblePortfolio_profit_range__buy_semantics ask bid buy sell days max_stock wait day stock value hi hw hdaydays hf
      omega
  have hshape := hp.1.1
  have hlen := hshape.1
  have hrow := hshape.2 day (by omega)
  have hnewlen : Zlength (replace_Znth stock value (Znth day table [])) = max_stock+1 := by
    rw [Zlength_replace_Znth]; exact hrow
  have hbound := row_bounded_replace (Znth day table []) max_stock stock value hrow (by omega) hv (hp.1.2.1 day · (by omega))
  have hdone := days_done_replace ask bid buy sell table max_stock wait day day _ hp.1 (by omega) (by omega) hnewlen hbound
  have hprev := Znth_replace_Znth_Diff ([] : List Int) table day (day-1) (replace_Znth stock value (Znth day table [])) (by omega) (by omega) (by omega)
  have hcur := Znth_replace_Znth_Same ([] : List Int) table day (replace_Znth stock value (Znth day table [])) (by omega)
  have hshapeDays : StockTableShape table days max_stock := by rw [← hi.1]; exact hshape
  have hport (k v : Int) (hc' : StockSellCellValue bid sell table max_stock day source k v) :=
    StockSellCellValue_replace_current_row__buy_semantics bid sell table max_stock day source k v stock value days hshapeDays (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hc'
  dsimp only
  refine ⟨⟨hdone,hday,hsource,hsr,by omega,?_,?_,?_⟩,?_⟩
  · intro k hk
    rw [hcur,Znth_replace_Znth_Diff 0 (Znth day table []) stock k value (by omega) (by omega) (by omega),hprev]
    exact hp.2.2.2.2.2.1 k (by omega)
  · intro k hk
    by_cases he : k = stock
    · subst k
      rw [hcur,Znth_replace_Znth_Same 0 (Znth day table []) stock value (by omega)]
      exact hport stock value hc
    · rw [hcur,Znth_replace_Znth_Diff 0 (Znth day table []) stock k value (by omega) (by omega) (by omega)]
      exact hport k _ (hp.2.2.2.2.2.2.1 k (by omega))
  · rw [hcur,Znth_replace_Znth_Diff 0 (Znth day table []) stock max_stock value (by omega) (by omega) (by omega),hprev]
    exact hp.2.2.2.2.2.2.2
  · rw [← hi.1]; exact hdone.1

theorem sell_queue_replace (table : List (List Int)) (queue : List Int)
    (source price lower upper head tail row : Int) (v : List Int)
    (hs : 0 ≤ source ∧ source < Zlength table) (hr : 0 ≤ row ∧ row < Zlength table)
    (hne : source ≠ row) (hq : StockSellQueue table queue source price lower upper head tail) :
    StockSellQueue (replace_Znth row v table) queue source price lower upper head tail := by
  unfold StockSellQueue StockFiniteIndexInWindow StockSellScore at *
  simpa only [Znth_replace_Znth_Diff ([] : List Int) table row source v hr hs (Ne.symm hne)] using hq

end SimpleC.EE.LLM_bench.Algorithms.stock_trading.StockProofInternal
