import AUXLib.NiaCompat

example (b ac : Int) (h : b * b - 4 * ac < 0) : b * b < 4 * ac := by
  nia

example (q n : Int) (hq : q <= 0) (hn : 0 <= n) : q * n <= 0 := by
  nia

example (d q n : Int) (hd : 0 <= d) (hdq : d <= q) (hdn : d <= n) :
    d * d <= q * n := by
  nia

example (a y bound : Int) (ha : 0 <= a) (hy : 0 <= y) (hy1 : y <= 1)
    (habound : a <= bound) : a * y <= bound := by
  nia

-- Exact nonlinear shapes used by the square-root prime loop.
example (d x : Int) (hsquare : d * d <= x) (_hd : 2 <= d)
    (hx : x <= 1000000000) : d + 1 <= 31624 := by
  nia

example (d x : Int) (hsquare : d * d <= x) (hd : 2 <= d) : d < x := by
  nia

-- Exact bounded-product shape used by the extended-gcd safety proofs.
example (q y bound : Int) (hq : 0 <= q) (hy : 0 <= y) (hy1 : y <= 1)
    (hqbound : q <= bound) : q * y <= bound := by
  nia

example (a x y : Int) (ha : 0 <= a) (hxy : x <= y) : a * x <= a * y := by
  nia

example (x y : Int) : x * y * 4 = 4 * x * y := by
  nia

-- Like an ordinary Lean tactic, `nia` changes only the current main goal and
-- leaves unrelated sibling goals in their original order.
example (x y : Int) : x * y = y * x ∧ True := by
  constructor
  · nia
  · trivial

example (x y : Int) : x * y = y * x ∧ True := by
  constructor
  try nia
  trivial

-- An unrelated multiplication hypothesis must not activate nonlinear search
-- for a non-arithmetic proposition target.
example (_P : Prop) (x y : Int) (_hmul : x * y = 0) : True := by
  fail_if_success
    have : _P := by nia
  trivial

-- A bounded compatibility tactic must not claim general polynomial reasoning.
set_option linter.unusedVariables false in
example (x y : Int) : True := by
  fail_if_success
    have : 2 * x * y <= x * x + y * y := by
      nia
  trivial
