import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Presuffix

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open AUXLib

abbrev concat {A : Type} (xs : List (List A)) : List A := xs.flatten


def Cell := Int × Int

def AdjCell (p q : Cell) : Prop :=
  Z.abs (Prod.fst p - Prod.fst q) + Z.abs (Prod.snd p - Prod.snd q) = 1

def SameColorPath (g : List (List Int)) (p q : Cell) : Prop :=
  exists path : List Cell, path ≠ [] ∧ Znth 0 path (0, 0) = p ∧ Znth (Zlength path - 1) path (0, 0) = q ∧
  Forall (fun x => (0 ≤ Prod.fst x ∧ Prod.fst x < Zlength g) ∧ (0 ≤ Prod.snd x ∧ Prod.snd x < Zlength (Znth 0 g [])) ∧
    Znth (Prod.snd x) (Znth (Prod.fst x) g []) 0 = Znth (Prod.snd p) (Znth (Prod.fst p) g []) 0) path ∧
  forall i, (0 ≤ i ∧ i < Zlength path - 1) → AdjCell (Znth i path (0, 0)) (Znth (i + 1) path (0, 0))

def SquareTiling (n m : Int) (g : List (List Int)) : Prop :=
  (Zlength g = n ∧ Forall (fun row => Zlength row = m) g) ∧ Forall (Forall (fun c => (65 ≤ c ∧ c ≤ 90) )) g ∧
  forall p, (0 ≤ Prod.fst p ∧ Prod.fst p < n) → (0 ≤ Prod.snd p ∧ Prod.snd p < m) → exists r c side,
    side ≥ 1 ∧ (r ≤ Prod.fst p ∧ Prod.fst p < r + side) ∧ (c ≤ Prod.snd p ∧ Prod.snd p < c + side) ∧ r ≥ 0 ∧ c ≥ 0 ∧ r + side ≤ n ∧ c + side ≤ m ∧
    forall q, (0 ≤ Prod.fst q ∧ Prod.fst q < n) → (0 ≤ Prod.snd q ∧ Prod.snd q < m) →
      (SameColorPath g p q ↔ (r ≤ Prod.fst q ∧ Prod.fst q < r + side) ∧ (c ≤ Prod.snd q ∧ Prod.snd q < c + side) )

def Flatten (g : List (List Int)) : List Int := List.flatten g

def Pre (n m : Int) : Prop :=

  True

def Spec (n m : Int) (out : List (List Int)) : Prop :=
  SquareTiling n m out ∧ forall q, SquareTiling n m q → ((Flatten out) = (Flatten q) ∨ ((exists i, (0 ≤ i ∧ i < min (Zlength (Flatten out)) (Zlength (Flatten q))) ∧
    (forall j, (0 ≤ j ∧ j < i) → Znth j (Flatten out) 0 = Znth j (Flatten q) 0) ∧
    Znth i (Flatten out) 0 < Znth i (Flatten q) 0) ∨
  (Zlength (Flatten out) < Zlength (Flatten q) ∧ ListLib.is_prefix (Flatten out) (Flatten q))))

def NeighborConflict
    (flat : List Int) (n m i j c left_override : Int) : Prop :=
  (0 < i ∧ Znth ((i - 1) * m + j) flat 0 = c) ∨
  (i + 1 < n ∧ Znth ((i + 1) * m + j) flat 0 = c) ∨
  (j + 1 < m ∧ Znth (i * m + j + 1) flat 0 = c) ∨
  (0 < j ∧
    (if left_override = 0
     then Znth (i * m + j - 1) flat 0
     else left_override) = c) ∨
  (j = 0 ∧ left_override = c)

def LegalColor
    (flat : List Int) (n m i j left_override c : Int) : Prop :=
  (65 ≤ c ∧ c ≤ 90) ∧
  ¬ NeighborConflict flat n m i j c left_override

def LeastLegalColor
    (flat : List Int) (n m i j left_override c : Int) : Prop :=
  LegalColor flat n m i j left_override c ∧
  forall d, (65 ≤ d ∧ d < c) →
    ¬ LegalColor flat n m i j left_override d

def CanPlace
    (flat : List Int) (n m i j side color : Int) : Prop :=
  1 ≤ side ∧ i + side ≤ n ∧ j + side ≤ m ∧
  (forall r q,
      (i ≤ r ∧ r < i + side) → (j ≤ q ∧ q < j + side) →
      Znth (r * m + q) flat 0 = 0) ∧
  (forall q,
      (j ≤ q ∧ q < j + side) →
      (0 < i → Znth ((i - 1) * m + q) flat 0 ≠ color) ∧
      (i + side < n → Znth ((i + side) * m + q) flat 0 ≠ color)) ∧
  (forall r,
      (i ≤ r ∧ r < i + side) →
      (0 < j → Znth (r * m + j - 1) flat 0 ≠ color) ∧
      (j + side < m → Znth (r * m + j + side) flat 0 ≠ color))

def ZeroPrefix (flat : List Int) (upto : Int) : Prop :=
  forall k, (0 ≤ k ∧ k < upto) → Znth k flat 0 = 0

def NoConflictBelow
    (flat : List Int) (n m i j left_override next : Int) : Prop :=
  forall color, (65 ≤ color ∧ color < next) →
    NeighborConflict flat n m i j color left_override

def EmptySquarePrefix
    (flat : List Int) (m i j side done : Int) : Prop :=
  forall off, (0 ≤ off ∧ off < done) →
    Znth ((i + Z.div off side) * m + (j + Z.modulo off side)) flat 0 = 0

def HorizontalBoundaryClearPrefix
    (flat : List Int) (n m i j side color done : Int) : Prop :=
  forall off, (0 ≤ off ∧ off < done) →
    (0 < i → Znth ((i - 1) * m + (j + off)) flat 0 ≠ color) ∧
    (i + side < n → Znth ((i + side) * m + (j + off)) flat 0 ≠ color)

def VerticalBoundaryClearPrefix
    (flat : List Int) (n m i j side color done : Int) : Prop :=
  forall off, (0 ≤ off ∧ off < done) →
    (0 < j → Znth ((i + off) * m + j - 1) flat 0 ≠ color) ∧
    (j + side < m → Znth ((i + off) * m + j + side) flat 0 ≠ color)

def RowsOfFlat (n m : Int) (flat : List Int) (grid : List (List Int)) : Prop :=
  Zlength grid = n ∧
  Forall (fun row => Zlength row = m) grid ∧
  Flatten grid = flat

def LexPrefixLe (upto : Int) (left right : List Int) : Prop :=
  (forall k, (0 ≤ k ∧ k < upto) → Znth k left 0 = Znth k right 0) ∨
  exists first,
    (0 ≤ first ∧ first < upto) ∧
    (forall k, (0 ≤ k ∧ k < first) → Znth k left 0 = Znth k right 0) ∧
    Znth first left 0 < Znth first right 0

def PartialSquareComponents
    (n m : Int) (grid : List (List Int)) : Prop :=
  forall p,
    (0 ≤ Prod.fst p ∧ Prod.fst p < n) → (0 ≤ Prod.snd p ∧ Prod.snd p < m) →
    Znth (Prod.snd p) (Znth (Prod.fst p) grid []) 0 ≠ 0 →
    exists r c side,
      1 ≤ side ∧
      0 ≤ r ∧ 0 ≤ c ∧ r + side ≤ n ∧ c + side ≤ m ∧
      (r ≤ Prod.fst p ∧ Prod.fst p < r + side) ∧ (c ≤ Prod.snd p ∧ Prod.snd p < c + side) ∧
      forall q,
        (0 ≤ Prod.fst q ∧ Prod.fst q < n) → (0 ≤ Prod.snd q ∧ Prod.snd q < m) →
        (SameColorPath grid p q ↔
         (r ≤ Prod.fst q ∧ Prod.fst q < r + side) ∧ (c ≤ Prod.snd q ∧ Prod.snd q < c + side) )

def PartialTilingState
    (n m next : Int) (flat : List Int) : Prop :=
  exists grid,
    RowsOfFlat n m flat grid ∧
    (forall k, (0 ≤ k ∧ k < next) → (65 ≤ Znth k flat 0 ∧ Znth k flat 0 ≤ 90) ) ∧
    (forall k, (0 ≤ k ∧ k < n * m) →
       Znth k flat 0 = 0 ∨ (65 ≤ Znth k flat 0 ∧ Znth k flat 0 ≤ 90) ) ∧
    PartialSquareComponents n m grid ∧
    (forall candidate,
       SquareTiling n m candidate →
       LexPrefixLe next flat (Flatten candidate))

def NoPlaceableColorBelow
    (flat : List Int) (n m i j next : Int) : Prop :=
  forall color, (65 ≤ color ∧ color < next) →
    ¬ CanPlace flat n m i j 1 color

def GreedySideState
    (flat : List Int) (n m i j color side : Int) : Prop :=
  CanPlace flat n m i j side color ∧
  forall previous_side,
    (1 ≤ previous_side ∧ previous_side < side) →
    CanPlace flat n m i j (previous_side + 1) color ∧
    exists fallback,
      LeastLegalColor flat n m i (j + previous_side) color fallback ∧
      color < fallback

def PaintRectanglePrefix
    (before after : List Int) (m i j side color done : Int) : Prop :=
  Zlength after = Zlength before ∧
  forall index,
    (0 ≤ index ∧ index < Zlength before) →
    ((exists off,
        (0 ≤ off ∧ off < done) ∧
        index = (i + Z.div off side) * m + (j + Z.modulo off side)) ∧
      Znth index after 0 = color) ∨
    ((forall off,
        (0 ≤ off ∧ off < done) →
        index ≠ (i + Z.div off side) * m + (j + Z.modulo off side)) ∧
      Znth index after 0 = Znth index before 0)

def CanonicalGrid (flat : List Int) : Prop :=
  forall k, (0 ≤ k ∧ k < Zlength flat) →
    Znth k flat 0 = 0 ∨ (65 ≤ Znth k flat 0 ∧ Znth k flat 0 ≤ 90)

def CommittedFrontierState
    (n m next : Int) (flat : List Int) : Prop :=
  forall upto,
    (next ≤ upto ∧ upto ≤ n * m) →
    (forall k, (next ≤ k ∧ k < upto) → (65 ≤ Znth k flat 0 ∧ Znth k flat 0 ≤ 90) ) →
    PartialTilingState n m upto flat

def ChosenSquareState
    (flat : List Int) (n m i j color side : Int) : Prop :=
  LeastLegalColor flat n m i j 0 color ∧
  GreedySideState flat n m i j color side

def SettledSquareState
    (flat : List Int) (n m i j color side : Int) : Prop :=
  ChosenSquareState flat n m i j color side ∧
  (j + side = m ∨
   ¬ CanPlace flat n m i j (side + 1) color ∨
   exists fallback,
     LeastLegalColor flat n m i (j + side) color fallback ∧
     fallback ≤ color)


inductive GreedyPlacementTrace (n m : Int) : Int → List Int → Prop
  | GreedyTrace_zero : ∀ flat, Zlength flat = n*m → ZeroPrefix flat (n*m) → GreedyPlacementTrace n m 0 flat
  | GreedyTrace_skip : ∀ next flat, GreedyPlacementTrace n m next flat → (0 ≤ next ∧ next < n*m) →
      (65 ≤ Znth next flat 0 ∧ Znth next flat 0 ≤ 90) → GreedyPlacementTrace n m (next+1) flat
  | GreedyTrace_place : ∀ next before after i j color side,
      GreedyPlacementTrace n m next before → next = i*m+j → (0 ≤ i ∧ i < n) → (0 ≤ j ∧ j < m) →
      Znth next before 0 = 0 → SettledSquareState before n m i j color side →
      PaintRectanglePrefix before after m i j side color (side*side) → GreedyPlacementTrace n m (next+1) after
export GreedyPlacementTrace (GreedyTrace_zero GreedyTrace_skip GreedyTrace_place)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
