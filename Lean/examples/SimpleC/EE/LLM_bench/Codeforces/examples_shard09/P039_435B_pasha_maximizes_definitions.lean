import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import ListLib.General.Presuffix

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib


def AdjacentSwap (a b : List Int) : Prop :=
  ∃ i, (0 ≤ i ∧ i < Zlength a - 1) ∧ b = replace_Znth (i+1) (Znth i a 0) (replace_Znth i (Znth (i+1) a 0) a)
def SwapReach (a b : List Int) (k : Int) : Prop :=
  ∃ st : List (List Int), (1 ≤ Zlength st ∧ Zlength st ≤ k + 1) ∧ Znth 0 st [] = a ∧
    Znth (Zlength st - 1) st [] = b ∧ ∀ i, (0 ≤ i ∧ i < Zlength st - 1) → AdjacentSwap (Znth i st []) (Znth (i+1) st [])
def Pre (digits : List Int) (k : Int) : Prop := True
def Spec (digits : List Int) (k : Int) (out : List Int) : Prop :=
  SwapReach digits out k ∧ ∀ q, SwapReach digits q k →
    (q = out ∨ ((∃ i, (0 ≤ i ∧ i < min (Zlength q) (Zlength out)) ∧
      (∀ j, (0 ≤ j ∧ j < i) → Znth j q 0 = Znth j out 0) ∧ Znth i q 0 < Znth i out 0) ∨
      (Zlength q < Zlength out ∧ ListLib.is_prefix q out)))

def LexLe (a b : List Int) : Prop :=
  a = b ∨ (∃ i, (0 ≤ i ∧ i < min (Zlength a) (Zlength b)) ∧
    (∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = Znth j b 0) ∧ Znth i a 0 < Znth i b 0) ∨
    (Zlength a < Zlength b ∧ ListLib.is_prefix a b)

def PrefixEq (a b : List Int) (i : Int) : Prop :=
  Zlength a = Zlength b ∧ (0 ≤ i ∧ i ≤ Zlength a) ∧ ∀ j, (0 ≤ j ∧ j < i) → Znth j a 0 = Znth j b 0

def GreedyProgress (input : List Int) (budget : Int) (current : List Int) (pos remaining : Int) : Prop :=
  Zlength current = Zlength input ∧ (0 ≤ pos ∧ pos ≤ Zlength input) ∧ (0 ≤ remaining ∧ remaining ≤ budget) ∧
    SwapReach input current (budget - remaining) ∧
    ∀ q, SwapReach input q budget → LexLe q current ∨ (PrefixEq q current pos ∧ SwapReach current q remaining)

def FirstMaximumPrefix (l : List Int) (lo hi best : Int) : Prop :=
  (0 ≤ lo ∧ lo < hi) ∧ hi ≤ Zlength l ∧ (lo ≤ best ∧ best < hi) ∧
    (∀ p, (lo ≤ p ∧ p < hi) → Znth p l 0 ≤ Znth best l 0) ∧
    (∀ p, (lo ≤ p ∧ p < best) → Znth p l 0 < Znth best l 0)

def ReachableFirstMaximum (l : List Int) (pos remaining best : Int) : Prop :=
  FirstMaximumPrefix l pos (min (Zlength l) (pos + remaining + 1)) best

def move_left (l : List Int) («from» «to» : Int) : List Int :=
  sublist 0 «to» l ++ [Znth «from» l 0] ++ sublist «to» «from» l ++ sublist («from» + 1) (Zlength l) l

def GreedyExchangeClosure (current : List Int) (pos remaining best : Int) : Prop :=
  let moved := move_left current best pos
  let residual := remaining - (best - pos)
  (∀ q, LexLe q current → LexLe q moved) ∧
    (∀ q, PrefixEq q current pos → SwapReach current q remaining →
      LexLe q moved ∨ (PrefixEq q moved (pos + 1) ∧ SwapReach moved q residual))

def GreedySelectionReady (current : List Int) (pos remaining : Int) : Prop :=
  ∀ best, ReachableFirstMaximum current pos remaining best → GreedyExchangeClosure current pos remaining best

inductive AdjacentSwapList : List Int → List Int → Prop
  | ASL_here : ∀ x y tail, AdjacentSwapList (x :: y :: tail) (y :: x :: tail)
  | ASL_cons : ∀ h left right, AdjacentSwapList left right → AdjacentSwapList (h :: left) (h :: right)
export AdjacentSwapList (ASL_here ASL_cons)

inductive FirstRemove (x : Int) : List Int → Nat → List Int → Prop
  | FirstRemove_here : ∀ tail, FirstRemove x (x :: tail) 0 tail
  | FirstRemove_later : ∀ y tail p rest, x ≠ y → FirstRemove x tail p rest → FirstRemove x (y :: tail) (p + 1) (y :: rest)
export FirstRemove (FirstRemove_here FirstRemove_later)

def CanonicalRemovalCost (source target : List Int) (cost : Nat) : Prop :=
  match target with
  | [] => source = [] ∧ cost = 0
  | x :: target_tail => ∃ p source_rest tail_cost,
      FirstRemove x source p source_rest ∧ CanonicalRemovalCost source_rest target_tail tail_cost ∧ cost = p + tail_cost

inductive AdjacentSwapChain : List (List Int) → Prop
  | ASC_one : ∀ state, AdjacentSwapChain [state]
  | ASC_cons : ∀ left right tail, AdjacentSwap left right → AdjacentSwapChain (right :: tail) → AdjacentSwapChain (left :: right :: tail)
export AdjacentSwapChain (ASC_one ASC_cons)

inductive CanonicalSwapPath : List Int → List Int → Nat → Prop
  | CSP_refl : ∀ state, CanonicalSwapPath state state 0
  | CSP_step : ∀ left middle right steps, AdjacentSwapList left middle → CanonicalSwapPath middle right steps → CanonicalSwapPath left right (steps + 1)
export CanonicalSwapPath (CSP_refl CSP_step)

inductive StructuralLexLe : List Int → List Int → Prop
  | SLL_nil : ∀ right, StructuralLexLe [] right
  | SLL_lt : ∀ x y left right, x < y → StructuralLexLe (x :: left) (y :: right)
  | SLL_eq : ∀ x left right, StructuralLexLe left right → StructuralLexLe (x :: left) (x :: right)
export StructuralLexLe (SLL_nil SLL_lt SLL_eq)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
