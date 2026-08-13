import SimpleC.SL.SeparationLogic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace SimpleC.EE.QCP_demos_LLM.dll_queue_lib

open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance dll_queue_libSacContext : SacContext := ⟨naive_C_Rules⟩

def dlistrep (x prev : addr) : List Int -> Assertion
  | [] => “ x = NULL ” && emp
  | a :: l0 =>
      “ x ≠ NULL ” &&
        (EX y : addr,
          ((&((x # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((x # "list") ->ₛ "next")) # PTR |-> (y)) ** ((&((x # "list") ->ₛ "prev")) # PTR |-> (prev)) ** dlistrep y x l0)

def dllseg (x y px py : addr) : List Int -> Assertion
  | [] => “ x = y ” && “ px = py ” && emp
  | a :: l0 =>
      “ x ≠ NULL ” &&
        (EX z : addr,
          ((&((x # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((x # "list") ->ₛ "next")) # PTR |-> (z)) ** ((&((x # "list") ->ₛ "prev")) # PTR |-> (px)) ** dllseg z y x py l0)

def store_queue (x : addr) (l : List Int) : Assertion :=
  EX h : addr, EX t : addr,
    ((&((x # "queue") ->ₛ "head")) # PTR |-> (h)) ** ((&((x # "queue") ->ₛ "tail")) # PTR |-> (t)) ** dllseg h NULL NULL t l

attribute [irreducible] dlistrep dllseg

theorem dllseg_len1 (x px nx : addr) (a : Int) (hx : x ≠ NULL) :
    ((&((x # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((x # "list") ->ₛ "next")) # PTR |-> (nx)) ** ((&((x # "list") ->ₛ "prev")) # PTR |-> (px)) |--
      dllseg x nx px x [a] := by
  rw [dllseg.eq_2]
  Exists nx
  rw [dllseg.eq_1]
  entailer!

theorem dllseg_dllseg (x y z px py pz : addr) (l1 l2 : List Int) :
    dllseg x y px py l1 ** dllseg y z py pz l2 |--
      dllseg x z px pz (l1 ++ l2) := by
  induction l1 generalizing x px with
  | nil =>
      simp only [List.nil_append]
      rw [dllseg.eq_1]
      Intros
      subst x
      subst px
      entailer!
  | cons a l1 ih =>
      simp only [List.cons_append]
      rw [dllseg.eq_2, dllseg.eq_2]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hx, u, head, tail, hheadTail, hhead, htail⟩
      rcases SacContext.rules.toContext.join_assoc
          head tail right left state hheadTail hjoin with
        ⟨tailRight, htailRight, hheadResult⟩
      have hcombined := ih u x tailRight
        ⟨tail, right, htailRight, htail, hright⟩
      exact ⟨hx, u, head, tailRight, hheadResult, hhead, hcombined⟩

theorem dllseg_head_zero (x y px py : addr) (l : List Int) (hx : x = 0) :
    dllseg x y px py l |-- “ y = 0 ” && “ px = py ” &&
      “ l = [] ” && emp := by
  subst x
  cases l with
  | nil =>
      rw [dllseg.eq_1]
      entailer!
  | cons a l =>
      rw [dllseg.eq_2]
      Intros z
      entailer!

theorem dllseg_head_neq (x y px py : addr) (l : List Int) (hxy : x ≠ y) :
    dllseg x y px py l |--
      EX z : addr, EX a : Int, EX l0 : List Int,
        “ l = a :: l0 ” && ((&((x # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((x # "list") ->ₛ "next")) # PTR |-> (z)) **
        ((&((x # "list") ->ₛ "prev")) # PTR |-> (px)) ** dllseg z y x py l0 := by
  cases l with
  | nil =>
      rw [dllseg.eq_1]
      entailer!
  | cons a l =>
      rw [dllseg.eq_2]
      Intros z
      Exists z a l
      entailer!

theorem dllseg_head_neq_destruct_tail_aux
    (x y px py : addr) (l : List Int) :
    dllseg x y px py l |--
      (“ x = y ” && “ px = py ” && “ l = [] ” && emp) ||
      (EX z : addr, EX l0 : List Int, EX a : Int,
        “ py ≠ 0 ” && “ l = l0 ++ [a] ” &&
        dllseg x py px z l0 ** ((&((py # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((py # "list") ->ₛ "next")) # PTR |-> (y)) **
        ((&((py # "list") ->ₛ "prev")) # PTR |-> (z))) := by
  induction l generalizing x px with
  | nil =>
      rw [dllseg.eq_1]
      Left
      entailer!
  | cons a l ih =>
      rw [dllseg.eq_2]
      Intros z
      sep_apply (ih z x)
      Split
      · Intros
        Right
        Exists px ([] : List Int) a
        subst z
        subst x
        rw [dllseg.eq_1]
        entailer!
      · Intros z0 l0 a0
        Right
        Exists z0 (a :: l0) a0
        simp only [dllseg]
        Exists z
        entailer! <;> (subst l; simp)

theorem dllseg_head_neq_destruct_tail
    (x y px py : addr) (l : List Int) (hxy : x ≠ y) :
    dllseg x y px py l |--
      EX z : addr, EX l0 : List Int, EX a : Int,
        “ py ≠ 0 ” && “ l = l0 ++ [a] ” &&
        dllseg x py px z l0 ** ((&((py # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((py # "list") ->ₛ "next")) # PTR |-> (y)) **
        ((&((py # "list") ->ₛ "prev")) # PTR |-> (z)) := by
  sep_apply (dllseg_head_neq_destruct_tail_aux x y px py l)
  Split
  · Intros
    contradiction
  · entailer!

theorem dllseg_head_neq_destruct_tail'
    (x y px py : addr) (l : List Int) (hpxy : px ≠ py) :
    dllseg x y px py l |--
      EX z : addr, EX l0 : List Int, EX a : Int,
        “ py ≠ 0 ” && “ l = l0 ++ [a] ” &&
        dllseg x py px z l0 ** ((&((py # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((py # "list") ->ₛ "next")) # PTR |-> (y)) **
        ((&((py # "list") ->ₛ "prev")) # PTR |-> (z)) := by
  sep_apply (dllseg_head_neq_destruct_tail_aux x y px py l)
  Split
  · Intros
    contradiction
  · entailer!

theorem dll_zero (x prev : addr) (l : List Int) (hx : x = NULL) :
    dlistrep x prev l |-- “ l = [] ” && emp := by
  subst x
  cases l with
  | nil =>
      rw [dlistrep.eq_1]
      entailer!
  | cons a l =>
      rw [dlistrep.eq_2]
      Intros y
      entailer!

theorem dll_not_zero (x prev : addr) (l : List Int) (hx : x ≠ NULL) :
    dlistrep x prev l |--
      EX y : addr, EX a : Int, EX l0 : List Int,
        “ l = a :: l0 ” && ((&((x # "list") ->ₛ "data")) # INT |-> (a)) ** ((&((x # "list") ->ₛ "next")) # PTR |-> (y)) **
        ((&((x # "list") ->ₛ "prev")) # PTR |-> (prev)) ** dlistrep y x l0 := by
  cases l with
  | nil =>
      rw [dlistrep.eq_1]
      entailer!
  | cons a l =>
      rw [dlistrep.eq_2]
      Intros y
      Exists y a l
      entailer!

theorem dllseg_dlistrep (x y px py : addr) (l1 l2 : List Int) :
    dllseg x y px py l1 ** dlistrep y py l2 |--
      dlistrep x px (l1 ++ l2) := by
  induction l1 generalizing x y px py l2 with
  | nil =>
      simp only [List.nil_append]
      rw [dllseg.eq_1]
      Intros
      subst x
      subst px
      entailer!
  | cons a l1 ih =>
      simp only [List.cons_append]
      rw [dllseg.eq_2, dlistrep.eq_2]
      intro state h
      rcases h with ⟨left, right, hjoin, hleft, hright⟩
      rcases hleft with ⟨hx, z, head, tail, hheadTail, hhead, htail⟩
      rcases SacContext.rules.toContext.join_assoc
          head tail right left state hheadTail hjoin with
        ⟨tailRight, htailRight, hheadResult⟩
      have hcombined := ih z y x py l2 tailRight
        ⟨tail, right, htailRight, htail, hright⟩
      exact ⟨hx, z, head, tailRight, hheadResult, hhead, hcombined⟩

end SimpleC.EE.QCP_demos_LLM.dll_queue_lib

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.dll_queue_lib (dlistrep dllseg store_queue)

end SimpleC.EE.QCP_demos_LLM
