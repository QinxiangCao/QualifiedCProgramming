import SimpleC.EE.QCP_demos_LLM.sll_lib

open SimpleC.SL.CommonAssertion SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance sll_shape_libSacContext : SacContext := ⟨naive_C_Rules⟩

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_auto_goal

def listrep (x : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sll x l
def lseg (x y : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sllseg x y l
def listboxseg (x y : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sllbseg x y l
def sll_tag (_ : Int) : Prop := True

end SimpleC.EE.QCP_demos_LLM.generated.sll_auto_goal

namespace SimpleC.EE.QCP_demos_LLM.generated.array_auto_goal

def listrep (x : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sll x l
def lseg (x y : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sllseg x y l
def listboxseg (x y : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sllbseg x y l
def sll_tag (_ : Int) : Prop := True

end SimpleC.EE.QCP_demos_LLM.generated.array_auto_goal

namespace SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal

def listrep (x : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sll x l
def lseg (x y : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sllseg x y l
def listboxseg (x y : Int) : Assertion := EX l : List Int, SimpleC.EE.QCP_demos_LLM.sllbseg x y l
def sll_tag (_ : Int) : Prop := True

open SimpleC.SL.CNotation
open SimpleC.EE.QCP_demos_LLM.sll_lib

theorem listrep_zero (p : Int) (hp : p = 0) : listrep p |-- emp := by
  unfold listrep
  Intros l
  sep_apply (sll_zero p l hp)
  entailer!

theorem lseg_listrep (p q : Int) : lseg p q ** listrep q |-- listrep p := by
  unfold lseg listrep
  Intros l1 l2
  Exists (l1 ++ l2)
  sep_apply (sllseg_sll p q l1 l2)
  cancel

theorem lseg_lseg (p q r : Int) : lseg p q ** lseg q r |-- lseg p r := by
  unfold lseg
  Intros l1 l2
  Exists (l1 ++ l2)
  sep_apply (sllseg_sllseg p q r l1 l2)
  cancel

theorem lseg_zero_listrep (p : Int) : lseg p 0 |-- listrep p := by
  unfold lseg listrep
  Intros l
  Exists l
  exact sllseg_0_sll p l

theorem listrep_nonzero (p : Int) (hp : p ≠ 0) :
    listrep p |-- EX y : Int, EX v : Int,
      (data_addr p # INT |-> v) ** (next_addr p # PTR |-> y) ** listrep y := by
  unfold listrep
  Intros l
  sep_apply (sll_not_zero p l hp)
  Intros y v tail
  Exists y v tail
  entailer!

theorem lseg_len1 (p v q : Int) (hp : p ≠ 0) :
    (data_addr p # INT |-> v) ** (next_addr p # PTR |-> q) |-- lseg p q := by
  unfold lseg
  Exists [v]
  sep_apply (sllseg_len1 p v q hp)
  cancel

theorem lseg_unfold_head (p q : Int) (hpq : p ≠ q) :
    lseg p q |-- EX v : Int, EX z : Int,
      (data_addr p # INT |-> v) ** (next_addr p # PTR |-> z) ** lseg z q := by
  unfold lseg
  Intros l
  sep_apply (sllseg_unfold_head p q l hpq)
  Intros v z tail
  Exists v z tail
  entailer!

end SimpleC.EE.QCP_demos_LLM.generated.sll_shape_strategy_goal
