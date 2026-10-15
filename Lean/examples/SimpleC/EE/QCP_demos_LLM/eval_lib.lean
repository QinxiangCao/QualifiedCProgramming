import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.QCP_demos_LLM
open SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance eval_libSacContext : SacContext := ⟨naive_C_Rules⟩

inductive unop where
  | T_not | T_uminus
inductive binop where
  | T_plus | T_minus | T_mul | T_div | T_mod | T_lt | T_le
  | T_ge | T_gt | T_eq | T_ne | T_and | T_or
inductive expr where
  | EConst : Int → expr
  | EVar : Int → expr
  | EUnop : unop → expr → expr
  | EBinop : binop → expr → expr → expr
export expr (EConst EVar EUnop EBinop)

def UnOpID : unop → Int
  | .T_uminus => 0 | .T_not => 1
def BinOpID : binop → Int
  | .T_plus => 0 | .T_minus => 1 | .T_mul => 2 | .T_div => 3
  | .T_mod => 4 | .T_lt => 5 | .T_gt => 6 | .T_le => 7
  | .T_ge => 8 | .T_eq => 9 | .T_ne => 10 | .T_and => 11 | .T_or => 12

noncomputable def store_expr (p : Int) : expr → Assertion
  | .EConst v => (&(p # "expr" ->ₛ "t") # INT |-> 0) **
      (&(((p # "expr" ->ₛ "d") .ₛ "CONST") .ₛ "value") # INT |-> v)
  | .EVar name => (&(p # "expr" ->ₛ "t") # INT |-> 1) **
      (&(((p # "expr" ->ₛ "d") .ₛ "VAR") .ₛ "name") # INT |-> name)
  | .EBinop op e1 e2 => EX p1 : Int, EX p2 : Int,
      (&(p # "expr" ->ₛ "t") # INT |-> 2) **
      (&(((p # "expr" ->ₛ "d") .ₛ "BINOP") .ₛ "op") # INT |-> BinOpID op) **
      (&(((p # "expr" ->ₛ "d") .ₛ "BINOP") .ₛ "left") # PTR |-> p1) **
      (&(((p # "expr" ->ₛ "d") .ₛ "BINOP") .ₛ "right") # PTR |-> p2) **
      store_expr p1 e1 ** store_expr p2 e2
  | .EUnop op e => EX p1 : Int,
      (&(p # "expr" ->ₛ "t") # INT |-> 3) **
      (&(((p # "expr" ->ₛ "d") .ₛ "UNOP") .ₛ "op") # INT |-> UnOpID op) **
      (&(((p # "expr" ->ₛ "d") .ₛ "UNOP") .ₛ "arg") # PTR |-> p1) ** store_expr p1 e

noncomputable def store_expr_aux (p t : Int) : expr → Assertion
  | .EConst v => “ t = 0 ” &&
      (&(((p # "expr" ->ₛ "d") .ₛ "CONST") .ₛ "value") # INT |-> v)
  | .EVar name => “ t = 1 ” &&
      (&(((p # "expr" ->ₛ "d") .ₛ "VAR") .ₛ "name") # INT |-> name)
  | .EBinop op e1 e2 => EX p1 : Int, EX p2 : Int,
      “ t = 2 ” &&
      (&(((p # "expr" ->ₛ "d") .ₛ "BINOP") .ₛ "op") # INT |-> BinOpID op) **
      (&(((p # "expr" ->ₛ "d") .ₛ "BINOP") .ₛ "left") # PTR |-> p1) **
      (&(((p # "expr" ->ₛ "d") .ₛ "BINOP") .ₛ "right") # PTR |-> p2) **
      store_expr p1 e1 ** store_expr p2 e2
  | .EUnop op e => EX p1 : Int,
      “ t = 3 ” &&
      (&(((p # "expr" ->ₛ "d") .ₛ "UNOP") .ₛ "op") # INT |-> UnOpID op) **
      (&(((p # "expr" ->ₛ "d") .ₛ "UNOP") .ₛ "arg") # PTR |-> p1) ** store_expr p1 e
end SimpleC.EE.QCP_demos_LLM
