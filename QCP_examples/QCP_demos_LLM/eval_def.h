
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.eval_lib */
/*@ Import Lean import SimpleC.EE.QCP_demos_LLM.eval_lib */

/*@ Extern Coq (expr :: *) */
/*@ Extern Coq (binop :: *) */
/*@ Extern Coq (unop :: *) */
/*@ Extern Coq (store_expr : Z -> expr -> Assertion)
               (store_expr_aux : Z -> Z -> expr -> Assertion)
               (EConst: Z -> expr)
               (EVar: Z -> expr)
               (EBinop: binop -> expr -> expr -> expr)
               (EUnop: unop -> expr -> expr)
               (BinOpID: binop -> Z)
               (UnOpID: unop -> Z)
               (eval_fun: list Z -> expr -> Z)
               (store_int_array : Z -> Z -> list Z -> Assertion)
               (store_int_array_missing_i_rec: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (safe_eval: expr -> list Z -> Prop)               
               (expr_eval: expr -> list Z -> Z)
 */

/*@ include strategies "eval.strategies" */
