Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_LLM.bst_fp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition bst_fp_strategy0 :=
  forall (p : Z) (tr0 : tree) (fa : Z),
    TT &&
    emp **
    ((store_tree p fa tr0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (tr1 : tree),
      TT &&
      (“ (tr0 = tr1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_tree p fa tr1))
      ).

Definition bst_fp_strategy1 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (pt : partial_tree) (q : Z) (r : Z) (p : Z),
    TT &&
    (“ (pt = ( empty_partial_tree)) ”) &&
    emp **
    ((poly_store FET_ptr p r)) -*
    TT &&
    emp **
    ((store_ptb p p q q pt)) **
    ((poly_store FET_ptr p r))
    ).

Definition bst_fp_strategy2 :=
  forall (fa : Z) (p : Z),
    TT &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "tree" ->ₛ "father") fa))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "tree" ->ₛ "father") fa))
    ) ** (
    ALL (tr0 : tree) (tr1 : tree) (v : Z) (tr2 : tree) (k : Z) (l : Z) (r : Z),
      TT &&
      (“ (p <> 0) ”) &&
      (“ (Z.le (Z.opp 2147483648) k) ”) &&
      (“ (Z.le k 2147483647) ”) &&
      (“ (tr0 = ( make_tree tr1 k v tr2)) ”) &&
      emp **
      ((poly_store FET_int &( ((p)) # "tree" ->ₛ "key") k)) **
      ((poly_store FET_int &( ((p)) # "tree" ->ₛ "value") v)) **
      ((poly_store FET_ptr &( ((p)) # "tree" ->ₛ "father") fa)) **
      ((poly_store FET_ptr &( ((p)) # "tree" ->ₛ "left") l)) **
      ((store_tree l p tr1)) **
      ((poly_store FET_ptr &( ((p)) # "tree" ->ₛ "right") r)) **
      ((store_tree r p tr2)) -*
      TT &&
      emp **
      ((store_tree p fa tr0))
      ).

Module Type bst_fp_Strategy_Correct.

  Axiom bst_fp_strategy0_correctness : bst_fp_strategy0.
  Axiom bst_fp_strategy1_correctness : bst_fp_strategy1.
  Axiom bst_fp_strategy2_correctness : bst_fp_strategy2.

End bst_fp_Strategy_Correct.
