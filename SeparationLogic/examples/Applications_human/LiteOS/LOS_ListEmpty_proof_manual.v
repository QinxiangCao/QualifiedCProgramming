Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.LiteOS Require Import LOS_ListEmpty_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_LOS_ListEmpty_return_wit_1 : LOS_ListEmpty_return_wit_1.
Proof.
    pre_process.
    intros.
    unfold store_dll.
    Exists h pt.
    induction l.
    -
    unfold dllseg.
    simpl.
    entailer!.
    -
    simpl.
    Intros z.
    subst h.
    Exists z.
    entailer!.
    congruence.
Qed.

Lemma dllseg_neq:
  forall {A : Type} (storeA : addr -> A -> Assertion)
  (x px y py: addr) (l: list (DL_Node A)),
  x <> y ->
  dllseg storeA x px y py l |--
  EX z a l0,
    “ l = a :: l0 ” &&
    “ x = a.(ptr) ” &&
    storeA x a.(dll_data) **
    &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px ** 
    &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z **
    dllseg storeA z x y py l0.
Proof.
  intros.
  destruct l; simpl.
  + entailer!.
  + Intros z0.
    Exists z0 d l.
    entailer!.
Qed.


Lemma proof_of_LOS_ListEmpty_return_wit_2 : LOS_ListEmpty_return_wit_2.
Proof. 
    pre_process.
    intros.
    unfold store_dll.
    Exists h pt.
    induction l.
    -
    unfold dllseg.
    simpl.
    entailer!.
    -
    simpl.
    Intros z.
    subst h.
    prop_apply (dup_store_ptr (&(node_pre # "LOS_DL_LIST" ->ₛ "pstPrev")) node_pre pt).
    entailer!.
Qed. 

Lemma proof_of_LOS_ListEmpty_which_implies_wit_1 : LOS_ListEmpty_which_implies_wit_1.
Proof. 
    unfold LOS_ListEmpty_which_implies_wit_1.
    pre_process.
Qed.
