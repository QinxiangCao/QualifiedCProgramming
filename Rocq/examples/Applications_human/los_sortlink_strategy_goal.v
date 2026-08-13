Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition los_sortlink_strategy7 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node A))) (x : Z),
    TT &&
    emp **
    ((store_dll storeA x l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_dll storeA x l1))
      ).

Definition los_sortlink_strategy14 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node (@sortedLinkNode A)))) (x : Z),
    TT &&
    emp **
    ((store_sorted_dll storeA x l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node (@sortedLinkNode A)))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sorted_dll storeA x l1))
      ).

Definition los_sortlink_strategy15 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (py : Z) (l0 : (@list (@DL_Node A))) (px : Z),
    TT &&
    emp **
    ((dllseg_shift storeA px py l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg_shift storeA px py l1))
      ).

Definition los_sortlink_strategy18 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (a : (@sortedLinkNode A)) (x : Z),
    TT &&
    emp **
    ((storesortedLinkNode storeA x a))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((storesortedLinkNode storeA x a))
    ).

Definition los_sortlink_strategy19 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A : Type) (l : (@list (@DL_Node (@sortedLinkNode A)))) (l1 : (@list (@DL_Node (@sortedLinkNode A)))) (b : (@DL_Node (@sortedLinkNode A))) (a : (@DL_Node (@sortedLinkNode A))),
    TT &&
    (“ (a = b) ”) &&
    (“ (l = l1) ”) &&
    emp -*
    TT &&
    (“ ((@cons (@DL_Node (@sortedLinkNode A)) a l) = (@cons (@DL_Node (@sortedLinkNode A)) b l1)) ”) &&
    emp
    ).

Definition los_sortlink_strategy6 :=
  forall (A : Type) (p : Z) (x : A) (storeA : (Z -> (A -> Assertion))),
    TT &&
    emp **
    ((storeA p x))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (y : A),
      TT &&
      (“ (x = y) ”) &&
      emp -*
      TT &&
      emp **
      ((storeA p y))
      ).

Definition los_sortlink_strategy20 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (A1 : Type) (t : Z) (a1 : (@DL_Node (@sortedLinkNode A1))) (x : Z) (b1 : A1),
    TT &&
    (“ (x = (@ptr (@sortedLinkNode A1) a1)) ”) &&
    (“ (b1 = (@sl_data A1 (@data (@sortedLinkNode A1) a1))) ”) &&
    (“ (t = (@responseTime A1 (@data (@sortedLinkNode A1) a1))) ”) &&
    emp -*
    TT &&
    (“ (a1 = (@Build_DL_Node (@sortedLinkNode A1) (@mksortedLinkNode A1 b1 t) x)) ”) &&
    emp
    ).

Definition los_sortlink_strategy21 :=
  forall (rt : Z) (h : Z) (px : Z),
    TT &&
    (“ (&( ((rt)) # "anonymous struct 1" ->ₛ "sortLinkNode") = h) ”) &&
    emp **
    ((poly_store FET_ptr &( ((&( ((rt)) # "anonymous struct 1" ->ₛ "sortLinkNode"))) # "LOS_DL_LIST" ->ₛ "pstNext") px))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (v : Z),
      TT &&
      (“ (v = px) ”) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr &( ((h)) # "LOS_DL_LIST" ->ₛ "pstNext") v))
      ).

Definition los_sortlink_strategy22 :=
  forall (A : Type) (la : Z) (re : Z) (sa : Z) (storeA : (Z -> (A -> Assertion))) (sp : Z) (l : (@list (@DL_Node (@sortedLinkNode A)))) (h : Z),
    TT &&
    emp **
    ((poly_store FET_ptr sa sp)) **
    ((poly_store FET_ptr la re)) **
    ((dllseg_shift_rev (@storesortedLinkNode A storeA) h &( ((sp)) # "SortLinkAttribute" ->ₛ "sortLink") l))
    |--
    (
    TT &&
    emp **
    ((poly_store FET_ptr sa sp)) **
    ((poly_store FET_ptr la re))
    ) ** (
    TT &&
    (“ (h = &( ((re)) # "anonymous struct 1" ->ₛ "sortLinkNode")) ”) &&
    emp -*
    TT &&
    emp **
    ((dllseg_shift_rev (@storesortedLinkNode A storeA) &( ((re)) # "anonymous struct 1" ->ₛ "sortLinkNode") &( ((sp)) # "SortLinkAttribute" ->ₛ "sortLink") l))
    ).

Definition los_sortlink_strategy17 :=
  forall (A : Type) (l0 : (@list (@DL_Node A))) (py : Z) (a : A) (storeA : (Z -> (A -> Assertion))) (x : Z) (px : Z),
    TT &&
    emp **
    ((dllseg_shift storeA x py l0)) **
    ((storeA x a)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") px)) **
    ((poly_store FET_ptr &( ((px)) # "LOS_DL_LIST" ->ₛ "pstNext") x))
    |--
    (
    TT &&
    emp **
    ((dllseg_shift storeA px py (@cons (@DL_Node A) (@Build_DL_Node A a x) l0)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition los_sortlink_strategy3 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node A))) (p : Z),
    TT &&
    emp **
    ((store_dll storeA p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_dll storeA p l1))
      ).

Definition los_sortlink_strategy8 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (px : Z) (py : Z) (l0 : (@list (@DL_Node A))) (y : Z) (x : Z),
    TT &&
    emp **
    ((dllseg storeA x px y py l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node A))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((dllseg storeA x px y py l1))
      ).

Definition los_sortlink_strategy11 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (l0 : (@list (@DL_Node (@sortedLinkNode A)))) (p : Z),
    TT &&
    emp **
    ((store_sorted_dll storeA p l0))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l1 : (@list (@DL_Node (@sortedLinkNode A)))),
      TT &&
      (“ (l0 = l1) ”) &&
      emp -*
      TT &&
      emp **
      ((store_sorted_dll storeA p l1))
      ).

Definition los_sortlink_strategy16 :=
  forall (A : Type) (storeA : (Z -> (A -> Assertion))) (py : Z) (x : Z) (a : A) (l0 : (@list (@DL_Node A))) (px : Z),
    TT &&
    emp **
    ((dllseg_shift storeA px py (@cons (@DL_Node A) (@Build_DL_Node A a x) l0)))
    |--
    (
    TT &&
    emp **
    ((storeA x a)) **
    ((poly_store FET_ptr &( ((x)) # "LOS_DL_LIST" ->ₛ "pstPrev") px)) **
    ((poly_store FET_ptr &( ((px)) # "LOS_DL_LIST" ->ₛ "pstNext") x)) **
    ((dllseg_shift storeA x py l0))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type los_sortlink_Strategy_Correct.

  Axiom los_sortlink_strategy7_correctness : los_sortlink_strategy7.
  Axiom los_sortlink_strategy14_correctness : los_sortlink_strategy14.
  Axiom los_sortlink_strategy15_correctness : los_sortlink_strategy15.
  Axiom los_sortlink_strategy18_correctness : los_sortlink_strategy18.
  Axiom los_sortlink_strategy19_correctness : los_sortlink_strategy19.
  Axiom los_sortlink_strategy6_correctness : los_sortlink_strategy6.
  Axiom los_sortlink_strategy20_correctness : los_sortlink_strategy20.
  Axiom los_sortlink_strategy21_correctness : los_sortlink_strategy21.
  Axiom los_sortlink_strategy22_correctness : los_sortlink_strategy22.
  Axiom los_sortlink_strategy17_correctness : los_sortlink_strategy17.
  Axiom los_sortlink_strategy3_correctness : los_sortlink_strategy3.
  Axiom los_sortlink_strategy8_correctness : los_sortlink_strategy8.
  Axiom los_sortlink_strategy11_correctness : los_sortlink_strategy11.
  Axiom los_sortlink_strategy16_correctness : los_sortlink_strategy16.

End los_sortlink_Strategy_Correct.
