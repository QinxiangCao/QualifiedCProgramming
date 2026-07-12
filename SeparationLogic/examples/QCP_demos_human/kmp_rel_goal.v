Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import SimpleC.EE.QCP_demos_human.kmp_rel_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import safeexecE_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import safeexecE_strategy_proof.

(*----- Function inner -----*)

Definition inner_safety_wit_1 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH2 : (m_low_level_spec <= n_low_level_spec)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition inner_safety_wit_2 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) = ch)) (PreH2 : (0 <= j)) (PreH3 : (j < m_low_level_spec)) (PreH4 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH5 : (m_low_level_spec <= n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition inner_safety_wit_3 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) = ch)) (PreH2 : (0 <= j)) (PreH3 : (j < m_low_level_spec)) (PreH4 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH5 : (m_low_level_spec <= n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition inner_safety_wit_4 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH2 : (0 <= j)) (PreH3 : (j < m_low_level_spec)) (PreH4 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH5 : (m_low_level_spec <= n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inner_safety_wit_5 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition inner_safety_wit_6 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition inner_safety_wit_7 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ch" ) )) # Char  |-> ch)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition inner_entail_wit_1 := 
forall (j_pre: Z) (ch_pre: Z) (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch_pre) (j_pre)) X_low_level_spec )) (PreH2 : (m_low_level_spec <= n_low_level_spec)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch_pre) (j_pre)) X_low_level_spec ) ” 
  &&  “ (m_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_entail_wit_2 := 
(
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH2 : (m_low_level_spec <= n_low_level_spec)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (0 <= j) ” 
  &&  “ (j < m_low_level_spec) ” 
  &&  “ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) ” 
  &&  “ (m_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH2 : (m_low_level_spec <= n_low_level_spec)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  “ (j < m_low_level_spec) ” 
  &&  “ (0 <= j) ”
  &&  emp
).

Definition inner_entail_wit_2_split_goal_1 := 
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH2 : (m_low_level_spec <= n_low_level_spec)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  (j < m_low_level_spec)
.

Definition inner_entail_wit_2_split_goal_2 := 
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH2 : (m_low_level_spec <= n_low_level_spec)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  (0 <= j)
.

Definition inner_entail_wit_3 := 
(
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  “ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) ((Znth (j - 1 ) vnext0_low_level_spec 0))) X_low_level_spec ) ” 
  &&  “ (m_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) ((Znth (j - 1 ) vnext0_low_level_spec 0))) X_low_level_spec ) ”
  &&  emp
).

Definition inner_entail_wit_3_split_goal_1 := 
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) ((Znth (j - 1 ) vnext0_low_level_spec 0))) X_low_level_spec )
.

Definition inner_return_wit_1 := 
(
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (return (0)) X_low_level_spec ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < (m_low_level_spec + 1 )) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (return (0)) X_low_level_spec ) ”
  &&  emp
).

Definition inner_return_wit_1_split_goal_1 := 
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j = 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (safeExec ATrue (return (0)) X_low_level_spec )
.

Definition inner_return_wit_2 := 
(
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) = ch)) (PreH2 : (0 <= j)) (PreH3 : (j < m_low_level_spec)) (PreH4 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH5 : (m_low_level_spec <= n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (return ((j + 1 ))) X_low_level_spec ) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) < (m_low_level_spec + 1 )) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) = ch)) (PreH2 : (0 <= j)) (PreH3 : (j < m_low_level_spec)) (PreH4 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH5 : (m_low_level_spec <= n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (return ((j + 1 ))) X_low_level_spec ) ”
  &&  emp
).

Definition inner_return_wit_2_split_goal_1 := 
forall (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) = ch)) (PreH2 : (0 <= j)) (PreH3 : (j < m_low_level_spec)) (PreH4 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH5 : (m_low_level_spec <= n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) ,
  (safeExec ATrue (return ((j + 1 ))) X_low_level_spec )
.

Definition inner_partial_solve_wit_1 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (0 <= j)) (PreH2 : (j < m_low_level_spec)) (PreH3 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH4 : (m_low_level_spec <= n_low_level_spec)) (PreH5 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (0 <= j) ” 
  &&  “ (j < m_low_level_spec) ” 
  &&  “ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) ” 
  &&  “ (m_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (((str_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i str_pre j 0 (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
.

Definition inner_partial_solve_wit_2 := 
forall (vnext_pre: Z) (str_pre: Z) (X_low_level_spec: (Z -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (str0_low_level_spec: (@list Z)) (ch: Z) (j: Z) (PreH1 : (j <> 0)) (PreH2 : ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch)) (PreH3 : (0 <= j)) (PreH4 : (j < m_low_level_spec)) (PreH5 : (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec )) (PreH6 : (m_low_level_spec <= n_low_level_spec)) (PreH7 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec )
|--
  “ (j <> 0) ” 
  &&  “ ((Znth j (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) 0) <> ch) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_low_level_spec) ” 
  &&  “ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch) (j)) X_low_level_spec ) ” 
  &&  “ (m_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (((vnext_pre + ((j - 1 ) * sizeof(INT)))) # Int  |-> (Znth (j - 1 ) vnext0_low_level_spec 0))
  **  (IntArray.missing_i vnext_pre (j - 1 ) 0 m_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) ((@nil Z))))) )
.

(*----- Function constr -----*)

Definition constr_safety_wit_1 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  (IntArray.full retval_2 retval l )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition constr_safety_wit_2 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  (IntArray.full retval_2 retval l )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition constr_safety_wit_3 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full retval_2 retval (replace_Znth (0) (0) (l)) )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition constr_safety_wit_4 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  (IntArray.full retval_2 retval (replace_Znth (0) (0) (l)) )
  **  ((( &( "vnext" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition constr_safety_wit_5 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) (PreH1 : (l0 = (cons (a) (l1)))) (PreH2 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (i + 1 ))) (PreH5 : (i < n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (1 <= i)) ,
  (IntArray.full vnext (i + 1 ) (replace_Znth (i) (retval) ((app (vnext0) ((cons (a) ((@nil Z))))))) )
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l1 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition constr_entail_wit_1 := 
(
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval_2: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval_2 = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  (IntArray.full retval retval_2 (replace_Znth (0) (0) (l)) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> retval_2)
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  “ (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (1) (vnext0) (0)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= 1) ”
  &&  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full retval 1 vnext0 )
  **  (IntArray.full (retval + (1 * sizeof(INT))) (n_low_level_spec - 1 ) l0 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval_2: Z) (l: (@list Z)) (retval: Z) (PreH1 : (retval_2 = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  (IntArray.full retval retval_2 (replace_Znth (0) (0) (l)) )
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  “ (retval_2 = n_low_level_spec) ” 
  &&  “ (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (1) (vnext0) (0)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= 1) ”
  &&  (IntArray.full retval 1 vnext0 )
  **  (IntArray.full (retval + (1 * sizeof(INT))) (n_low_level_spec - 1 ) l0 )
).

Definition constr_entail_wit_2 := 
(
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0_2: (@list Z)) (vnext: Z) (i: Z) (vnext0_2: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) (PreH1 : (l0_2 = (cons (a) (l1)))) (PreH2 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0_2))) (retval)) X_low_level_spec )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (i + 1 ))) (PreH5 : (i < n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (1 <= i)) ,
  (IntArray.full vnext (i + 1 ) (replace_Znth (i) (retval) ((app (vnext0_2) ((cons (a) ((@nil Z))))))) )
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l1 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  EX (l0: (@list Z))  (vnext0: (@list Z)) ,
  “ (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) ((i + 1 )) (vnext0) (retval)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= (i + 1 )) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext (i + 1 ) vnext0 )
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l0 )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0_2: (@list Z)) (i: Z) (vnext0_2: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) (PreH1 : (l0_2 = (cons (a) (l1)))) (PreH2 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0_2))) (retval)) X_low_level_spec )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (i + 1 ))) (PreH5 : (i < n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (1 <= i)) ,
  TT && emp 
|--
  “ (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) ((i + 1 )) ((replace_Znth (i) (retval) ((app (vnext0_2) ((cons (a) ((@nil Z)))))))) (retval)) X_low_level_spec ) ”
  &&  emp
).

Definition constr_entail_wit_2_split_goal_1 := 
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0_2: (@list Z)) (i: Z) (vnext0_2: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) (PreH1 : (l0_2 = (cons (a) (l1)))) (PreH2 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0_2))) (retval)) X_low_level_spec )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (i + 1 ))) (PreH5 : (i < n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (1 <= i)) ,
  (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) ((i + 1 )) ((replace_Znth (i) (retval) ((app (vnext0_2) ((cons (a) ((@nil Z)))))))) (retval)) X_low_level_spec )
.

Definition constr_return_wit_1 := 
(
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext_2: Z) (i: Z) (vnext0: (@list Z)) (j: Z) (PreH1 : (i >= n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_2 i vnext0 )
  **  (IntArray.full (vnext_2 + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  EX (vnext: (@list Z)) ,
  “ (safeExec ATrue (return (vnext)) X_low_level_spec ) ”
  &&  (IntArray.full vnext_2 n_low_level_spec vnext )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
) \/
(
forall (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext_2: Z) (i: Z) (vnext0: (@list Z)) (j: Z) (PreH1 : (i >= n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (1 <= i)) ,
  (IntArray.full vnext_2 i vnext0 )
  **  (IntArray.full (vnext_2 + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  EX (vnext: (@list Z)) ,
  “ (safeExec ATrue (return (vnext)) X_low_level_spec ) ”
  &&  (IntArray.full vnext_2 n_low_level_spec vnext )
).

Definition constr_partial_solve_wit_1 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH2 : (n_low_level_spec > 0)) (PreH3 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  “ (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
.

Definition constr_partial_solve_wit_2_pure := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  ((( &( "vnext" ) )) # Ptr  |->_)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
|--
  “ (retval > 0) ”
.

Definition constr_partial_solve_wit_2_aux := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = n_low_level_spec) ” 
  &&  “ (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
.

Definition constr_partial_solve_wit_2 := constr_partial_solve_wit_2_pure -> constr_partial_solve_wit_2_aux.

Definition constr_partial_solve_wit_3 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (retval: Z) (l: (@list Z)) (retval_2: Z) (PreH1 : (retval = n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) ,
  (IntArray.full retval_2 retval l )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  “ (retval = n_low_level_spec) ” 
  &&  “ (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (((retval_2 + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i retval_2 0 0 retval l )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
.

Definition constr_partial_solve_wit_4 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) (PreH1 : (i < n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (i < n_low_level_spec) ” 
  &&  “ (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= i) ”
  &&  (((patn_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (str_low_level_spec) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i patn_pre i 0 (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
.

Definition constr_partial_solve_wit_5_pure := 
(
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) (PreH1 : (i < n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (i <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) X_low_level_spec ) ”
) \/
(
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) (PreH1 : (n_low_level_spec <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (n_low_level_spec >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i < n_low_level_spec)) (PreH8 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (safeExec ATrue (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) X_low_level_spec ) ”
).

Definition constr_partial_solve_wit_5_pure_split_goal_1 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) (PreH1 : (n_low_level_spec <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (n_low_level_spec >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i < n_low_level_spec)) (PreH8 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (safeExec ATrue (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) X_low_level_spec ) ”
.

Definition constr_partial_solve_wit_5_aux := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (j: Z) (vnext0: (@list Z)) (PreH1 : (i < n_low_level_spec)) (PreH2 : (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (i <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((inner_loop (0) (str_low_level_spec) (vnext0) ((Znth i (app (str_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0)))) X_low_level_spec ) ” 
  &&  “ (i < n_low_level_spec) ” 
  &&  “ (safeExec ATrue (constr_loop_from (0) (str_low_level_spec) (i) (vnext0) (j)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= i) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
.

Definition constr_partial_solve_wit_5 := constr_partial_solve_wit_5_pure -> constr_partial_solve_wit_5_aux.

Definition constr_partial_solve_wit_6_pure := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (i + 1 ))) (PreH4 : (i < n_low_level_spec)) (PreH5 : (n_low_level_spec < INT_MAX)) (PreH6 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "len" ) )) # Int  |-> n_low_level_spec)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (i < n_low_level_spec) ”
.

Definition constr_partial_solve_wit_6_aux := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) (PreH1 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec )) (PreH2 : (0 <= retval)) (PreH3 : (retval < (i + 1 ))) (PreH4 : (i < n_low_level_spec)) (PreH5 : (n_low_level_spec < INT_MAX)) (PreH6 : (1 <= i)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
  **  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  “ (i < n_low_level_spec) ” 
  &&  “ (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (i + 1 )) ” 
  &&  “ (i < n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= i) ”
  &&  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext i vnext0 )
.

Definition constr_partial_solve_wit_6 := constr_partial_solve_wit_6_pure -> constr_partial_solve_wit_6_aux.

Definition constr_partial_solve_wit_7 := 
forall (patn_pre: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) (n_low_level_spec: Z) (str_low_level_spec: (@list Z)) (l0: (@list Z)) (vnext: Z) (i: Z) (vnext0: (@list Z)) (retval: Z) (a: Z) (l1: (@list Z)) (PreH1 : (l0 = (cons (a) (l1)))) (PreH2 : (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec )) (PreH3 : (0 <= retval)) (PreH4 : (retval < (i + 1 ))) (PreH5 : (i < n_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (1 <= i)) ,
  (IntArray.full vnext (i + 1 ) (app (vnext0) ((cons (a) ((@nil Z))))) )
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l1 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  “ (l0 = (cons (a) (l1))) ” 
  &&  “ (safeExec ATrue (applyf ((constr_loop_from_after (0) (str_low_level_spec) (i) (vnext0))) (retval)) X_low_level_spec ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (i + 1 )) ” 
  &&  “ (i < n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (1 <= i) ”
  &&  (((vnext + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i vnext i 0 (i + 1 ) (app (vnext0) ((cons (a) ((@nil Z))))) )
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l1 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) ((@nil Z))))) )
.

Definition constr_which_implies_wit_1 := 
(
forall (n_low_level_spec: Z) (l0: (@list Z)) (i: Z) (vnext: Z) (PreH1 : (i < n_low_level_spec)) ,
  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  EX (a: Z)  (l1: (@list Z)) ,
  “ (l0 = (cons (a) (l1))) ”
  &&  (((vnext + (i * sizeof(INT)))) # Int  |-> a)
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l1 )
) \/
(
forall (n_low_level_spec: Z) (l0: (@list Z)) (i: Z) (vnext: Z) (PreH1 : (i < n_low_level_spec)) ,
  (IntArray.full (vnext + (i * sizeof(INT))) (n_low_level_spec - i ) l0 )
|--
  EX (a: Z)  (l1: (@list Z)) ,
  “ (l0 = (cons (a) (l1))) ”
  &&  (((vnext + (i * sizeof(INT)))) # Int  |-> a)
  **  (IntArray.full (vnext + ((i + 1 ) * sizeof(INT))) (n_low_level_spec - (i + 1 ) ) l1 )
).

(*----- Function match -----*)

Definition match_safety_wit_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH2 : (n_low_level_spec > 0)) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_safety_wit_2 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = n_low_level_spec)) (PreH2 : (retval = m_low_level_spec)) (PreH3 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH4 : (n_low_level_spec > 0)) (PreH5 : (n_low_level_spec < INT_MAX)) (PreH6 : (m_low_level_spec < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "patn_len" ) )) # Int  |-> retval_2)
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "text_len" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition match_safety_wit_3 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 = n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  “ (((i - n_low_level_spec ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - n_low_level_spec ) + 1 )) ”
.

Definition match_safety_wit_4 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 = n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  “ ((i - n_low_level_spec ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - n_low_level_spec )) ”
.

Definition match_safety_wit_5 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 = n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_safety_wit_6 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 <> n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition match_safety_wit_7 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i >= m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition match_safety_wit_8 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i >= m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition match_entail_wit_1 := 
(
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = n_low_level_spec)) (PreH2 : (retval = m_low_level_spec)) (PreH3 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH4 : (n_low_level_spec > 0)) (PreH5 : (n_low_level_spec < INT_MAX)) (PreH6 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "patn_len" ) )) # Int  |-> retval_2)
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "text_len" ) )) # Int  |-> retval)
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (0) (0)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ” 
  &&  “ (0 >= 0) ” 
  &&  “ (retval_2 = n_low_level_spec) ” 
  &&  “ (retval = m_low_level_spec) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = n_low_level_spec)) (PreH2 : (retval = m_low_level_spec)) (PreH3 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH4 : (n_low_level_spec > 0)) (PreH5 : (n_low_level_spec < INT_MAX)) (PreH6 : (m_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (0) (0)) X_low_level_spec ) ”
  &&  emp
).

Definition match_entail_wit_1_split_goal_1 := 
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = n_low_level_spec)) (PreH2 : (retval = m_low_level_spec)) (PreH3 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH4 : (n_low_level_spec > 0)) (PreH5 : (n_low_level_spec < INT_MAX)) (PreH6 : (m_low_level_spec < INT_MAX)) ,
  (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (0) (0)) X_low_level_spec )
.

Definition match_entail_wit_2 := 
(
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 <> n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  “ (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) ((i + 1 )) (retval_3)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ” 
  &&  “ ((i + 1 ) >= 0) ” 
  &&  “ (retval_2 = n_low_level_spec) ” 
  &&  “ (retval = m_low_level_spec) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 <> n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  “ (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) ((i + 1 )) (retval_3)) X_low_level_spec ) ”
  &&  emp
).

Definition match_entail_wit_2_split_goal_1 := 
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 <> n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) ((i + 1 )) (retval_3)) X_low_level_spec )
.

Definition match_return_wit_1 := 
(
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i >= m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  EX (ret: (@option Z)) ,
  “ (safeExec ATrue (return (ret)) X_low_level_spec ) ” 
  &&  “ ((-1) = (option_int_repr (ret))) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i >= m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  EX (ret: (@option Z)) ,
  “ (safeExec ATrue (return (ret)) X_low_level_spec ) ” 
  &&  “ ((-1) = (option_int_repr (ret))) ”
  &&  emp
).

Definition match_return_wit_2 := 
(
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 = n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
|--
  EX (ret: (@option Z)) ,
  “ (safeExec ATrue (return (ret)) X_low_level_spec ) ” 
  &&  “ (((i - n_low_level_spec ) + 1 ) = (option_int_repr (ret))) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (retval_3: Z) (PreH1 : (retval_3 = n_low_level_spec)) (PreH2 : (safeExec ATrue (applyf ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i))) (retval_3)) X_low_level_spec )) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 < (n_low_level_spec + 1 ))) (PreH5 : (i < m_low_level_spec)) (PreH6 : (n_low_level_spec < INT_MAX)) (PreH7 : (m_low_level_spec < INT_MAX)) (PreH8 : (i >= 0)) (PreH9 : (retval_2 = n_low_level_spec)) (PreH10 : (retval = m_low_level_spec)) (PreH11 : (n_low_level_spec > 0)) (PreH12 : (n_low_level_spec < INT_MAX)) (PreH13 : (m_low_level_spec < INT_MAX)) ,
  TT && emp 
|--
  EX (ret: (@option Z)) ,
  “ (safeExec ATrue (return (ret)) X_low_level_spec ) ” 
  &&  “ (((i - n_low_level_spec ) + 1 ) = (option_int_repr (ret))) ”
  &&  emp
).

Definition match_partial_solve_wit_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (PreH1 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH2 : (n_low_level_spec > 0)) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_2 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (PreH1 : (retval = m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec )) (PreH3 : (n_low_level_spec > 0)) (PreH4 : (n_low_level_spec < INT_MAX)) (PreH5 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (retval = m_low_level_spec) ” 
  &&  “ (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_3 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i < m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (i < m_low_level_spec) ” 
  &&  “ (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ” 
  &&  “ (i >= 0) ” 
  &&  “ (retval_2 = n_low_level_spec) ” 
  &&  “ (retval = m_low_level_spec) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  (((text_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i text_pre i 0 (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
.

Definition match_partial_solve_wit_4_pure := 
(
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i < m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (n_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) X_low_level_spec ) ”
) \/
(
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (n_low_level_spec <= INT_MAX)) (PreH2 : (m_low_level_spec <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (n_low_level_spec >= INT_MIN)) (PreH6 : (m_low_level_spec >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i < m_low_level_spec)) (PreH10 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH11 : (n_low_level_spec < INT_MAX)) (PreH12 : (m_low_level_spec < INT_MAX)) (PreH13 : (i >= 0)) (PreH14 : (retval_2 = n_low_level_spec)) (PreH15 : (retval = m_low_level_spec)) (PreH16 : (n_low_level_spec > 0)) (PreH17 : (n_low_level_spec < INT_MAX)) (PreH18 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) X_low_level_spec ) ”
).

Definition match_partial_solve_wit_4_pure_split_goal_1 := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (n_low_level_spec <= INT_MAX)) (PreH2 : (m_low_level_spec <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (j <= INT_MAX)) (PreH5 : (n_low_level_spec >= INT_MIN)) (PreH6 : (m_low_level_spec >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i < m_low_level_spec)) (PreH10 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH11 : (n_low_level_spec < INT_MAX)) (PreH12 : (m_low_level_spec < INT_MAX)) (PreH13 : (i >= 0)) (PreH14 : (retval_2 = n_low_level_spec)) (PreH15 : (retval = m_low_level_spec)) (PreH16 : (n_low_level_spec > 0)) (PreH17 : (n_low_level_spec < INT_MAX)) (PreH18 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text_len" ) )) # Int  |-> m_low_level_spec)
  **  ((( &( "patn_len" ) )) # Int  |-> n_low_level_spec)
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (safeExec ATrue (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) X_low_level_spec ) ”
.

Definition match_partial_solve_wit_4_aux := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (m_low_level_spec: Z) (n_low_level_spec: Z) (vnext0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (patn0_low_level_spec: (@list Z)) (retval: Z) (retval_2: Z) (i: Z) (j: Z) (PreH1 : (i < m_low_level_spec)) (PreH2 : (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec )) (PreH3 : (n_low_level_spec < INT_MAX)) (PreH4 : (m_low_level_spec < INT_MAX)) (PreH5 : (i >= 0)) (PreH6 : (retval_2 = n_low_level_spec)) (PreH7 : (retval = m_low_level_spec)) (PreH8 : (n_low_level_spec > 0)) (PreH9 : (n_low_level_spec < INT_MAX)) (PreH10 : (m_low_level_spec < INT_MAX)) ,
  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
|--
  “ (n_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (safeExec ATrue (bind ((inner_loop (0) (patn0_low_level_spec) (vnext0_low_level_spec) ((Znth i (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) 0)) (j))) ((match_loop_from_after (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i)))) X_low_level_spec ) ” 
  &&  “ (i < m_low_level_spec) ” 
  &&  “ (safeExec ATrue (match_loop_from (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec) (i) (j)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ” 
  &&  “ (i >= 0) ” 
  &&  “ (retval_2 = n_low_level_spec) ” 
  &&  “ (retval = m_low_level_spec) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) ((@nil Z))))) )
.

Definition match_partial_solve_wit_4 := match_partial_solve_wit_4_pure -> match_partial_solve_wit_4_aux.

(*----- Function main -----*)

Definition main_entail_wit_1 := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext: (@list Z)) (retval: Z) (PreH1 : (is_prefix_func vnext patn0 )) (PreH2 : (n > 0)) (PreH3 : (n < INT_MAX)) (PreH4 : (m < INT_MAX)) ,
  (IntArray.full retval n vnext )
  **  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
|--
  EX (vnext0: (@list Z)) ,
  “ (is_prefix_func vnext0 patn0 ) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ”
  &&  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full retval n vnext0 )
.

Definition main_return_wit_1 := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext0: (@list Z)) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (no_occurance patn0 text0 )) (PreH3 : (is_prefix_func vnext0 patn0 )) (PreH4 : (n > 0)) (PreH5 : (n < INT_MAX)) (PreH6 : (m < INT_MAX)) ,
  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
|--
  “ (retval = (-1)) ” 
  &&  “ (no_occurance patn0 text0 ) ”
  &&  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
.

Definition main_return_wit_2 := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext0: (@list Z)) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (first_occur patn0 text0 retval )) (PreH3 : (is_prefix_func vnext0 patn0 )) (PreH4 : (n > 0)) (PreH5 : (n < INT_MAX)) (PreH6 : (m < INT_MAX)) ,
  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
|--
  “ (retval >= 0) ” 
  &&  “ (first_occur patn0 text0 retval ) ”
  &&  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
.

Definition main_partial_solve_wit_1_pure := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (PreH1 : (n > 0)) (PreH2 : (n < INT_MAX)) (PreH3 : (m < INT_MAX)) ,
  ((( &( "vnext" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
|--
  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ”
.

Definition main_partial_solve_wit_1_aux := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (PreH1 : (n > 0)) (PreH2 : (n < INT_MAX)) (PreH3 : (m < INT_MAX)) ,
  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
|--
  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ”
  &&  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
.

Definition main_partial_solve_wit_1 := main_partial_solve_wit_1_pure -> main_partial_solve_wit_1_aux.

Definition main_partial_solve_wit_2_pure := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext: Z) (vnext0: (@list Z)) (PreH1 : (is_prefix_func vnext0 patn0 )) (PreH2 : (n > 0)) (PreH3 : (n < INT_MAX)) (PreH4 : (m < INT_MAX)) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "patn" ) )) # Ptr  |-> patn_pre)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
  **  ((( &( "vnext" ) )) # Ptr  |-> vnext)
  **  (IntArray.full vnext n vnext0 )
|--
  “ (is_prefix_func vnext0 patn0 ) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ”
.

Definition main_partial_solve_wit_2_aux := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext: Z) (vnext0: (@list Z)) (PreH1 : (is_prefix_func vnext0 patn0 )) (PreH2 : (n > 0)) (PreH3 : (n < INT_MAX)) (PreH4 : (m < INT_MAX)) ,
  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext n vnext0 )
|--
  “ (is_prefix_func vnext0 patn0 ) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ” 
  &&  “ (is_prefix_func vnext0 patn0 ) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ”
  &&  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext n vnext0 )
.

Definition main_partial_solve_wit_2 := main_partial_solve_wit_2_pure -> main_partial_solve_wit_2_aux.

Definition main_partial_solve_wit_3 := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext: Z) (vnext0: (@list Z)) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (no_occurance patn0 text0 )) (PreH3 : (is_prefix_func vnext0 patn0 )) (PreH4 : (n > 0)) (PreH5 : (n < INT_MAX)) (PreH6 : (m < INT_MAX)) ,
  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext n vnext0 )
|--
  “ (retval = (-1)) ” 
  &&  “ (no_occurance patn0 text0 ) ” 
  &&  “ (is_prefix_func vnext0 patn0 ) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ”
  &&  (IntArray.full vnext n vnext0 )
  **  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
.

Definition main_partial_solve_wit_4 := 
forall (text_pre: Z) (patn_pre: Z) (m: Z) (n: Z) (text0: (@list Z)) (patn0: (@list Z)) (vnext: Z) (vnext0: (@list Z)) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (first_occur patn0 text0 retval )) (PreH3 : (is_prefix_func vnext0 patn0 )) (PreH4 : (n > 0)) (PreH5 : (n < INT_MAX)) (PreH6 : (m < INT_MAX)) ,
  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full vnext n vnext0 )
|--
  “ (retval >= 0) ” 
  &&  “ (first_occur patn0 text0 retval ) ” 
  &&  “ (is_prefix_func vnext0 patn0 ) ” 
  &&  “ (n > 0) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (m < INT_MAX) ”
  &&  (IntArray.full vnext n vnext0 )
  **  (CharArray.full patn_pre (n + 1 ) (app (patn0) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full text_pre (m + 1 ) (app (text0) ((cons (0) ((@nil Z))))) )
.

Definition match_derive_high_level_spec_by_low_level_spec := 
forall (vnext_pre: Z) (text_pre: Z) (patn_pre: Z) (m_high_level_spec: Z) (n_high_level_spec: Z) (vnext0_high_level_spec: (@list Z)) (text0_high_level_spec: (@list Z)) (patn0_high_level_spec: (@list Z)) ,
  “ (is_prefix_func vnext0_high_level_spec patn0_high_level_spec ) ” 
  &&  “ (n_high_level_spec > 0) ” 
  &&  “ (n_high_level_spec < INT_MAX) ” 
  &&  “ (m_high_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (patn0_high_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_high_level_spec + 1 ) (app (text0_high_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec )
|--
EX (patn0_low_level_spec: (@list Z)) (text0_low_level_spec: (@list Z)) (vnext0_low_level_spec: (@list Z)) (n_low_level_spec: Z) (m_low_level_spec: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (match_loop (0) (patn0_low_level_spec) (text0_low_level_spec) (vnext0_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ” 
  &&  “ (m_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec ))
  **
  ((EX ret retval_2,
  “ (safeExec ATrue (return (ret)) X_low_level_spec ) ” 
  &&  “ (retval_2 = (option_int_repr (ret))) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (patn0_low_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_low_level_spec + 1 ) (app (text0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec ))
  -*
  ((EX retval,
  “ (retval = (-1)) ” 
  &&  “ (no_occurance patn0_high_level_spec text0_high_level_spec ) ”
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (patn0_high_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_high_level_spec + 1 ) (app (text0_high_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec ))
  ||
  (EX retval,
  “ (retval >= 0) ” 
  &&  “ (first_occur patn0_high_level_spec text0_high_level_spec retval ) ”
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (patn0_high_level_spec) ((cons (0) (nil)))) )
  **  (CharArray.full text_pre (m_high_level_spec + 1 ) (app (text0_high_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre n_high_level_spec vnext0_high_level_spec ))))
.

Definition constr_derive_high_level_spec_by_low_level_spec := 
forall (patn_pre: Z) (n_high_level_spec: Z) (str_high_level_spec: (@list Z)) ,
  “ (n_high_level_spec > 0) ” 
  &&  “ (n_high_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (str_high_level_spec) ((cons (0) (nil)))) )
|--
EX (str_low_level_spec: (@list Z)) (n_low_level_spec: Z) (X_low_level_spec: ((@list Z) -> (unit -> Prop))) ,
  (“ (safeExec ATrue (constr_loop (0) (str_low_level_spec)) X_low_level_spec ) ” 
  &&  “ (n_low_level_spec > 0) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) ))
  **
  ((EX vnext_2 retval_2,
  “ (safeExec ATrue (return (vnext_2)) X_low_level_spec ) ”
  &&  (IntArray.full retval_2 n_low_level_spec vnext_2 )
  **  (CharArray.full patn_pre (n_low_level_spec + 1 ) (app (str_low_level_spec) ((cons (0) (nil)))) ))
  -*
  (EX vnext retval,
  “ (is_prefix_func vnext str_high_level_spec ) ”
  &&  (IntArray.full retval n_high_level_spec vnext )
  **  (CharArray.full patn_pre (n_high_level_spec + 1 ) (app (str_high_level_spec) ((cons (0) (nil)))) )))
.

Definition inner_derive_bind_spec_by_low_level_spec := 
forall (B: Type) ,
forall (j_pre: Z) (ch_pre: Z) (vnext_pre: Z) (str_pre: Z) (f_bind_spec: (Z -> (@ MonadErr.M  unit B))) (X_bind_spec: (B -> (unit -> Prop))) (m_bind_spec: Z) (n_bind_spec: Z) (vnext0_bind_spec: (@list Z)) (str0_bind_spec: (@list Z)) ,
  “ (safeExec ATrue (bind ((inner_loop (0) (str0_bind_spec) (vnext0_bind_spec) (ch_pre) (j_pre))) (f_bind_spec)) X_bind_spec ) ” 
  &&  “ (m_bind_spec <= n_bind_spec) ” 
  &&  “ (n_bind_spec < INT_MAX) ”
  &&  (CharArray.full str_pre (n_bind_spec + 1 ) (app (str0_bind_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec )
|--
EX (str0_low_level_spec: (@list Z)) (vnext0_low_level_spec: (@list Z)) (n_low_level_spec: Z) (m_low_level_spec: Z) (X_low_level_spec: (Z -> (unit -> Prop))) ,
  (“ (safeExec ATrue (inner_loop (0) (str0_low_level_spec) (vnext0_low_level_spec) (ch_pre) (j_pre)) X_low_level_spec ) ” 
  &&  “ (m_low_level_spec <= n_low_level_spec) ” 
  &&  “ (n_low_level_spec < INT_MAX) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec ))
  **
  ((EX retval_2,
  “ (safeExec ATrue (return (retval_2)) X_low_level_spec ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < (m_low_level_spec + 1 )) ”
  &&  (CharArray.full str_pre (n_low_level_spec + 1 ) (app (str0_low_level_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_low_level_spec vnext0_low_level_spec ))
  -*
  (EX retval,
  “ (safeExec ATrue (applyf (f_bind_spec) (retval)) X_bind_spec ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < (m_bind_spec + 1 )) ”
  &&  (CharArray.full str_pre (n_bind_spec + 1 ) (app (str0_bind_spec) ((cons (0) (nil)))) )
  **  (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec )))
.

Module Type VC_Correct.

Include safeexecE_Strategy_Correct.

Axiom proof_of_inner_safety_wit_1 : inner_safety_wit_1.
Axiom proof_of_inner_safety_wit_2 : inner_safety_wit_2.
Axiom proof_of_inner_safety_wit_3 : inner_safety_wit_3.
Axiom proof_of_inner_safety_wit_4 : inner_safety_wit_4.
Axiom proof_of_inner_safety_wit_5 : inner_safety_wit_5.
Axiom proof_of_inner_safety_wit_6 : inner_safety_wit_6.
Axiom proof_of_inner_safety_wit_7 : inner_safety_wit_7.
Axiom proof_of_inner_entail_wit_1 : inner_entail_wit_1.
Axiom proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Axiom proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Axiom proof_of_inner_return_wit_1 : inner_return_wit_1.
Axiom proof_of_inner_return_wit_2 : inner_return_wit_2.
Axiom proof_of_inner_partial_solve_wit_1 : inner_partial_solve_wit_1.
Axiom proof_of_inner_partial_solve_wit_2 : inner_partial_solve_wit_2.
Axiom proof_of_constr_safety_wit_1 : constr_safety_wit_1.
Axiom proof_of_constr_safety_wit_2 : constr_safety_wit_2.
Axiom proof_of_constr_safety_wit_3 : constr_safety_wit_3.
Axiom proof_of_constr_safety_wit_4 : constr_safety_wit_4.
Axiom proof_of_constr_safety_wit_5 : constr_safety_wit_5.
Axiom proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Axiom proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Axiom proof_of_constr_return_wit_1 : constr_return_wit_1.
Axiom proof_of_constr_partial_solve_wit_1 : constr_partial_solve_wit_1.
Axiom proof_of_constr_partial_solve_wit_2_pure : constr_partial_solve_wit_2_pure.
Axiom proof_of_constr_partial_solve_wit_2 : constr_partial_solve_wit_2.
Axiom proof_of_constr_partial_solve_wit_3 : constr_partial_solve_wit_3.
Axiom proof_of_constr_partial_solve_wit_4 : constr_partial_solve_wit_4.
Axiom proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Axiom proof_of_constr_partial_solve_wit_5 : constr_partial_solve_wit_5.
Axiom proof_of_constr_partial_solve_wit_6_pure : constr_partial_solve_wit_6_pure.
Axiom proof_of_constr_partial_solve_wit_6 : constr_partial_solve_wit_6.
Axiom proof_of_constr_partial_solve_wit_7 : constr_partial_solve_wit_7.
Axiom proof_of_constr_which_implies_wit_1 : constr_which_implies_wit_1.
Axiom proof_of_match_safety_wit_1 : match_safety_wit_1.
Axiom proof_of_match_safety_wit_2 : match_safety_wit_2.
Axiom proof_of_match_safety_wit_3 : match_safety_wit_3.
Axiom proof_of_match_safety_wit_4 : match_safety_wit_4.
Axiom proof_of_match_safety_wit_5 : match_safety_wit_5.
Axiom proof_of_match_safety_wit_6 : match_safety_wit_6.
Axiom proof_of_match_safety_wit_7 : match_safety_wit_7.
Axiom proof_of_match_safety_wit_8 : match_safety_wit_8.
Axiom proof_of_match_entail_wit_1 : match_entail_wit_1.
Axiom proof_of_match_entail_wit_2 : match_entail_wit_2.
Axiom proof_of_match_return_wit_1 : match_return_wit_1.
Axiom proof_of_match_return_wit_2 : match_return_wit_2.
Axiom proof_of_match_partial_solve_wit_1 : match_partial_solve_wit_1.
Axiom proof_of_match_partial_solve_wit_2 : match_partial_solve_wit_2.
Axiom proof_of_match_partial_solve_wit_3 : match_partial_solve_wit_3.
Axiom proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Axiom proof_of_match_partial_solve_wit_4 : match_partial_solve_wit_4.
Axiom proof_of_main_entail_wit_1 : main_entail_wit_1.
Axiom proof_of_main_return_wit_1 : main_return_wit_1.
Axiom proof_of_main_return_wit_2 : main_return_wit_2.
Axiom proof_of_main_partial_solve_wit_1_pure : main_partial_solve_wit_1_pure.
Axiom proof_of_main_partial_solve_wit_1 : main_partial_solve_wit_1.
Axiom proof_of_main_partial_solve_wit_2_pure : main_partial_solve_wit_2_pure.
Axiom proof_of_main_partial_solve_wit_2 : main_partial_solve_wit_2.
Axiom proof_of_main_partial_solve_wit_3 : main_partial_solve_wit_3.
Axiom proof_of_main_partial_solve_wit_4 : main_partial_solve_wit_4.
Axiom proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Axiom proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.

End VC_Correct.
