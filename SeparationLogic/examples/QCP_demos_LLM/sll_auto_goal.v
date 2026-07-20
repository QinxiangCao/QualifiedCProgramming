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
Require Import SimpleC.EE.QCP_demos_LLM.sll_shape_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import sll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_shape_strategy_proof.

(*----- Function sll_copy -----*)

Definition sll_copy_safety_wit_1 := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (listrep x_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sll_copy_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (listrep x_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sll_copy_entail_wit_1 := 
forall (x_pre: Z) (x: Z) (y: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (x_pre <> 0)) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
|--
  EX (v: Z)  (t_next: Z) ,
  “ (retval <> 0) ” 
  &&  “ (t_next = 0) ”
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre y )
  **  (listrep y )
  **  (lseg retval retval )
.

Definition sll_copy_entail_wit_2 := 
forall (x_pre: Z) (y: Z) (p: Z) (v_2: Z) (t_next_2: Z) (t: Z) (x: Z) (y_2: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (t <> 0)) (PreH4 : (t_next_2 = 0)) (PreH5 : (p <> 0)) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_2 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (lseg x_pre p )
  **  (lseg y t )
|--
  EX (v: Z)  (t_next: Z) ,
  “ (retval <> 0) ” 
  &&  “ (t_next = 0) ”
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre y_2 )
  **  (listrep y_2 )
  **  (lseg y retval )
.

Definition sll_copy_return_wit_1 := 
forall (x_pre: Z) (y: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (p = 0)) ,
  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre p )
  **  (listrep p )
  **  (lseg y t )
|--
  (listrep y )
  **  (listrep x_pre )
.

Definition sll_copy_return_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (listrep x_pre )
|--
  (listrep 0 )
  **  (listrep x_pre )
.

Definition sll_copy_partial_solve_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (listrep x_pre )
|--
  EX (x: Z)  (y: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
.

Definition sll_copy_partial_solve_wit_2_pure := 
forall (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (x = x) ”
.

Definition sll_copy_partial_solve_wit_2_aux := 
forall (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (x = x) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
.

Definition sll_copy_partial_solve_wit_2 := sll_copy_partial_solve_wit_2_pure -> sll_copy_partial_solve_wit_2_aux.

Definition sll_copy_partial_solve_wit_3 := 
forall (x_pre: Z) (y: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (p <> 0)) ,
  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre p )
  **  (listrep p )
  **  (lseg y t )
|--
  EX (x: Z)  (y_2: Z) ,
  “ (t <> 0) ” 
  &&  “ (t_next = 0) ” 
  &&  “ (p <> 0) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_2 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre p )
  **  (lseg y t )
.

Definition sll_copy_partial_solve_wit_4_pure := 
forall (x_pre: Z) (y: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_2 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (lseg x_pre p )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (lseg y t )
|--
  “ (x = x) ”
.

Definition sll_copy_partial_solve_wit_4_aux := 
forall (x_pre: Z) (y: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_2 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre p )
  **  (lseg y t )
|--
  “ (x = x) ” 
  &&  “ (t <> 0) ” 
  &&  “ (t_next = 0) ” 
  &&  “ (p <> 0) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_2 )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (lseg x_pre p )
  **  (lseg y t )
.

Definition sll_copy_partial_solve_wit_4 := sll_copy_partial_solve_wit_4_pure -> sll_copy_partial_solve_wit_4_aux.

(*----- Function sll_free -----*)

Definition sll_free_entail_wit_1 := 
forall (x_pre: Z) ,
  (listrep x_pre )
|--
  (listrep x_pre )
.

Definition sll_free_entail_wit_2 := 
forall (x: Z) (y: Z) (PreH1 : (x <> 0)) ,
  (listrep y )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  ((( &( "y" ) )) # Ptr  |->_)
  **  (listrep y )
.

Definition sll_free_return_wit_1 := 
forall (x: Z) (PreH1 : (x = 0)) ,
  (listrep x )
|--
  TT && emp 
.

Definition sll_free_partial_solve_wit_1 := 
forall (x: Z) (PreH1 : (x <> 0)) ,
  (listrep x )
|--
  EX (y: Z)  (x_2: Z) ,
  “ (x <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
.

Definition sll_free_partial_solve_wit_2 := 
forall (x: Z) (x_2: Z) (y: Z) (PreH1 : (x <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
|--
  “ (x <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (listrep p_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_entail_wit_1 := 
forall (p_pre: Z) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (listrep p_pre )
|--
  ((( &( "p" ) )) # Ptr  |->_)
  **  (listrep 0 )
  **  (listrep p_pre )
.

Definition reverse_entail_wit_2 := 
forall (v: Z) (w: Z) (x: Z) (y: Z) (PreH1 : (v <> 0)) ,
  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (listrep y )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep w )
|--
  (listrep v )
  **  (listrep y )
.

Definition reverse_return_wit_1 := 
forall (v: Z) (w: Z) (PreH1 : (v = 0)) ,
  (listrep w )
  **  (listrep v )
|--
  (listrep w )
.

Definition reverse_partial_solve_wit_1 := 
forall (v: Z) (w: Z) (PreH1 : (v <> 0)) ,
  (listrep w )
  **  (listrep v )
|--
  EX (y: Z)  (x: Z) ,
  “ (v <> 0) ”
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep w )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (listrep x_pre )
  **  (listrep y_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_pre )
|--
  EX (w: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y_pre )
  **  (listrep y )
  **  (lseg x_pre x_pre )
.

Definition append_entail_wit_2 := 
forall (x: Z) (y: Z) (w_2: Z) (u: Z) (t: Z) (x_2: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) ,
  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w_2)
  **  (listrep y )
  **  (lseg x t )
|--
  EX (w: Z) ,
  “ (u <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (listrep y_2 )
  **  (lseg x u )
.

Definition append_return_wit_1 := 
forall (x: Z) (y: Z) (w: Z) (u: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (u = 0)) ,
  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (listrep u )
  **  (lseg x t )
|--
  (listrep x )
.

Definition append_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (listrep x_pre )
  **  (listrep y_pre )
|--
  (listrep y_pre )
.

Definition append_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (listrep x_pre )
  **  (listrep y_pre )
|--
  EX (y: Z)  (x: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_pre )
.

Definition append_partial_solve_wit_2 := 
forall (x: Z) (y: Z) (w: Z) (u: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) ,
  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (listrep u )
  **  (lseg x t )
|--
  EX (y_2: Z)  (x_2: Z) ,
  “ (t <> 0) ” 
  &&  “ (u <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> w)
  **  (listrep y )
  **  (lseg x t )
.

(*----- Function merge -----*)

Definition merge_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "z" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (listrep x_pre )
  **  (listrep y_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_safety_wit_2 := 
forall (z: Z) (x: Z) (t: Z) (y: Z) (x_2: Z) (y_2: Z) (x_3: Z) (y_3: Z) (PreH1 : (y = t)) (PreH2 : (x <> 0)) (PreH3 : (y <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y_3 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  ((( &( "t" ) )) # Ptr  |-> y_2)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (lseg z x )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition merge_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (listrep x_pre )
  **  (listrep y_pre )
|--
  “ (y_pre = y_pre) ” 
  &&  “ (x_pre <> 0) ”
  &&  (lseg x_pre x_pre )
  **  (listrep x_pre )
  **  (listrep y_pre )
.

Definition merge_entail_wit_2 := 
forall (z: Z) (x: Z) (t: Z) (y_3: Z) (x_2: Z) (y: Z) (x_3: Z) (y_2: Z) (PreH1 : (y_2 <> 0)) (PreH2 : (y_3 = t)) (PreH3 : (x <> 0)) (PreH4 : (y_3 <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (listrep y_2 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (lseg z x )
|--
  “ (y = y) ” 
  &&  “ (y_2 <> 0) ”
  &&  (lseg z y_2 )
  **  (listrep y_2 )
  **  (listrep y )
.

Definition merge_return_wit_1 := 
forall (z: Z) (x: Z) (t: Z) (y: Z) (PreH1 : (y = t)) (PreH2 : (x <> 0)) (PreH3 : (y = 0)) ,
  (lseg z x )
  **  (listrep x )
  **  (listrep y )
|--
  (listrep z )
.

Definition merge_return_wit_2 := 
forall (z: Z) (x: Z) (t: Z) (y: Z) (x_2: Z) (y_2: Z) (x_3: Z) (y_3: Z) (PreH1 : (y_3 = 0)) (PreH2 : (y = t)) (PreH3 : (x <> 0)) (PreH4 : (y <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y_3 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (lseg z x )
|--
  (listrep z )
.

Definition merge_return_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (listrep x_pre )
  **  (listrep y_pre )
|--
  (listrep y_pre )
.

Definition merge_partial_solve_wit_1 := 
forall (z: Z) (x: Z) (t: Z) (y: Z) (PreH1 : (y = t)) (PreH2 : (x <> 0)) (PreH3 : (y <> 0)) ,
  (lseg z x )
  **  (listrep x )
  **  (listrep y )
|--
  EX (y_2: Z)  (x_2: Z) ,
  “ (y = t) ” 
  &&  “ (x <> 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (lseg z x )
  **  (listrep x )
.

Definition merge_partial_solve_wit_2 := 
forall (z: Z) (x: Z) (t: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (y = t)) (PreH2 : (x <> 0)) (PreH3 : (y <> 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (lseg z x )
  **  (listrep x )
|--
  EX (y_3: Z)  (x_3: Z) ,
  “ (y = t) ” 
  &&  “ (x <> 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (listrep y_3 )
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (lseg z x )
.

(*----- Function multi_append -----*)

Definition multi_append_safety_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (listrep x_pre )
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_append_entail_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  EX (v: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y_pre )
  **  (listrep z_pre )
  **  (listrep y )
  **  (lseg x_pre x_pre )
.

Definition multi_append_entail_wit_2 := 
forall (x: Z) (z: Z) (y_3: Z) (u: Z) (v_2: Z) (t: Z) (x_2: Z) (y: Z) (x_3: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) (PreH3 : (y_3 <> 0)) ,
  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y )
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (listrep z )
  **  (lseg x t )
|--
  EX (v: Z) ,
  “ (u <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y )
  **  (listrep z )
  **  (listrep y_2 )
  **  (lseg x u )
.

Definition multi_append_return_wit_1 := 
forall (x: Z) (u: Z) (v: Z) (t: Z) (retval: Z) (PreH1 : (t <> 0)) (PreH2 : (u = 0)) ,
  (listrep retval )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (lseg x t )
|--
  (listrep x )
.

Definition multi_append_return_wit_2 := 
forall (x: Z) (y: Z) (u: Z) (v: Z) (t: Z) (retval: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) (PreH3 : (y = 0)) ,
  (listrep retval )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  (lseg x t )
|--
  (listrep x )
.

Definition multi_append_return_wit_3 := 
forall (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) ,
  (listrep retval )
|--
  (listrep retval )
.

Definition multi_append_partial_solve_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (listrep x_pre )
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  “ (x_pre = 0) ”
  &&  (listrep y_pre )
  **  (listrep z_pre )
.

Definition multi_append_partial_solve_wit_2 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (listrep x_pre )
  **  (listrep y_pre )
  **  (listrep z_pre )
|--
  EX (y: Z)  (x: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (listrep y_pre )
  **  (listrep z_pre )
.

Definition multi_append_partial_solve_wit_3 := 
forall (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) (PreH3 : (y <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep y )
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  EX (y_2: Z)  (x_2: Z) ,
  “ (t <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
.

Definition multi_append_partial_solve_wit_4 := 
forall (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) (x_2: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) (PreH3 : (y <> 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  EX (y_3: Z)  (x_3: Z) ,
  “ (t <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  (listrep y_3 )
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y_2 )
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (listrep z )
  **  (lseg x t )
.

Definition multi_append_partial_solve_wit_5 := 
forall (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (u <> 0)) (PreH3 : (y = 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y )
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  “ (t <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y = 0) ”
  &&  (listrep u )
  **  (listrep z )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (lseg x t )
.

Definition multi_append_partial_solve_wit_6 := 
forall (x: Z) (z: Z) (y: Z) (u: Z) (v: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (u = 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (listrep y )
  **  (listrep z )
  **  (listrep u )
  **  (lseg x t )
|--
  “ (t <> 0) ” 
  &&  “ (u = 0) ”
  &&  (listrep y )
  **  (listrep z )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  (lseg x t )
.

Module Type VC_Correct.

Include sll_shape_Strategy_Correct.

Axiom proof_of_sll_copy_safety_wit_1 : sll_copy_safety_wit_1.
Axiom proof_of_sll_copy_safety_wit_2 : sll_copy_safety_wit_2.
Axiom proof_of_sll_copy_entail_wit_1 : sll_copy_entail_wit_1.
Axiom proof_of_sll_copy_entail_wit_2 : sll_copy_entail_wit_2.
Axiom proof_of_sll_copy_return_wit_1 : sll_copy_return_wit_1.
Axiom proof_of_sll_copy_return_wit_2 : sll_copy_return_wit_2.
Axiom proof_of_sll_copy_partial_solve_wit_1 : sll_copy_partial_solve_wit_1.
Axiom proof_of_sll_copy_partial_solve_wit_2_pure : sll_copy_partial_solve_wit_2_pure.
Axiom proof_of_sll_copy_partial_solve_wit_2 : sll_copy_partial_solve_wit_2.
Axiom proof_of_sll_copy_partial_solve_wit_3 : sll_copy_partial_solve_wit_3.
Axiom proof_of_sll_copy_partial_solve_wit_4_pure : sll_copy_partial_solve_wit_4_pure.
Axiom proof_of_sll_copy_partial_solve_wit_4 : sll_copy_partial_solve_wit_4.
Axiom proof_of_sll_free_entail_wit_1 : sll_free_entail_wit_1.
Axiom proof_of_sll_free_entail_wit_2 : sll_free_entail_wit_2.
Axiom proof_of_sll_free_return_wit_1 : sll_free_return_wit_1.
Axiom proof_of_sll_free_partial_solve_wit_1 : sll_free_partial_solve_wit_1.
Axiom proof_of_sll_free_partial_solve_wit_2 : sll_free_partial_solve_wit_2.
Axiom proof_of_reverse_safety_wit_1 : reverse_safety_wit_1.
Axiom proof_of_reverse_entail_wit_1 : reverse_entail_wit_1.
Axiom proof_of_reverse_entail_wit_2 : reverse_entail_wit_2.
Axiom proof_of_reverse_return_wit_1 : reverse_return_wit_1.
Axiom proof_of_reverse_partial_solve_wit_1 : reverse_partial_solve_wit_1.
Axiom proof_of_append_safety_wit_1 : append_safety_wit_1.
Axiom proof_of_append_entail_wit_1 : append_entail_wit_1.
Axiom proof_of_append_entail_wit_2 : append_entail_wit_2.
Axiom proof_of_append_return_wit_1 : append_return_wit_1.
Axiom proof_of_append_return_wit_2 : append_return_wit_2.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_merge_safety_wit_1 : merge_safety_wit_1.
Axiom proof_of_merge_safety_wit_2 : merge_safety_wit_2.
Axiom proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Axiom proof_of_merge_entail_wit_2 : merge_entail_wit_2.
Axiom proof_of_merge_return_wit_1 : merge_return_wit_1.
Axiom proof_of_merge_return_wit_2 : merge_return_wit_2.
Axiom proof_of_merge_return_wit_3 : merge_return_wit_3.
Axiom proof_of_merge_partial_solve_wit_1 : merge_partial_solve_wit_1.
Axiom proof_of_merge_partial_solve_wit_2 : merge_partial_solve_wit_2.
Axiom proof_of_multi_append_safety_wit_1 : multi_append_safety_wit_1.
Axiom proof_of_multi_append_entail_wit_1 : multi_append_entail_wit_1.
Axiom proof_of_multi_append_entail_wit_2 : multi_append_entail_wit_2.
Axiom proof_of_multi_append_return_wit_1 : multi_append_return_wit_1.
Axiom proof_of_multi_append_return_wit_2 : multi_append_return_wit_2.
Axiom proof_of_multi_append_return_wit_3 : multi_append_return_wit_3.
Axiom proof_of_multi_append_partial_solve_wit_1 : multi_append_partial_solve_wit_1.
Axiom proof_of_multi_append_partial_solve_wit_2 : multi_append_partial_solve_wit_2.
Axiom proof_of_multi_append_partial_solve_wit_3 : multi_append_partial_solve_wit_3.
Axiom proof_of_multi_append_partial_solve_wit_4 : multi_append_partial_solve_wit_4.
Axiom proof_of_multi_append_partial_solve_wit_5 : multi_append_partial_solve_wit_5.
Axiom proof_of_multi_append_partial_solve_wit_6 : multi_append_partial_solve_wit_6.

End VC_Correct.
