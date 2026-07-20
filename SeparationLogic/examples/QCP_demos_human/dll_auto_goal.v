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
Require Import SimpleC.EE.QCP_demos_human.dll_shape_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import dll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import dll_shape_strategy_proof.

(*----- Function dll_copy -----*)

Definition dll_copy_safety_wit_1 := 
forall (x_pre: Z) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep_shape x_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dll_copy_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (dlistrep_shape x_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dll_copy_entail_wit_1 := 
forall (x_pre: Z) (x: Z) (y: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (retval_prev = 0)) (PreH4 : (x_pre <> 0)) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> retval_prev)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
|--
  EX (t_prev: Z)  (p_prev: Z)  (v: Z)  (t_next: Z) ,
  “ (retval <> 0) ” 
  &&  “ (t_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (retval_prev = 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev y )
  **  (dlistrep_shape y p_prev )
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape retval 0 t_prev retval )
.

Definition dll_copy_entail_wit_2 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev_2: Z) (p_prev_2: Z) (p: Z) (v_2: Z) (t_next_2: Z) (t: Z) (x: Z) (y_2: Z) (retval_prev_2: Z) (retval_next_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_next_2 = 0)) (PreH3 : (retval_prev_2 = 0)) (PreH4 : (t <> 0)) (PreH5 : (t_next_2 = 0)) (PreH6 : (retval <> 0)) (PreH7 : (retval_next = 0)) (PreH8 : (retval_prev = 0)) (PreH9 : (x_pre <> 0)) (PreH10 : (p <> 0)) ,
  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next_2)
  **  ((&((retval_2)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval_2)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  (dllseg_shape x_pre 0 p_prev_2 p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape y 0 t_prev_2 t )
|--
  EX (t_prev: Z)  (p_prev: Z)  (v: Z)  (t_next: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (t_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (retval_prev = 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev y_2 )
  **  (dlistrep_shape y_2 p_prev )
  **  ((&((retval_2)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev retval_2 )
.

Definition dll_copy_return_wit_1 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (retval_prev = 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p = 0)) ,
  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
|--
  (dlistrep_shape y 0 )
  **  (dlistrep_shape x_pre 0 )
.

Definition dll_copy_return_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (dlistrep_shape x_pre 0 )
|--
  (dlistrep_shape 0 0 )
  **  (dlistrep_shape x_pre 0 )
.

Definition dll_copy_partial_solve_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (dlistrep_shape x_pre 0 )
|--
  EX (x: Z)  (y: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
.

Definition dll_copy_partial_solve_wit_2_pure := 
forall (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (x = x) ”
.

Definition dll_copy_partial_solve_wit_2_aux := 
forall (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
|--
  “ (x = x) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
.

Definition dll_copy_partial_solve_wit_2 := dll_copy_partial_solve_wit_2_pure -> dll_copy_partial_solve_wit_2_aux.

Definition dll_copy_partial_solve_wit_3 := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (retval_prev = 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p <> 0)) ,
  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
|--
  EX (x: Z)  (y_2: Z) ,
  “ (t <> 0) ” 
  &&  “ (t_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (retval_prev = 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p <> 0) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
.

Definition dll_copy_partial_solve_wit_4_pure := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (retval_prev = 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((( &( "t" ) )) # Ptr  |-> t)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  (dllseg_shape y 0 t_prev t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (x = x) ”
.

Definition dll_copy_partial_solve_wit_4_aux := 
forall (x_pre: Z) (retval_prev: Z) (retval_next: Z) (retval: Z) (y: Z) (t_prev: Z) (p_prev: Z) (p: Z) (v: Z) (t_next: Z) (t: Z) (x: Z) (y_2: Z) (PreH1 : (t <> 0)) (PreH2 : (t_next = 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_next = 0)) (PreH5 : (retval_prev = 0)) (PreH6 : (x_pre <> 0)) (PreH7 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
|--
  “ (x = x) ” 
  &&  “ (t <> 0) ” 
  &&  “ (t_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (retval_prev = 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (p <> 0) ”
  &&  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_2 p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  (dllseg_shape x_pre 0 p_prev p )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape y 0 t_prev t )
.

Definition dll_copy_partial_solve_wit_4 := dll_copy_partial_solve_wit_4_pure -> dll_copy_partial_solve_wit_4_aux.

(*----- Function dll_free -----*)

Definition dll_free_entail_wit_1 := 
forall (x_pre: Z) ,
  (dlistrep_shape x_pre 0 )
|--
  EX (prev: Z) ,
  (dlistrep_shape x_pre prev )
.

Definition dll_free_entail_wit_2 := 
forall (x: Z) (y: Z) (PreH1 : (x <> 0)) ,
  (dlistrep_shape y x )
  **  ((( &( "y" ) )) # Ptr  |-> y)
|--
  EX (prev: Z) ,
  (dlistrep_shape y prev )
  **  ((( &( "y" ) )) # Ptr  |->_)
.

Definition dll_free_return_wit_1 := 
forall (x: Z) (prev: Z) (PreH1 : (x = 0)) ,
  (dlistrep_shape x prev )
|--
  TT && emp 
.

Definition dll_free_partial_solve_wit_1 := 
forall (x: Z) (prev: Z) (PreH1 : (x <> 0)) ,
  (dlistrep_shape x prev )
|--
  EX (y: Z)  (x_2: Z) ,
  “ (x <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x )
  **  ((&((x)  # "list" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
.

Definition dll_free_partial_solve_wit_2 := 
forall (x: Z) (prev: Z) (x_2: Z) (y: Z) (PreH1 : (x <> 0)) ,
  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x )
  **  ((&((x)  # "list" ->ₛ "prev")) # Ptr  |-> prev)
  **  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
|--
  “ (x <> 0) ”
  &&  ((&((x)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((x)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((x)  # "list" ->ₛ "prev")) # Ptr  |-> prev)
  **  (dlistrep_shape y x )
.

(*----- Function reverse -----*)

Definition reverse_safety_wit_1 := 
forall (p_pre: Z) ,
  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (dlistrep_shape p_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_entail_wit_1 := 
forall (p_pre: Z) ,
  (dlistrep_shape p_pre 0 )
|--
  (dlistrep_shape 0 p_pre )
  **  (dlistrep_shape p_pre 0 )
.

Definition reverse_entail_wit_2 := 
forall (w: Z) (v: Z) (x: Z) (y: Z) (PreH1 : (v <> 0)) ,
  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (dlistrep_shape y v )
  **  ((&((v)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape w v )
  **  ((( &( "t" ) )) # Ptr  |-> y)
|--
  (dlistrep_shape v y )
  **  (dlistrep_shape y v )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition reverse_return_wit_1 := 
forall (w: Z) (v: Z) (PreH1 : (v = 0)) ,
  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
|--
  (dlistrep_shape w 0 )
.

Definition reverse_partial_solve_wit_1 := 
forall (w: Z) (v: Z) (PreH1 : (v <> 0)) ,
  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
|--
  EX (y: Z)  (x: Z) ,
  “ (v <> 0) ”
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y v )
  **  ((&((v)  # "list" ->ₛ "prev")) # Ptr  |-> w)
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape w v )
.

(*----- Function append -----*)

Definition append_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition append_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_pre 0 )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y = t_next) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev x_pre )
  **  (dlistrep_shape y_pre 0 )
.

Definition append_entail_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (t_prev_2: Z) (t_next_2: Z) (u: Z) (v_2: Z) (t: Z) (x: Z) (y: Z) (PreH1 : (u = t_next_2)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) ,
  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next_2)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape x_pre 0 t_prev_2 t )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y = t_next) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev u )
  **  (dlistrep_shape y_pre 0 )
.

Definition append_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) (x: Z) (y: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) (PreH5 : (y_pre <> 0)) ,
  ((&((y_pre)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y y_pre )
  **  ((&((y_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition append_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) (PreH5 : (y_pre = 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
|--
  (dlistrep_shape x_pre 0 )
.

Definition append_return_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
|--
  (dlistrep_shape y_pre 0 )
.

Definition append_partial_solve_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_pre 0 )
.

Definition append_partial_solve_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
.

Definition append_partial_solve_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (v: Z) (t: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) (PreH5 : (y_pre <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  (dlistrep_shape y_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (y_pre <> 0) ”
  &&  ((&((y_pre)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y y_pre )
  **  ((&((y_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((y_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_pre)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

(*----- Function iter -----*)

Definition iter_entail_wit_1 := 
forall (l_pre: Z) ,
  (dlistrep_shape l_pre 0 )
|--
  EX (p_prev: Z) ,
  (dllseg_shape l_pre 0 p_prev l_pre )
  **  (dlistrep_shape l_pre p_prev )
.

Definition iter_entail_wit_2 := 
forall (l_pre: Z) (p_prev_2: Z) (p: Z) (x: Z) (y: Z) (PreH1 : (p <> 0)) ,
  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape l_pre 0 p_prev_2 p )
|--
  EX (p_prev: Z) ,
  (dllseg_shape l_pre 0 p_prev y )
  **  (dlistrep_shape y p_prev )
.

Definition iter_return_wit_1 := 
forall (l_pre: Z) (p_prev: Z) (p: Z) (PreH1 : (p = 0)) ,
  (dllseg_shape l_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
|--
  (dlistrep_shape l_pre 0 )
.

Definition iter_partial_solve_wit_1 := 
forall (l_pre: Z) (p_prev: Z) (p: Z) (PreH1 : (p <> 0)) ,
  (dllseg_shape l_pre 0 p_prev p )
  **  (dlistrep_shape p p_prev )
|--
  EX (y: Z)  (x: Z) ,
  “ (p <> 0) ”
  &&  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y p )
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg_shape l_pre 0 p_prev p )
.

(*----- Function iter_back -----*)

Definition iter_back_safety_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) (PreH1 : (head_pre <> 0)) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  (dllseg_shape head_pre 0 l_prev l_pre )
  **  (dlistrep_shape l_pre l_prev )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition iter_back_entail_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) (PreH1 : (l_pre <> 0)) (PreH2 : (head_pre <> 0)) ,
  (dllseg_shape head_pre 0 l_prev l_pre )
  **  (dlistrep_shape l_pre l_prev )
|--
  EX (p_next: Z)  (p_prev: Z)  (v: Z) ,
  “ (l_pre <> 0) ” 
  &&  “ (l_pre <> 0) ” 
  &&  “ (head_pre <> 0) ”
  &&  ((&((l_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((l_pre)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_pre 0 p_prev l_pre )
  **  ((&((l_pre)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next l_pre )
.

Definition iter_back_entail_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (p_next_2: Z) (p_prev_2: Z) (v_2: Z) (p: Z) (PreH1 : (p <> head_pre)) (PreH2 : (p <> 0)) (PreH3 : (l_pre <> 0)) (PreH4 : (head_pre <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg_shape head_pre 0 p_prev_2 p )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  (dlistrep_shape p_next_2 p )
|--
  EX (p_next: Z)  (p_prev: Z)  (v: Z) ,
  “ (p_prev_2 <> 0) ” 
  &&  “ (l_pre <> 0) ” 
  &&  “ (head_pre <> 0) ”
  &&  ((&((p_prev_2)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((p_prev_2)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_pre 0 p_prev p_prev_2 )
  **  ((&((p_prev_2)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next p_prev_2 )
.

Definition iter_back_return_wit_1 := 
forall (head_pre: Z) (l_pre: Z) (p_next: Z) (p_prev: Z) (v: Z) (p: Z) (PreH1 : (p = head_pre)) (PreH2 : (p <> 0)) (PreH3 : (l_pre <> 0)) (PreH4 : (head_pre <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_pre 0 p_prev p )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next p )
|--
  (dlistrep_shape p 0 )
.

Definition iter_back_return_wit_2 := 
forall (head_pre: Z) (l_pre: Z) (l_prev: Z) (PreH1 : (l_pre = 0)) (PreH2 : (head_pre <> 0)) ,
  (dllseg_shape head_pre 0 l_prev l_pre )
  **  (dlistrep_shape l_pre l_prev )
|--
  (dlistrep_shape head_pre 0 )
.

(*----- Function iter_back_2 -----*)

Definition iter_back_2_entail_wit_1 := 
forall (tail_pre: Z) (head_pre: Z) (tail_prev: Z) (tail_node: Z) (head_node: Z) (PreH1 : (head_node <> tail_node)) (PreH2 : (head_node <> 0)) (PreH3 : (tail_node <> 0)) ,
  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
  **  (dllseg_shape head_node 0 tail_prev tail_node )
  **  (dlistrep_shape tail_node tail_prev )
|--
  EX (p_next: Z)  (p_prev: Z)  (v: Z) ,
  “ (tail_node <> 0) ” 
  &&  “ (head_node <> tail_node) ” 
  &&  “ (head_node <> 0) ” 
  &&  “ (tail_node <> 0) ”
  &&  ((&((tail_node)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail_node)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_node 0 p_prev tail_node )
  **  ((&((tail_node)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next tail_node )
  **  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
.

Definition iter_back_2_entail_wit_2 := 
forall (tail_pre: Z) (head_pre: Z) (tail_node: Z) (head_node: Z) (p_next_2: Z) (p_prev_2: Z) (v_2: Z) (p: Z) (PreH1 : (p <> head_node)) (PreH2 : (p <> 0)) (PreH3 : (head_node <> tail_node)) (PreH4 : (head_node <> 0)) (PreH5 : (tail_node <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev_2)
  **  (dllseg_shape head_node 0 p_prev_2 p )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next_2)
  **  (dlistrep_shape p_next_2 p )
  **  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
|--
  EX (p_next: Z)  (p_prev: Z)  (v: Z) ,
  “ (p_prev_2 <> 0) ” 
  &&  “ (head_node <> tail_node) ” 
  &&  “ (head_node <> 0) ” 
  &&  “ (tail_node <> 0) ”
  &&  ((&((p_prev_2)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((p_prev_2)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_node 0 p_prev p_prev_2 )
  **  ((&((p_prev_2)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next p_prev_2 )
  **  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
.

Definition iter_back_2_return_wit_1 := 
forall (tail_pre: Z) (head_pre: Z) (tail_node: Z) (head_node: Z) (p_next: Z) (p_prev: Z) (v: Z) (p: Z) (PreH1 : (p = head_node)) (PreH2 : (p <> 0)) (PreH3 : (head_node <> tail_node)) (PreH4 : (head_node <> 0)) (PreH5 : (tail_node <> 0)) ,
  ((&((p)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> p_prev)
  **  (dllseg_shape head_node 0 p_prev p )
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> p_next)
  **  (dlistrep_shape p_next p )
  **  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
|--
  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
  **  (dlistrep_shape p 0 )
.

Definition iter_back_2_return_wit_2 := 
forall (tail_pre: Z) (head_pre: Z) (tail_prev: Z) (tail_node: Z) (head_node: Z) (PreH1 : (head_node = tail_node)) (PreH2 : (head_node <> 0)) (PreH3 : (tail_node <> 0)) ,
  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
  **  (dllseg_shape head_node 0 tail_prev tail_node )
  **  (dlistrep_shape tail_node tail_prev )
|--
  ((head_pre) # Ptr  |-> head_node)
  **  ((tail_pre) # Ptr  |-> tail_node)
  **  (dlistrep_shape tail_node 0 )
.

(*----- Function multi_merge -----*)

Definition multi_merge_safety_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) ,
  ((( &( "u" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "z" ) )) # Ptr  |-> z_pre)
  **  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_merge_safety_wit_2 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) ,
  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "t" ) )) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> z)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_merge_safety_wit_3 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (x_3: Z) (y_4: Z) (x_4: Z) (y_5: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y_5 <> 0)) ,
  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_5 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "t" ) )) # Ptr  |-> z)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> y_5)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_merge_safety_wit_4 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (x_3: Z) (y_4: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 = 0)) (PreH7 : (z <> 0)) (PreH8 : (y_4 <> 0)) ,
  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_4 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((( &( "t" ) )) # Ptr  |-> z)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((( &( "u" ) )) # Ptr  |-> u)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((( &( "y" ) )) # Ptr  |-> y_2)
  **  ((( &( "z" ) )) # Ptr  |-> y_4)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_merge_entail_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (x: Z) (y: Z) (PreH1 : (x_pre <> 0)) ,
  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y = t_next) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev x_pre )
.

Definition multi_merge_entail_wit_2_1 := 
forall (x_pre: Z) (t_prev_2: Z) (z: Z) (y_4: Z) (t_next_2: Z) (u: Z) (t: Z) (v_2: Z) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (x_3: Z) (y_5: Z) (x_4: Z) (y_3: Z) (x_5: Z) (y_6: Z) (PreH1 : (u = t_next_2)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y_4 <> 0)) (PreH6 : (y <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y_3 <> 0)) ,
  ((&((y_3)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_6 y_3 )
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_6)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_5)
  **  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y_4)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_5 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y_4)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y_4)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y_4)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape x_pre 0 t_prev_2 t )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y_2 = t_next) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape y_3 0 )
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev u )
.

Definition multi_merge_entail_wit_2_2 := 
forall (x_pre: Z) (t_prev_2: Z) (z: Z) (y_4: Z) (t_next_2: Z) (u: Z) (t: Z) (v_2: Z) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (x_3: Z) (y_3: Z) (x_4: Z) (y_5: Z) (PreH1 : (u = t_next_2)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y_4 <> 0)) (PreH6 : (y = 0)) (PreH7 : (z <> 0)) (PreH8 : (y_3 <> 0)) ,
  ((&((y_3)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_5 y_3 )
  **  ((&((y_3)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((y_3)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y_4)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y_4)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y_4)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y_4)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape x_pre 0 t_prev_2 t )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y_2 = t_next) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape y_3 0 )
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev u )
.

Definition multi_merge_entail_wit_2_3 := 
forall (x_pre: Z) (t_prev_2: Z) (z: Z) (y_4: Z) (t_next_2: Z) (u: Z) (t: Z) (v_2: Z) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (x_3: Z) (y_5: Z) (x_4: Z) (y_3: Z) (PreH1 : (u = t_next_2)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y_4 <> 0)) (PreH6 : (y <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y_3 = 0)) ,
  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y_4)
  **  (dlistrep_shape y_3 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_5 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y_4)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y_4)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y_4)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape x_pre 0 t_prev_2 t )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y_2 = t_next) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape y_3 0 )
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev u )
.

Definition multi_merge_entail_wit_2_4 := 
forall (x_pre: Z) (t_prev_2: Z) (z: Z) (y_4: Z) (t_next_2: Z) (u: Z) (t: Z) (v_2: Z) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (x_3: Z) (y_3: Z) (PreH1 : (u = t_next_2)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y_4 <> 0)) (PreH6 : (y = 0)) (PreH7 : (z <> 0)) (PreH8 : (y_3 = 0)) ,
  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y_4)
  **  (dlistrep_shape y_3 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> u)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y_4)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y_4)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y_4)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev_2)
  **  (dllseg_shape x_pre 0 t_prev_2 t )
|--
  EX (t_prev: Z)  (t_next: Z)  (v: Z) ,
  “ (y_2 = t_next) ” 
  &&  “ (u <> 0) ” 
  &&  “ (x_pre <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape y_3 0 )
  **  (dlistrep_shape y_2 u )
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev u )
.

Definition multi_merge_return_wit_1 := 
forall (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (retval: Z) (x: Z) (y: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) (PreH5 : (retval <> 0)) ,
  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y retval )
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition multi_merge_return_wit_2 := 
forall (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (retval: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) (PreH5 : (retval = 0)) ,
  (dlistrep_shape retval 0 )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition multi_merge_return_wit_3 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (retval: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) (PreH7 : (z = 0)) ,
  (dlistrep_shape retval y )
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition multi_merge_return_wit_4 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (retval: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 = 0)) (PreH7 : (z = 0)) ,
  (dlistrep_shape retval y )
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition multi_merge_return_wit_5 := 
forall (x_pre: Z) (t_prev: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (retval: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y = 0)) ,
  (dlistrep_shape retval t )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  (dlistrep_shape x_pre 0 )
.

Definition multi_merge_return_wit_6 := 
forall (x_pre: Z) (retval: Z) (PreH1 : (x_pre = 0)) ,
  (dlistrep_shape retval 0 )
|--
  (dlistrep_shape retval 0 )
.

Definition multi_merge_partial_solve_wit_1 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre = 0)) ,
  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
|--
  “ (x_pre = 0) ”
  &&  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
.

Definition multi_merge_partial_solve_wit_2 := 
forall (z_pre: Z) (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre <> 0)) ,
  (dlistrep_shape x_pre 0 )
  **  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
|--
  EX (y: Z)  (x: Z) ,
  “ (x_pre <> 0) ”
  &&  ((&((x_pre)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y x_pre )
  **  ((&((x_pre)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((x_pre)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dlistrep_shape y_pre 0 )
  **  (dlistrep_shape z_pre 0 )
.

Definition multi_merge_partial_solve_wit_3 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape z 0 )
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_2: Z)  (x: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_4 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) ,
  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_3: Z)  (x_2: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_5 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) ,
  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_4: Z)  (x_3: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 <> 0) ”
  &&  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_6 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y = 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape z 0 )
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y = 0) ”
  &&  (dlistrep_shape u t )
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_7 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (x_3: Z) (y_4: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) (PreH7 : (z <> 0)) ,
  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_5: Z)  (x_4: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (z <> 0) ”
  &&  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_5 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_8 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 = 0)) (PreH7 : (z <> 0)) ,
  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_4: Z)  (x_3: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 = 0) ” 
  &&  “ (z <> 0) ”
  &&  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_4 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_9 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (x_3: Z) (y_4: Z) (x_4: Z) (y_5: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) (PreH7 : (z <> 0)) (PreH8 : (y_5 <> 0)) ,
  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_5 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_6: Z)  (x_5: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_5 <> 0) ”
  &&  ((&((y_5)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_6 y_5 )
  **  ((&((y_5)  # "list" ->ₛ "next")) # Ptr  |-> y_6)
  **  ((&((y_5)  # "list" ->ₛ "data")) # Int  |-> x_5)
  **  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_10 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (x_3: Z) (y_4: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 = 0)) (PreH7 : (z <> 0)) (PreH8 : (y_4 <> 0)) ,
  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_4 z )
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y_5: Z)  (x_4: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 = 0) ” 
  &&  “ (z <> 0) ” 
  &&  “ (y_4 <> 0) ”
  &&  ((&((y_4)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y_5 y_4 )
  **  ((&((y_4)  # "list" ->ₛ "next")) # Ptr  |-> y_5)
  **  ((&((y_4)  # "list" ->ₛ "data")) # Int  |-> x_4)
  **  ((&((z)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  ((&((z)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((z)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> z)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> z)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_11 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (x_3: Z) (y_4: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 <> 0)) (PreH7 : (z = 0)) ,
  ((&((y_2)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  (dlistrep_shape y_4 y_2 )
  **  ((&((y_2)  # "list" ->ₛ "next")) # Ptr  |-> y_4)
  **  ((&((y_2)  # "list" ->ₛ "data")) # Int  |-> x_3)
  **  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 <> 0) ” 
  &&  “ (z = 0) ”
  &&  (dlistrep_shape u y )
  **  (dlistrep_shape y_2 0 )
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_12 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (x: Z) (y_2: Z) (x_2: Z) (y_3: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u <> 0)) (PreH5 : (y <> 0)) (PreH6 : (y_2 = 0)) (PreH7 : (z = 0)) ,
  ((&((u)  # "list" ->ₛ "prev")) # Ptr  |-> y)
  **  (dlistrep_shape y_3 u )
  **  ((&((u)  # "list" ->ₛ "next")) # Ptr  |-> y_3)
  **  ((&((u)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u <> 0) ” 
  &&  “ (y <> 0) ” 
  &&  “ (y_2 = 0) ” 
  &&  “ (z = 0) ”
  &&  (dlistrep_shape u y )
  **  (dlistrep_shape y_2 0 )
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> t)
  **  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_13 := 
forall (x_pre: Z) (t_prev: Z) (z: Z) (y: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) ,
  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  (dlistrep_shape y 0 )
  **  (dlistrep_shape z 0 )
  **  (dlistrep_shape u t )
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u = 0) ”
  &&  (dlistrep_shape y 0 )
  **  (dlistrep_shape z 0 )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> t_next)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

Definition multi_merge_partial_solve_wit_14 := 
forall (x_pre: Z) (t_prev: Z) (t_next: Z) (u: Z) (t: Z) (v: Z) (retval: Z) (PreH1 : (u = t_next)) (PreH2 : (t <> 0)) (PreH3 : (x_pre <> 0)) (PreH4 : (u = 0)) (PreH5 : (retval <> 0)) ,
  (dlistrep_shape retval 0 )
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
|--
  EX (y: Z)  (x: Z) ,
  “ (u = t_next) ” 
  &&  “ (t <> 0) ” 
  &&  “ (x_pre <> 0) ” 
  &&  “ (u = 0) ” 
  &&  “ (retval <> 0) ”
  &&  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |->_)
  **  (dlistrep_shape y retval )
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> y)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((t)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((t)  # "list" ->ₛ "next")) # Ptr  |-> retval)
  **  ((&((t)  # "list" ->ₛ "prev")) # Ptr  |-> t_prev)
  **  (dllseg_shape x_pre 0 t_prev t )
.

(*----- Function multi_rev -----*)

Definition multi_rev_safety_wit_1 := 
forall (q_pre: Z) (p_pre: Z) ,
  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |->_)
  **  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (dlistrep_shape p_pre 0 )
  **  (dlistrep_shape q_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_rev_safety_wit_2 := 
forall (q_pre: Z) (p_pre: Z) ,
  ((( &( "y" ) )) # Ptr  |->_)
  **  ((( &( "x" ) )) # Ptr  |->_)
  **  ((( &( "v" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> 0)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (dlistrep_shape p_pre 0 )
  **  (dlistrep_shape q_pre 0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition multi_rev_safety_wit_3 := 
forall (q_pre: Z) (p_pre: Z) (x: Z) (y: Z) (w: Z) (v: Z) ,
  ((( &( "v" ) )) # Ptr  |-> v)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
  **  ((( &( "y" ) )) # Ptr  |-> y)
  **  ((( &( "x" ) )) # Ptr  |-> x)
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
  **  ((( &( "t" ) )) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition multi_rev_entail_wit_1 := 
forall (q_pre: Z) (p_pre: Z) ,
  (dlistrep_shape p_pre 0 )
  **  (dlistrep_shape q_pre 0 )
|--
  (dlistrep_shape 0 p_pre )
  **  (dlistrep_shape p_pre 0 )
  **  (dlistrep_shape 0 q_pre )
  **  (dlistrep_shape q_pre 0 )
.

Definition multi_rev_entail_wit_2_1 := 
forall (x: Z) (y: Z) (w: Z) (v: Z) (x_2: Z) (y_2: Z) (PreH1 : (v <> 0)) ,
  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> w)
  **  (dlistrep_shape y_2 v )
  **  ((&((v)  # "list" ->ₛ "prev")) # Ptr  |-> y_2)
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (dlistrep_shape w v )
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
  **  ((( &( "t" ) )) # Ptr  |-> y_2)
|--
  (dlistrep_shape v y_2 )
  **  (dlistrep_shape y_2 v )
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition multi_rev_entail_wit_2_2 := 
forall (x: Z) (y: Z) (w: Z) (v: Z) (x_2: Z) (y_2: Z) (PreH1 : (v = 0)) (PreH2 : (y <> 0)) ,
  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> x)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> y_2)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (dlistrep_shape w v )
  **  (dlistrep_shape x y )
  **  ((( &( "t" ) )) # Ptr  |-> y_2)
|--
  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
  **  (dlistrep_shape y y_2 )
  **  (dlistrep_shape y_2 y )
  **  ((( &( "t" ) )) # Ptr  |->_)
.

Definition multi_rev_return_wit_1 := 
forall (y: Z) (v: Z) (retval: Z) (PreH1 : (v = 0)) (PreH2 : (y = 0)) ,
  (dlistrep_shape retval 0 )
|--
  (dlistrep_shape retval 0 )
.

Definition multi_rev_partial_solve_wit_1 := 
forall (x: Z) (y: Z) (w: Z) (v: Z) (PreH1 : (v <> 0)) ,
  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
|--
  EX (y_2: Z)  (x_2: Z) ,
  “ (v <> 0) ”
  &&  ((&((v)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (dlistrep_shape y_2 v )
  **  ((&((v)  # "list" ->ₛ "prev")) # Ptr  |-> w)
  **  ((&((v)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (dlistrep_shape w v )
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
.

Definition multi_rev_partial_solve_wit_2 := 
forall (x: Z) (y: Z) (w: Z) (v: Z) (PreH1 : (v = 0)) (PreH2 : (y <> 0)) ,
  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
|--
  EX (y_2: Z)  (x_2: Z) ,
  “ (v = 0) ” 
  &&  “ (y <> 0) ”
  &&  ((&((y)  # "list" ->ₛ "next")) # Ptr  |-> y_2)
  **  (dlistrep_shape y_2 y )
  **  ((&((y)  # "list" ->ₛ "prev")) # Ptr  |-> x)
  **  ((&((y)  # "list" ->ₛ "data")) # Int  |-> x_2)
  **  (dlistrep_shape w v )
  **  (dlistrep_shape x y )
.

Definition multi_rev_partial_solve_wit_3 := 
forall (x: Z) (y: Z) (w: Z) (v: Z) (PreH1 : (v = 0)) (PreH2 : (y = 0)) ,
  (dlistrep_shape w v )
  **  (dlistrep_shape v w )
  **  (dlistrep_shape x y )
  **  (dlistrep_shape y x )
|--
  “ (v = 0) ” 
  &&  “ (y = 0) ”
  &&  (dlistrep_shape w 0 )
  **  (dlistrep_shape x 0 )
.

Module Type VC_Correct.

Include dll_shape_Strategy_Correct.

Axiom proof_of_dll_copy_safety_wit_1 : dll_copy_safety_wit_1.
Axiom proof_of_dll_copy_safety_wit_2 : dll_copy_safety_wit_2.
Axiom proof_of_dll_copy_entail_wit_1 : dll_copy_entail_wit_1.
Axiom proof_of_dll_copy_entail_wit_2 : dll_copy_entail_wit_2.
Axiom proof_of_dll_copy_return_wit_1 : dll_copy_return_wit_1.
Axiom proof_of_dll_copy_return_wit_2 : dll_copy_return_wit_2.
Axiom proof_of_dll_copy_partial_solve_wit_1 : dll_copy_partial_solve_wit_1.
Axiom proof_of_dll_copy_partial_solve_wit_2_pure : dll_copy_partial_solve_wit_2_pure.
Axiom proof_of_dll_copy_partial_solve_wit_2 : dll_copy_partial_solve_wit_2.
Axiom proof_of_dll_copy_partial_solve_wit_3 : dll_copy_partial_solve_wit_3.
Axiom proof_of_dll_copy_partial_solve_wit_4_pure : dll_copy_partial_solve_wit_4_pure.
Axiom proof_of_dll_copy_partial_solve_wit_4 : dll_copy_partial_solve_wit_4.
Axiom proof_of_dll_free_entail_wit_1 : dll_free_entail_wit_1.
Axiom proof_of_dll_free_entail_wit_2 : dll_free_entail_wit_2.
Axiom proof_of_dll_free_return_wit_1 : dll_free_return_wit_1.
Axiom proof_of_dll_free_partial_solve_wit_1 : dll_free_partial_solve_wit_1.
Axiom proof_of_dll_free_partial_solve_wit_2 : dll_free_partial_solve_wit_2.
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
Axiom proof_of_append_return_wit_3 : append_return_wit_3.
Axiom proof_of_append_partial_solve_wit_1 : append_partial_solve_wit_1.
Axiom proof_of_append_partial_solve_wit_2 : append_partial_solve_wit_2.
Axiom proof_of_append_partial_solve_wit_3 : append_partial_solve_wit_3.
Axiom proof_of_iter_entail_wit_1 : iter_entail_wit_1.
Axiom proof_of_iter_entail_wit_2 : iter_entail_wit_2.
Axiom proof_of_iter_return_wit_1 : iter_return_wit_1.
Axiom proof_of_iter_partial_solve_wit_1 : iter_partial_solve_wit_1.
Axiom proof_of_iter_back_safety_wit_1 : iter_back_safety_wit_1.
Axiom proof_of_iter_back_entail_wit_1 : iter_back_entail_wit_1.
Axiom proof_of_iter_back_entail_wit_2 : iter_back_entail_wit_2.
Axiom proof_of_iter_back_return_wit_1 : iter_back_return_wit_1.
Axiom proof_of_iter_back_return_wit_2 : iter_back_return_wit_2.
Axiom proof_of_iter_back_2_entail_wit_1 : iter_back_2_entail_wit_1.
Axiom proof_of_iter_back_2_entail_wit_2 : iter_back_2_entail_wit_2.
Axiom proof_of_iter_back_2_return_wit_1 : iter_back_2_return_wit_1.
Axiom proof_of_iter_back_2_return_wit_2 : iter_back_2_return_wit_2.
Axiom proof_of_multi_merge_safety_wit_1 : multi_merge_safety_wit_1.
Axiom proof_of_multi_merge_safety_wit_2 : multi_merge_safety_wit_2.
Axiom proof_of_multi_merge_safety_wit_3 : multi_merge_safety_wit_3.
Axiom proof_of_multi_merge_safety_wit_4 : multi_merge_safety_wit_4.
Axiom proof_of_multi_merge_entail_wit_1 : multi_merge_entail_wit_1.
Axiom proof_of_multi_merge_entail_wit_2_1 : multi_merge_entail_wit_2_1.
Axiom proof_of_multi_merge_entail_wit_2_2 : multi_merge_entail_wit_2_2.
Axiom proof_of_multi_merge_entail_wit_2_3 : multi_merge_entail_wit_2_3.
Axiom proof_of_multi_merge_entail_wit_2_4 : multi_merge_entail_wit_2_4.
Axiom proof_of_multi_merge_return_wit_1 : multi_merge_return_wit_1.
Axiom proof_of_multi_merge_return_wit_2 : multi_merge_return_wit_2.
Axiom proof_of_multi_merge_return_wit_3 : multi_merge_return_wit_3.
Axiom proof_of_multi_merge_return_wit_4 : multi_merge_return_wit_4.
Axiom proof_of_multi_merge_return_wit_5 : multi_merge_return_wit_5.
Axiom proof_of_multi_merge_return_wit_6 : multi_merge_return_wit_6.
Axiom proof_of_multi_merge_partial_solve_wit_1 : multi_merge_partial_solve_wit_1.
Axiom proof_of_multi_merge_partial_solve_wit_2 : multi_merge_partial_solve_wit_2.
Axiom proof_of_multi_merge_partial_solve_wit_3 : multi_merge_partial_solve_wit_3.
Axiom proof_of_multi_merge_partial_solve_wit_4 : multi_merge_partial_solve_wit_4.
Axiom proof_of_multi_merge_partial_solve_wit_5 : multi_merge_partial_solve_wit_5.
Axiom proof_of_multi_merge_partial_solve_wit_6 : multi_merge_partial_solve_wit_6.
Axiom proof_of_multi_merge_partial_solve_wit_7 : multi_merge_partial_solve_wit_7.
Axiom proof_of_multi_merge_partial_solve_wit_8 : multi_merge_partial_solve_wit_8.
Axiom proof_of_multi_merge_partial_solve_wit_9 : multi_merge_partial_solve_wit_9.
Axiom proof_of_multi_merge_partial_solve_wit_10 : multi_merge_partial_solve_wit_10.
Axiom proof_of_multi_merge_partial_solve_wit_11 : multi_merge_partial_solve_wit_11.
Axiom proof_of_multi_merge_partial_solve_wit_12 : multi_merge_partial_solve_wit_12.
Axiom proof_of_multi_merge_partial_solve_wit_13 : multi_merge_partial_solve_wit_13.
Axiom proof_of_multi_merge_partial_solve_wit_14 : multi_merge_partial_solve_wit_14.
Axiom proof_of_multi_rev_safety_wit_1 : multi_rev_safety_wit_1.
Axiom proof_of_multi_rev_safety_wit_2 : multi_rev_safety_wit_2.
Axiom proof_of_multi_rev_safety_wit_3 : multi_rev_safety_wit_3.
Axiom proof_of_multi_rev_entail_wit_1 : multi_rev_entail_wit_1.
Axiom proof_of_multi_rev_entail_wit_2_1 : multi_rev_entail_wit_2_1.
Axiom proof_of_multi_rev_entail_wit_2_2 : multi_rev_entail_wit_2_2.
Axiom proof_of_multi_rev_return_wit_1 : multi_rev_return_wit_1.
Axiom proof_of_multi_rev_partial_solve_wit_1 : multi_rev_partial_solve_wit_1.
Axiom proof_of_multi_rev_partial_solve_wit_2 : multi_rev_partial_solve_wit_2.
Axiom proof_of_multi_rev_partial_solve_wit_3 : multi_rev_partial_solve_wit_3.

End VC_Correct.
