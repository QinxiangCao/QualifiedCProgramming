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
Require Import SimpleC.EE.QCP_demos_human.sll_shape_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_human Require Import sll_shape_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_shape_strategy_proof.

(*----- Function arr_sum -----*)

Definition arr_sum_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "ret" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.full_shape a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "ret" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.full_shape a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arr_sum_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (i: Z) (v: Z) (x: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
  **  ((( &( "ret" ) )) # UInt  |-> (unsigned_last_nbits ((v + x )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arr_sum_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (UIntArray.full_shape a_pre n_pre )
.

Definition arr_sum_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (UIntArray.full_shape a_pre n_pre )
.

Definition arr_sum_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
|--
  (UIntArray.full_shape a_pre n_pre )
.

Definition arr_sum_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt  |-> x)
  **  (UIntArray.missing_i_shape a_pre i 0 n_pre )
.

(*----- Function array_copy1 -----*)

Definition array_copy1_safety_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
  **  (IntArray.undef_full dest_pre n_pre )
  **  (IntArray.full_shape src_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_copy1_safety_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape dest_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full_shape src_pre n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest" ) )) # Ptr  |-> dest_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_copy1_entail_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.undef_full dest_pre n_pre )
  **  (IntArray.full_shape src_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.seg_shape dest_pre 0 0 )
  **  (IntArray.undef_seg dest_pre 0 n_pre )
  **  (IntArray.full_shape src_pre n_pre )
.

Definition array_copy1_entail_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape dest_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full_shape src_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.seg_shape dest_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full_shape src_pre n_pre )
.

Definition array_copy1_return_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape dest_pre 0 i )
  **  (IntArray.undef_seg dest_pre i n_pre )
  **  (IntArray.full_shape src_pre n_pre )
|--
  (IntArray.full_shape dest_pre n_pre )
  **  (IntArray.full_shape src_pre n_pre )
.

Definition array_copy1_partial_solve_wit_1 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape dest_pre 0 i )
  **  (IntArray.undef_seg dest_pre i n_pre )
  **  (IntArray.full_shape src_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((src_pre + (i * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape src_pre i 0 n_pre )
  **  (IntArray.seg_shape dest_pre 0 i )
  **  (IntArray.undef_seg dest_pre i n_pre )
.

Definition array_copy1_partial_solve_wit_2 := 
forall (n_pre: Z) (src_pre: Z) (dest_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape src_pre n_pre )
  **  (IntArray.seg_shape dest_pre 0 i )
  **  (IntArray.undef_seg dest_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((dest_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dest_pre (i + 1 ) n_pre )
  **  (IntArray.full_shape src_pre n_pre )
  **  (IntArray.seg_shape dest_pre 0 i )
.

(*----- Function array_concat -----*)

Definition array_concat_safety_wit_1 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
  **  (IntArray.undef_full ret_pre (n_pre + m_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_concat_safety_wit_2 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.full_shape b_pre m_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_concat_safety_wit_3 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg_shape ret_pre 0 i )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_concat_safety_wit_4 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i_2: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (0 <= m_pre)) (PreH9 : ((n_pre + m_pre ) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg_shape ret_pre 0 (n_pre + i ) )
  **  (IntArray.undef_seg ret_pre (n_pre + i ) (n_pre + m_pre ) )
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  “ ((n_pre + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + i )) ”
.

Definition array_concat_safety_wit_5 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i_2: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= m_pre)) (PreH4 : (i_2 >= n_pre)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (0 <= m_pre)) (PreH9 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 ((n_pre + i ) + 1 ) )
  **  (IntArray.undef_seg ret_pre ((n_pre + i ) + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape b_pre m_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_concat_entail_wit_1 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
  **  (IntArray.undef_full ret_pre (n_pre + m_pre ) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg_shape ret_pre 0 0 )
  **  (IntArray.undef_seg ret_pre 0 (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
.

Definition array_concat_entail_wit_2 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg_shape ret_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
.

Definition array_concat_entail_wit_3 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 i )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg_shape ret_pre 0 (n_pre + 0 ) )
  **  (IntArray.undef_seg ret_pre (n_pre + 0 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
.

Definition array_concat_entail_wit_4 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (i_2: Z) (PreH1 : (i_2 < m_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= m_pre)) (PreH4 : (i >= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (0 <= m_pre)) (PreH9 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 ((n_pre + i_2 ) + 1 ) )
  **  (IntArray.undef_seg ret_pre ((n_pre + i_2 ) + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape b_pre m_pre )
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i_2 + 1 )) ” 
  &&  “ ((i_2 + 1 ) <= m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (IntArray.seg_shape ret_pre 0 (n_pre + (i_2 + 1 ) ) )
  **  (IntArray.undef_seg ret_pre (n_pre + (i_2 + 1 ) ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
.

Definition array_concat_return_wit_1 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (i_2: Z) (PreH1 : (i_2 >= m_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= m_pre)) (PreH4 : (i >= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (0 <= m_pre)) (PreH9 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 (n_pre + i_2 ) )
  **  (IntArray.undef_seg ret_pre (n_pre + i_2 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
  **  (IntArray.full_shape ret_pre (n_pre + m_pre ) )
.

Definition array_concat_partial_solve_wit_1 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 i )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape a_pre i 0 n_pre )
  **  (IntArray.seg_shape ret_pre 0 i )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full_shape b_pre m_pre )
.

Definition array_concat_partial_solve_wit_2 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.seg_shape ret_pre 0 i )
  **  (IntArray.undef_seg ret_pre i (n_pre + m_pre ) )
  **  (IntArray.full_shape b_pre m_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((ret_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ret_pre (i + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.seg_shape ret_pre 0 i )
  **  (IntArray.full_shape b_pre m_pre )
.

Definition array_concat_partial_solve_wit_3 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (i_2: Z) (PreH1 : (i_2 < m_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= m_pre)) (PreH4 : (i >= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (0 <= m_pre)) (PreH9 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.seg_shape ret_pre 0 (n_pre + i_2 ) )
  **  (IntArray.undef_seg ret_pre (n_pre + i_2 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre m_pre )
|--
  EX (x: Z) ,
  “ (i_2 < m_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((b_pre + (i_2 * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape b_pre i_2 0 m_pre )
  **  (IntArray.seg_shape ret_pre 0 (n_pre + i_2 ) )
  **  (IntArray.undef_seg ret_pre (n_pre + i_2 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
.

Definition array_concat_partial_solve_wit_4 := 
forall (m_pre: Z) (b_pre: Z) (n_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (i_2: Z) (PreH1 : (i_2 < m_pre)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 <= m_pre)) (PreH4 : (i >= n_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (0 <= m_pre)) (PreH9 : ((n_pre + m_pre ) < INT_MAX)) ,
  (IntArray.full_shape b_pre m_pre )
  **  (IntArray.seg_shape ret_pre 0 (n_pre + i_2 ) )
  **  (IntArray.undef_seg ret_pre (n_pre + i_2 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (i_2 < m_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= m_pre) ” 
  &&  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ ((n_pre + m_pre ) < INT_MAX) ”
  &&  (((ret_pre + ((n_pre + i_2 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ret_pre ((n_pre + i_2 ) + 1 ) (n_pre + m_pre ) )
  **  (IntArray.full_shape b_pre m_pre )
  **  (IntArray.seg_shape ret_pre 0 (n_pre + i_2 ) )
  **  (IntArray.full_shape a_pre n_pre )
.

(*----- Function array_swap -----*)

Definition array_swap_safety_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_swap_safety_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape b_pre n_pre )
  **  (IntArray.full_shape a_pre n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_swap_entail_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
.

Definition array_swap_entail_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape b_pre n_pre )
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
.

Definition array_swap_return_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
|--
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
.

Definition array_swap_partial_solve_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape a_pre i 0 n_pre )
  **  (IntArray.full_shape b_pre n_pre )
.

Definition array_swap_partial_solve_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape b_pre i 0 n_pre )
  **  (IntArray.full_shape a_pre n_pre )
.

Definition array_swap_partial_solve_wit_3 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape b_pre n_pre )
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i_shape a_pre i 0 n_pre )
  **  (IntArray.full_shape b_pre n_pre )
.

Definition array_swap_partial_solve_wit_4 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  (IntArray.full_shape b_pre n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i_shape b_pre i 0 n_pre )
  **  (IntArray.full_shape a_pre n_pre )
.

(*----- Function array_vector_sum -----*)

Definition array_vector_sum_safety_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.undef_full ret_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_vector_sum_safety_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape ret_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ret" ) )) # Ptr  |-> ret_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_vector_sum_entail_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.undef_full ret_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (UIntArray.seg_shape ret_pre 0 0 )
  **  (UIntArray.undef_seg ret_pre 0 n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
.

Definition array_vector_sum_entail_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape ret_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (UIntArray.seg_shape ret_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
.

Definition array_vector_sum_return_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape ret_pre 0 i )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
|--
  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape ret_pre n_pre )
.

Definition array_vector_sum_partial_solve_wit_1 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape ret_pre 0 i )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt  |-> x)
  **  (UIntArray.missing_i_shape a_pre i 0 n_pre )
  **  (UIntArray.seg_shape ret_pre 0 i )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
.

Definition array_vector_sum_partial_solve_wit_2 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape ret_pre 0 i )
  **  (UIntArray.undef_seg ret_pre i n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt  |-> x)
  **  (UIntArray.missing_i_shape b_pre i 0 n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape ret_pre 0 i )
  **  (UIntArray.undef_seg ret_pre i n_pre )
.

Definition array_vector_sum_partial_solve_wit_3 := 
forall (n_pre: Z) (b_pre: Z) (a_pre: Z) (ret_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape ret_pre 0 i )
  **  (UIntArray.undef_seg ret_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((ret_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg ret_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape ret_pre 0 i )
.

(*----- Function pointwise_mul -----*)

Definition pointwise_mul_safety_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.undef_full c_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pointwise_mul_safety_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape c_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition pointwise_mul_entail_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.undef_full c_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (UIntArray.seg_shape c_pre 0 0 )
  **  (UIntArray.undef_seg c_pre 0 n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
.

Definition pointwise_mul_entail_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape c_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (UIntArray.seg_shape c_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
.

Definition pointwise_mul_return_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape c_pre 0 i )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
|--
  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape c_pre n_pre )
.

Definition pointwise_mul_partial_solve_wit_1 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.seg_shape c_pre 0 i )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(UINT)))) # UInt  |-> x)
  **  (UIntArray.missing_i_shape a_pre i 0 n_pre )
  **  (UIntArray.seg_shape c_pre 0 i )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
.

Definition pointwise_mul_partial_solve_wit_2 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape c_pre 0 i )
  **  (UIntArray.undef_seg c_pre i n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((b_pre + (i * sizeof(UINT)))) # UInt  |-> x)
  **  (UIntArray.missing_i_shape b_pre i 0 n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape c_pre 0 i )
  **  (UIntArray.undef_seg c_pre i n_pre )
.

Definition pointwise_mul_partial_solve_wit_3 := 
forall (n_pre: Z) (c_pre: Z) (b_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape c_pre 0 i )
  **  (UIntArray.undef_seg c_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((c_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg c_pre (i + 1 ) n_pre )
  **  (UIntArray.full_shape b_pre n_pre )
  **  (UIntArray.full_shape a_pre n_pre )
  **  (UIntArray.seg_shape c_pre 0 i )
.

(*----- Function array_max -----*)

Definition array_max_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition array_max_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition array_max_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "max" ) )) # Int  |-> (-1))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_max_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (v: Z) (x: Z) (x_2: Z) (PreH1 : (x > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  ((( &( "max" ) )) # Int  |-> x_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_max_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (v: Z) (x: Z) (PreH1 : (x <= v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  ((( &( "max" ) )) # Int  |-> v)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_max_entail_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
.

Definition array_max_entail_wit_2_1 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (v: Z) (x: Z) (PreH1 : (x > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
.

Definition array_max_entail_wit_2_2 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (v: Z) (x: Z) (PreH1 : (x <= v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
.

Definition array_max_return_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  (IntArray.full_shape a_pre n_pre )
.

Definition array_max_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape a_pre i 0 n_pre )
.

Definition array_max_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (v: Z) (x: Z) (PreH1 : (x > v)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  EX (x_2: Z) ,
  “ (x > v) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> x_2)
  **  (IntArray.missing_i_shape a_pre i 0 n_pre )
.

(*----- Function memset -----*)

Definition memset_safety_wit_1 := 
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.undef_full a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition memset_safety_wit_2 := 
forall (value_pre: Z) (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape a_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition memset_entail_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.undef_full a_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.seg_shape a_pre 0 0 )
  **  (IntArray.undef_seg a_pre 0 n_pre )
.

Definition memset_entail_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape a_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.seg_shape a_pre 0 (i + 1 ) )
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
.

Definition memset_return_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape a_pre 0 i )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  (IntArray.full_shape a_pre n_pre )
.

Definition memset_partial_solve_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) ,
  (IntArray.seg_shape a_pre 0 i )
  **  (IntArray.undef_seg a_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg a_pre (i + 1 ) n_pre )
  **  (IntArray.seg_shape a_pre 0 i )
.

(*----- Function array_to_list -----*)

Definition array_to_list_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_to_list_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  ((( &( "head" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_to_list_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (tail_next: Z) (v: Z) (tail: Z) (head: Z) (i: Z) (x: Z) (retval_next_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_next_2 = 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head <> 0)) (PreH7 : (tail <> 0)) (PreH8 : (tail_next = 0)) (PreH9 : (retval <> 0)) (PreH10 : (retval_next = 0)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) ,
  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next_2)
  **  (IntArray.full_shape a_pre n_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  ((( &( "tail" ) )) # Ptr  |-> retval_2)
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval_2)
  **  (lseg head tail )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_to_list_entail_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval_next = 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) ,
  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> retval_next)
  **  (IntArray.full_shape a_pre n_pre )
|--
  EX (tail_next: Z)  (v: Z) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tail_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg retval retval )
  **  (IntArray.full_shape a_pre n_pre )
.

Definition array_to_list_entail_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (tail_next_2: Z) (v_2: Z) (tail: Z) (head: Z) (i: Z) (x: Z) (retval_next_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_next_2 = 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (head <> 0)) (PreH7 : (tail <> 0)) (PreH8 : (tail_next_2 = 0)) (PreH9 : (retval <> 0)) (PreH10 : (retval_next = 0)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre < INT_MAX)) ,
  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> retval_next_2)
  **  (IntArray.full_shape a_pre n_pre )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v_2)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> retval_2)
  **  (lseg head tail )
|--
  EX (tail_next: Z)  (v: Z) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (head <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (tail_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  ((&((retval_2)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((retval_2)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head retval_2 )
  **  (IntArray.full_shape a_pre n_pre )
.

Definition array_to_list_return_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (tail_next: Z) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (tail_next = 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_next = 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head tail )
  **  (IntArray.full_shape a_pre n_pre )
|--
  (listrep head )
  **  (IntArray.full_shape a_pre n_pre )
.

Definition array_to_list_partial_solve_wit_1_pure := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  ((( &( "head" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 = 0) ”
.

Definition array_to_list_partial_solve_wit_1_aux := 
forall (n_pre: Z) (a_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
|--
  “ (0 = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
.

Definition array_to_list_partial_solve_wit_1 := array_to_list_partial_solve_wit_1_pure -> array_to_list_partial_solve_wit_1_aux.

Definition array_to_list_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (tail_next: Z) (v: Z) (tail: Z) (head: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (tail_next = 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_next = 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) ,
  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head tail )
  **  (IntArray.full_shape a_pre n_pre )
|--
  EX (x: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (head <> 0) ” 
  &&  “ (tail <> 0) ” 
  &&  “ (tail_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> x)
  **  (IntArray.missing_i_shape a_pre i 0 n_pre )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head tail )
.

Definition array_to_list_partial_solve_wit_3_pure := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (tail_next: Z) (v: Z) (tail: Z) (head: Z) (i: Z) (x: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (tail_next = 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_next = 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  ((( &( "node" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Ptr  |-> head)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head tail )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (x = x) ”
.

Definition array_to_list_partial_solve_wit_3_aux := 
forall (n_pre: Z) (a_pre: Z) (retval_next: Z) (retval: Z) (tail_next: Z) (v: Z) (tail: Z) (head: Z) (i: Z) (x: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (head <> 0)) (PreH5 : (tail <> 0)) (PreH6 : (tail_next = 0)) (PreH7 : (retval <> 0)) (PreH8 : (retval_next = 0)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre < INT_MAX)) ,
  (IntArray.full_shape a_pre n_pre )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head tail )
|--
  “ (x = x) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (head <> 0) ” 
  &&  “ (tail <> 0) ” 
  &&  “ (tail_next = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_next = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ”
  &&  (IntArray.full_shape a_pre n_pre )
  **  ((&((tail)  # "list" ->ₛ "data")) # Int  |-> v)
  **  ((&((tail)  # "list" ->ₛ "next")) # Ptr  |-> tail_next)
  **  (lseg head tail )
.

Definition array_to_list_partial_solve_wit_3 := array_to_list_partial_solve_wit_3_pure -> array_to_list_partial_solve_wit_3_aux.

Module Type VC_Correct.

Include sll_shape_Strategy_Correct.

Axiom proof_of_arr_sum_safety_wit_1 : arr_sum_safety_wit_1.
Axiom proof_of_arr_sum_safety_wit_2 : arr_sum_safety_wit_2.
Axiom proof_of_arr_sum_safety_wit_3 : arr_sum_safety_wit_3.
Axiom proof_of_arr_sum_entail_wit_1 : arr_sum_entail_wit_1.
Axiom proof_of_arr_sum_entail_wit_2 : arr_sum_entail_wit_2.
Axiom proof_of_arr_sum_return_wit_1 : arr_sum_return_wit_1.
Axiom proof_of_arr_sum_partial_solve_wit_1 : arr_sum_partial_solve_wit_1.
Axiom proof_of_array_copy1_safety_wit_1 : array_copy1_safety_wit_1.
Axiom proof_of_array_copy1_safety_wit_2 : array_copy1_safety_wit_2.
Axiom proof_of_array_copy1_entail_wit_1 : array_copy1_entail_wit_1.
Axiom proof_of_array_copy1_entail_wit_2 : array_copy1_entail_wit_2.
Axiom proof_of_array_copy1_return_wit_1 : array_copy1_return_wit_1.
Axiom proof_of_array_copy1_partial_solve_wit_1 : array_copy1_partial_solve_wit_1.
Axiom proof_of_array_copy1_partial_solve_wit_2 : array_copy1_partial_solve_wit_2.
Axiom proof_of_array_concat_safety_wit_1 : array_concat_safety_wit_1.
Axiom proof_of_array_concat_safety_wit_2 : array_concat_safety_wit_2.
Axiom proof_of_array_concat_safety_wit_3 : array_concat_safety_wit_3.
Axiom proof_of_array_concat_safety_wit_4 : array_concat_safety_wit_4.
Axiom proof_of_array_concat_safety_wit_5 : array_concat_safety_wit_5.
Axiom proof_of_array_concat_entail_wit_1 : array_concat_entail_wit_1.
Axiom proof_of_array_concat_entail_wit_2 : array_concat_entail_wit_2.
Axiom proof_of_array_concat_entail_wit_3 : array_concat_entail_wit_3.
Axiom proof_of_array_concat_entail_wit_4 : array_concat_entail_wit_4.
Axiom proof_of_array_concat_return_wit_1 : array_concat_return_wit_1.
Axiom proof_of_array_concat_partial_solve_wit_1 : array_concat_partial_solve_wit_1.
Axiom proof_of_array_concat_partial_solve_wit_2 : array_concat_partial_solve_wit_2.
Axiom proof_of_array_concat_partial_solve_wit_3 : array_concat_partial_solve_wit_3.
Axiom proof_of_array_concat_partial_solve_wit_4 : array_concat_partial_solve_wit_4.
Axiom proof_of_array_swap_safety_wit_1 : array_swap_safety_wit_1.
Axiom proof_of_array_swap_safety_wit_2 : array_swap_safety_wit_2.
Axiom proof_of_array_swap_entail_wit_1 : array_swap_entail_wit_1.
Axiom proof_of_array_swap_entail_wit_2 : array_swap_entail_wit_2.
Axiom proof_of_array_swap_return_wit_1 : array_swap_return_wit_1.
Axiom proof_of_array_swap_partial_solve_wit_1 : array_swap_partial_solve_wit_1.
Axiom proof_of_array_swap_partial_solve_wit_2 : array_swap_partial_solve_wit_2.
Axiom proof_of_array_swap_partial_solve_wit_3 : array_swap_partial_solve_wit_3.
Axiom proof_of_array_swap_partial_solve_wit_4 : array_swap_partial_solve_wit_4.
Axiom proof_of_array_vector_sum_safety_wit_1 : array_vector_sum_safety_wit_1.
Axiom proof_of_array_vector_sum_safety_wit_2 : array_vector_sum_safety_wit_2.
Axiom proof_of_array_vector_sum_entail_wit_1 : array_vector_sum_entail_wit_1.
Axiom proof_of_array_vector_sum_entail_wit_2 : array_vector_sum_entail_wit_2.
Axiom proof_of_array_vector_sum_return_wit_1 : array_vector_sum_return_wit_1.
Axiom proof_of_array_vector_sum_partial_solve_wit_1 : array_vector_sum_partial_solve_wit_1.
Axiom proof_of_array_vector_sum_partial_solve_wit_2 : array_vector_sum_partial_solve_wit_2.
Axiom proof_of_array_vector_sum_partial_solve_wit_3 : array_vector_sum_partial_solve_wit_3.
Axiom proof_of_pointwise_mul_safety_wit_1 : pointwise_mul_safety_wit_1.
Axiom proof_of_pointwise_mul_safety_wit_2 : pointwise_mul_safety_wit_2.
Axiom proof_of_pointwise_mul_entail_wit_1 : pointwise_mul_entail_wit_1.
Axiom proof_of_pointwise_mul_entail_wit_2 : pointwise_mul_entail_wit_2.
Axiom proof_of_pointwise_mul_return_wit_1 : pointwise_mul_return_wit_1.
Axiom proof_of_pointwise_mul_partial_solve_wit_1 : pointwise_mul_partial_solve_wit_1.
Axiom proof_of_pointwise_mul_partial_solve_wit_2 : pointwise_mul_partial_solve_wit_2.
Axiom proof_of_pointwise_mul_partial_solve_wit_3 : pointwise_mul_partial_solve_wit_3.
Axiom proof_of_array_max_safety_wit_1 : array_max_safety_wit_1.
Axiom proof_of_array_max_safety_wit_2 : array_max_safety_wit_2.
Axiom proof_of_array_max_safety_wit_3 : array_max_safety_wit_3.
Axiom proof_of_array_max_safety_wit_4 : array_max_safety_wit_4.
Axiom proof_of_array_max_safety_wit_5 : array_max_safety_wit_5.
Axiom proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Axiom proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Axiom proof_of_array_max_entail_wit_2_2 : array_max_entail_wit_2_2.
Axiom proof_of_array_max_return_wit_1 : array_max_return_wit_1.
Axiom proof_of_array_max_partial_solve_wit_1 : array_max_partial_solve_wit_1.
Axiom proof_of_array_max_partial_solve_wit_2 : array_max_partial_solve_wit_2.
Axiom proof_of_memset_safety_wit_1 : memset_safety_wit_1.
Axiom proof_of_memset_safety_wit_2 : memset_safety_wit_2.
Axiom proof_of_memset_entail_wit_1 : memset_entail_wit_1.
Axiom proof_of_memset_entail_wit_2 : memset_entail_wit_2.
Axiom proof_of_memset_return_wit_1 : memset_return_wit_1.
Axiom proof_of_memset_partial_solve_wit_1 : memset_partial_solve_wit_1.
Axiom proof_of_array_to_list_safety_wit_1 : array_to_list_safety_wit_1.
Axiom proof_of_array_to_list_safety_wit_2 : array_to_list_safety_wit_2.
Axiom proof_of_array_to_list_safety_wit_3 : array_to_list_safety_wit_3.
Axiom proof_of_array_to_list_entail_wit_1 : array_to_list_entail_wit_1.
Axiom proof_of_array_to_list_entail_wit_2 : array_to_list_entail_wit_2.
Axiom proof_of_array_to_list_return_wit_1 : array_to_list_return_wit_1.
Axiom proof_of_array_to_list_partial_solve_wit_1_pure : array_to_list_partial_solve_wit_1_pure.
Axiom proof_of_array_to_list_partial_solve_wit_1 : array_to_list_partial_solve_wit_1.
Axiom proof_of_array_to_list_partial_solve_wit_2 : array_to_list_partial_solve_wit_2.
Axiom proof_of_array_to_list_partial_solve_wit_3_pure : array_to_list_partial_solve_wit_3_pure.
Axiom proof_of_array_to_list_partial_solve_wit_3 : array_to_list_partial_solve_wit_3.

End VC_Correct.
