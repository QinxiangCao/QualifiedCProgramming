import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P040_1983C_have_your_cake_and_eat_it_too_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def try_order_safety_wit_1 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "pos" ) )) # Int |->_)
  ** (intArray.full ( &( "right" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** (intArray.full ( &( "left" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_2 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_3 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_4 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_5 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (intArray.full ( &( "left" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_6 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (intArray.full ( &( "left" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_7 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (intArray.full ( &( "left" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_8 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  ((( &( "part" ) )) # Int |->_)
  ** ((( &( "pos" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full ( &( "right" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** (intArray.full ( &( "left" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_9 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts : (List Int)) (rights : (List Int)) (part : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part <= 2)) (PreH15 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def try_order_safety_wit_10 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts : (List Int)) (rights : (List Int)) (part : Int) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights)) ,
  ((( &( "acc" ) )) # Int64 |->_)
  ** ((( &( "start" ) )) # Int |-> (pos))
  ** (intArray.full order_pre 3 ord)
  ** ((( &( "who" ) )) # Int |-> ((Znth part ord (0 : Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_11 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
) \/
(
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
)

noncomputable def try_order_safety_wit_11_split_goal_1 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 9223372036854775807) ”

noncomputable def try_order_safety_wit_11_split_goal_2 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((-9223372036854775808) <= (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”

noncomputable def try_order_safety_wit_12 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((pos + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + 1)) ”

noncomputable def try_order_safety_wit_13 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (part : Int) (who : Int) (start : Int) (acc : Int) (PreH1 : ((0 : Int) <= part)) (PreH2 : (part < 2)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : ((0 : Int) <= start)) (PreH6 : (start <= n_pre)) (PreH7 : ((0 : Int) <= acc)) (PreH8 : (acc < need_pre)) (PreH9 : (TryOrderSpec a b c ord None)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (n_pre))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_14 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((start + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (start + 1)) ”

noncomputable def try_order_safety_wit_15 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "start" ) )) # Int |-> (start))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def try_order_safety_wit_16 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (intArray.full ( &( "right" ) ) 3 (replace_Znth (who) (pos) (rights)))
  ** (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1)) (lefts)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "part" ) )) # Int |-> (part))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((part + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (part + 1)) ”

noncomputable def try_order_safety_wit_17 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts : (List Int)) (rights : (List Int)) (part : Int) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights)) ,
  ((( &( "who" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def try_order_safety_wit_18 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts : (List Int)) (rights : (List Int)) (part : Int) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights)) ,
  ((( &( "acc" ) )) # Int64 |->_)
  ** (intArray.full order_pre 3 ord)
  ** ((( &( "who" ) )) # Int |-> ((Znth 2 ord (0 : Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_19 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "acc" ) )) # Int64 |-> ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def try_order_safety_wit_20 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
) \/
(
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
)

noncomputable def try_order_safety_wit_20_split_goal_1 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 9223372036854775807) ”

noncomputable def try_order_safety_wit_20_split_goal_2 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((-9223372036854775808) <= (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”

noncomputable def try_order_safety_wit_21 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : ((0 : Int) <= acc)) (PreH6 : (acc < need_pre)) (PreH7 : (TryOrderSpec a b c ord None)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_22 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((pos + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + 1)) ”

noncomputable def try_order_safety_wit_23 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def try_order_safety_wit_24 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def try_order_safety_wit_25 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 3)) (PreH9 : ((Zlength (raw_prefix)) = (2 * i))) (PreH10 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH11 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def try_order_safety_wit_26 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)
|--
  “ ((2 * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i)) ”

noncomputable def try_order_safety_wit_27 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def try_order_safety_wit_28 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
|--
  “ (((2 * i) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i) + 1)) ”

noncomputable def try_order_safety_wit_29 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
|--
  “ ((2 * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i)) ”

noncomputable def try_order_safety_wit_30 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def try_order_safety_wit_31 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def try_order_safety_wit_32 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) (((2 * i) + 1) + 1) ((raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))) ++ ((Znth i rights (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (((2 * i) + 1) + 1) 6)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def try_order_safety_wit_33 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_result : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH8 : ((Zlength (raw_result)) = 6)) (PreH9 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "need" ) )) # Int64 |-> (need_pre))
  ** ((( &( "order" ) )) # Ptr |-> (order_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "who" ) )) # Int |-> (who))
  ** ((( &( "acc" ) )) # Int64 |-> (acc))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.full out_pre 6 raw_result)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def try_order_entail_wit_1 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (intArray.full ( &( "right" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** (intArray.full ( &( "left" ) ) 3 (repeat_Z ((0 : Int)) (3)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 2) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre (0 : Int) (0 : Int) lefts rights) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  TT && emp 
|--
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre (0 : Int) (0 : Int) (repeat_Z ((0 : Int)) (3)) (repeat_Z ((0 : Int)) (3))) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (1 <= need_pre) ”
  &&  emp
)

noncomputable def try_order_entail_wit_1_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre (0 : Int) (0 : Int) (repeat_Z ((0 : Int)) (3)) (repeat_Z ((0 : Int)) (3)))

noncomputable def try_order_entail_wit_1_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (need_pre <= 200000000000)

noncomputable def try_order_entail_wit_1_split_goal_3 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (CakeOrder ord)) (PreH10 : ((Zlength (ord)) = 3)) ,
  (1 <= need_pre)

noncomputable def try_order_entail_wit_2 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (intArray.full order_pre 3 ord)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX row_ptr : Int, EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ ((Znth part ord (0 : Int)) = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (Znth part ord (0 : Int))) ” &&
  “ ((Znth part ord (0 : Int)) < 3) ” &&
  “ (pos = pos) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (Znth part ord (0 : Int)) row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((Znth part ord (0 : Int)) * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth ((Znth part ord (0 : Int))) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
|--
  EX row_ptr : Int,
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ ((Znth part ord (0 : Int)) = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (Znth part ord (0 : Int))) ” &&
  “ ((Znth part ord (0 : Int)) < 3) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (Znth part ord (0 : Int)) row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((Znth part ord (0 : Int)) * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth ((Znth part ord (0 : Int))) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
)

noncomputable def try_order_entail_wit_3 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (row_ptr_2 : Int) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr_2))
  ** (int64Array.full row_ptr_2 n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX row_ptr : Int, EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (start >= (0 : Int)) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc) ”
  &&  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  TT && emp 
|--
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start start need_pre (0 : Int)) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= n_pre) ” &&
  “ (start >= (0 : Int)) ”
  &&  emp
)

noncomputable def try_order_entail_wit_3_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start start need_pre (0 : Int))

noncomputable def try_order_entail_wit_3_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (start <= n_pre)

noncomputable def try_order_entail_wit_3_split_goal_3 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  ((0 : Int) <= start)

noncomputable def try_order_entail_wit_3_split_goal_4 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (start <= n_pre)

noncomputable def try_order_entail_wit_3_split_goal_5 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : ((0 : Int) <= part)) (PreH14 : (part < 2)) (PreH15 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH16 : ((0 : Int) <= who)) (PreH17 : (who < 3)) (PreH18 : (start = pos)) (PreH19 : (acc = (0 : Int))) (PreH20 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (start >= (0 : Int))

noncomputable def try_order_entail_wit_4 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr_2 : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64Array.full row_ptr_2 n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr_2))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX row_ptr : Int, EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (start >= (0 : Int)) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= (pos + 1)) ” &&
  “ ((pos + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ” &&
  “ ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start (pos + 1) need_pre (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
  &&  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  TT && emp 
|--
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start (pos + 1) need_pre (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ” &&
  “ ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 200000000000) ” &&
  “ ((0 : Int) <= (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
  &&  emp
)

noncomputable def try_order_entail_wit_4_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start (pos + 1) need_pre (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))))

noncomputable def try_order_entail_wit_4_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  ((acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 200000000000)

noncomputable def try_order_entail_wit_4_split_goal_3 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  ((0 : Int) <= (acc + (Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))))

noncomputable def try_order_entail_wit_5_1 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= (0 : Int))) (PreH20 : (start <= n_pre)) (PreH21 : ((0 : Int) <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : ((0 : Int) <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH26 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((acc < need_pre) -> (pos >= n_pre)) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= (0 : Int))) (PreH20 : (start <= n_pre)) (PreH21 : ((0 : Int) <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : ((0 : Int) <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH26 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
)

noncomputable def try_order_entail_wit_5_1_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= (0 : Int))) (PreH20 : (start <= n_pre)) (PreH21 : ((0 : Int) <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : ((0 : Int) <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH26 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”

noncomputable def try_order_entail_wit_5_1_split_goal_spatial : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (pos >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part < 2)) (PreH16 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : (start >= (0 : Int))) (PreH20 : (start <= n_pre)) (PreH21 : ((0 : Int) <= pos)) (PreH22 : (pos <= n_pre)) (PreH23 : ((0 : Int) <= acc)) (PreH24 : (acc <= 200000000000)) (PreH25 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH26 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))

noncomputable def try_order_entail_wit_5_2 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((acc < need_pre) -> (pos >= n_pre)) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ (start <= pos) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
)

noncomputable def try_order_entail_wit_5_2_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ (start <= pos) ”

noncomputable def try_order_entail_wit_5_2_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”

noncomputable def try_order_entail_wit_5_2_split_goal_spatial : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))

noncomputable def try_order_entail_wit_6 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  ((( &( "pos" ) )) # Int |-> (pos))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX rights : (List Int), EX lefts : (List Int),
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc < need_pre) ” &&
  “ (TryOrderSpec a b c ord None) ”
  &&  ((( &( "pos" ) )) # Int |-> (n_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  TT && emp 
|--
  “ (TryOrderSpec a b c ord None) ” &&
  “ ((0 : Int) <= acc) ”
  &&  emp
)

noncomputable def try_order_entail_wit_6_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (TryOrderSpec a b c ord None)

noncomputable def try_order_entail_wit_6_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  ((0 : Int) <= acc)

noncomputable def try_order_entail_wit_7 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (intArray.full ( &( "right" ) ) 3 (replace_Znth (who) (pos) (rights_2)))
  ** (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1)) (lefts_2)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= (part + 1)) ” &&
  “ ((part + 1) <= 2) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre (part + 1) pos lefts rights) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  TT && emp 
|--
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre (part + 1) pos (replace_Znth (who) ((start + 1)) (lefts_2)) (replace_Znth (who) (pos) (rights_2))) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (1 <= need_pre) ”
  &&  emp
)

noncomputable def try_order_entail_wit_7_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre (part + 1) pos (replace_Znth (who) ((start + 1)) (lefts_2)) (replace_Znth (who) (pos) (rights_2)))

noncomputable def try_order_entail_wit_7_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (need_pre <= 200000000000)

noncomputable def try_order_entail_wit_7_split_goal_3 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts_2 rights_2)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (1 <= need_pre)

noncomputable def try_order_entail_wit_8 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (intArray.full order_pre 3 ord)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX row_ptr : Int, EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((Znth 2 ord (0 : Int)) = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (Znth 2 ord (0 : Int))) ” &&
  “ ((Znth 2 ord (0 : Int)) < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (Znth 2 ord (0 : Int)) row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((Znth 2 ord (0 : Int)) * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth ((Znth 2 ord (0 : Int))) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (part : Int) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts_2 rights_2)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
|--
  EX row_ptr : Int,
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((Znth 2 ord (0 : Int)) = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= (Znth 2 ord (0 : Int))) ” &&
  “ ((Znth 2 ord (0 : Int)) < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (Znth 2 ord (0 : Int)) row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((Znth 2 ord (0 : Int)) * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth ((Znth 2 ord (0 : Int))) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
)

noncomputable def try_order_entail_wit_9 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (row_ptr_2 : Int) (who : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH14 : ((0 : Int) <= who)) (PreH15 : (who < 3)) (PreH16 : ((0 : Int) <= pos)) (PreH17 : (pos <= n_pre)) (PreH18 : (acc = (0 : Int))) (PreH19 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr_2))
  ** (int64Array.full row_ptr_2 n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX row_ptr : Int, EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ (who = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ” &&
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos pos acc) ”
  &&  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (who : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH14 : ((0 : Int) <= who)) (PreH15 : (who < 3)) (PreH16 : ((0 : Int) <= pos)) (PreH17 : (pos <= n_pre)) (PreH18 : (acc = (0 : Int))) (PreH19 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) ,
  TT && emp 
|--
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos pos (0 : Int)) ”
  &&  emp
)

noncomputable def try_order_entail_wit_9_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (who : Int) (pos : Int) (acc : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need_pre)) (PreH10 : (need_pre <= 200000000000)) (PreH11 : (CakeOrder ord)) (PreH12 : ((Zlength (ord)) = 3)) (PreH13 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH14 : ((0 : Int) <= who)) (PreH15 : (who < 3)) (PreH16 : ((0 : Int) <= pos)) (PreH17 : (pos <= n_pre)) (PreH18 : (acc = (0 : Int))) (PreH19 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) ,
  (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos pos (0 : Int))

noncomputable def try_order_entail_wit_10 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr_2 : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64Array.full row_ptr_2 n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr_2 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr_2))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX row_ptr : Int, EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ (who = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ” &&
  “ ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ” &&
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos (i + 1) (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
  &&  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  TT && emp 
|--
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos (i + 1) (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ” &&
  “ ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 200000000000) ” &&
  “ ((0 : Int) <= (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int)))) ”
  &&  emp
)

noncomputable def try_order_entail_wit_10_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos (i + 1) (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))))

noncomputable def try_order_entail_wit_10_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  ((acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))) <= 200000000000)

noncomputable def try_order_entail_wit_10_split_goal_3 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  ((0 : Int) <= (acc + (Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))))

noncomputable def try_order_entail_wit_11 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ (who = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ” &&
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
)

noncomputable def try_order_entail_wit_11_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc) ”

noncomputable def try_order_entail_wit_11_split_goal_2 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”

noncomputable def try_order_entail_wit_11_split_goal_spatial : Prop :=
  forall (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts_2 : (List Int)) (rights_2 : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
|--
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))

noncomputable def try_order_entail_wit_12 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX rights : (List Int), EX lefts : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc < need_pre) ” &&
  “ (TryOrderSpec a b c ord None) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  TT && emp 
|--
  “ (TryOrderSpec a b c ord None) ”
  &&  emp
)

noncomputable def try_order_entail_wit_12_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc < need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  (TryOrderSpec a b c ord None)

noncomputable def try_order_entail_wit_13 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  (intArray.full ( &( "right" ) ) 3 (replace_Znth (who) (n_pre) (rights_2)))
  ** (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((pos + 1)) (lefts_2)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  TT && emp 
|--
  “ (TryOrderSpec a b c ord (Some ((OutputBounds ((replace_Znth (who) ((pos + 1)) (lefts_2))) ((replace_Znth (who) (n_pre) (rights_2))))))) ”
  &&  emp
)

noncomputable def try_order_entail_wit_13_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts_2 rights_2)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  (TryOrderSpec a b c ord (Some ((OutputBounds ((replace_Znth (who) ((pos + 1)) (lefts_2))) ((replace_Znth (who) (n_pre) (rights_2)))))))

noncomputable def try_order_entail_wit_14 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.undef_full out_pre 6)
|--
  EX lefts : (List Int), EX rights : (List Int), EX raw_prefix : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * (0 : Int))) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * (0 : Int)))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * (0 : Int)) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * (0 : Int)) 6)
) \/
(
forall (out_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  EX raw_prefix : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * (0 : Int))) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * (0 : Int)))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.seg out_pre (0 : Int) (2 * (0 : Int)) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * (0 : Int)) 6)
)

noncomputable def try_order_entail_wit_15 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (raw_prefix_2 : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix_2)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix_2 (0 : Int)) = ((Znth j (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) (((2 * i) + 1) + 1) ((raw_prefix_2 ++ ((Znth i lefts_2 (0 : Int)) :: (@List.nil Int))) ++ ((Znth i rights_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre (((2 * i) + 1) + 1) 6)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
|--
  EX lefts : (List Int), EX rights : (List Int), EX raw_prefix : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * (i + 1))) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * (i + 1)))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * (i + 1)) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * (i + 1)) 6)
) \/
(
forall (out_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (raw_prefix_2 : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix_2)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix_2 (0 : Int)) = ((Znth j (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) (((2 * i) + 1) + 1) ((raw_prefix_2 ++ ((Znth i lefts_2 (0 : Int)) :: (@List.nil Int))) ++ ((Znth i rights_2 (0 : Int)) :: (@List.nil Int))))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
|--
  EX raw_prefix : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * (i + 1))) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * (i + 1)))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.seg out_pre (0 : Int) (2 * (i + 1)) raw_prefix)
)

noncomputable def try_order_entail_wit_16 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i >= 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) (PreH12 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < (2 * i))) -> ((Znth j_2 raw_prefix (0 : Int)) = ((Znth j_2 (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1)))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts_2)
  ** (intArray.full ( &( "right" ) ) 3 rights_2)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)
|--
  EX raw_result : (List Int), EX lefts : (List Int), EX rights : (List Int),
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ ((Zlength (raw_result)) = 6) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.full out_pre 6 raw_result)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i >= 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) (PreH12 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < (2 * i))) -> ((Znth j_2 raw_prefix (0 : Int)) = ((Znth j_2 (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1)))) ,
  TT && emp 
|--
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1))) ”
  &&  emp
)

noncomputable def try_order_entail_wit_16_split_goal_1 : Prop :=
  forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts_2 : (List Int)) (rights_2 : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i >= 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts_2) (rights_2)))))) (PreH12 : forall (j_2 : Int) , ((((0 : Int) <= j_2) ∧ (j_2 < (2 * i))) -> ((Znth j_2 raw_prefix (0 : Int)) = ((Znth j_2 (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1)))) ,
  forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts_2) (rights_2)) (0 : Int)) + 1)))

noncomputable def try_order_return_wit_1 : Prop :=
  (
forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_result_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH8 : ((Zlength (raw_result_2)) = 6)) (PreH9 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result_2 (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full out_pre 6 raw_result_2)
|--
  EX raw_result : (List Int), EX result : (List Int),
  “ (1 = 1) ” &&
  “ (TryOrderSpec a b c ord (Some (result))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full out_pre 6 raw_result)
) \/
(
forall (need_pre : Int) (n_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_result_2 : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : (need_pre <= acc)) (PreH6 : (acc <= 200000000000)) (PreH7 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH8 : ((Zlength (raw_result_2)) = 6)) (PreH9 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result_2 (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  TT && emp 
|--
  EX result : (List Int),
  “ (TryOrderSpec a b c ord (Some (result))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result_2 (0 : Int)) = ((Znth i result (0 : Int)) + 1))) ”
  &&  emp
)

noncomputable def try_order_return_wit_2 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : ((0 : Int) <= pos)) (PreH2 : (pos <= n_pre)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : ((0 : Int) <= acc)) (PreH6 : (acc < need_pre)) (PreH7 : (TryOrderSpec a b c ord None)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (TryOrderSpec a b c ord None) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_return_wit_3 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (part : Int) (who : Int) (start : Int) (acc : Int) (PreH1 : ((0 : Int) <= part)) (PreH2 : (part < 2)) (PreH3 : ((0 : Int) <= who)) (PreH4 : (who < 3)) (PreH5 : ((0 : Int) <= start)) (PreH6 : (start <= n_pre)) (PreH7 : ((0 : Int) <= acc)) (PreH8 : (acc < need_pre)) (PreH9 : (TryOrderSpec a b c ord None)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (TryOrderSpec a b c ord None) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts : (List Int)) (rights : (List Int)) (part : Int) (PreH1 : (part < 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (part < 2) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part <= 2) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights) ”
  &&  (((order_pre + (part * sizeof(INT)))) # Int |-> ((Znth part ord (0 : Int))))
  ** (intArray.missing_i order_pre part (0 : Int) 3 ord)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_2 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (pos : Int) (start : Int) (who : Int) (part : Int) (PreH1 : (acc < need_pre)) (PreH2 : (pos < n_pre)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need_pre)) (PreH12 : (need_pre <= 200000000000)) (PreH13 : (CakeOrder ord)) (PreH14 : ((Zlength (ord)) = 3)) (PreH15 : ((0 : Int) <= part)) (PreH16 : (part < 2)) (PreH17 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH18 : ((0 : Int) <= who)) (PreH19 : (who < 3)) (PreH20 : (start >= (0 : Int))) (PreH21 : (start <= n_pre)) (PreH22 : ((0 : Int) <= pos)) (PreH23 : (pos <= n_pre)) (PreH24 : ((0 : Int) <= acc)) (PreH25 : (acc <= 200000000000)) (PreH26 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH27 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (acc < need_pre) ” &&
  “ (pos < n_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (start >= (0 : Int)) ” &&
  “ (start <= n_pre) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc) ”
  &&  (((row_ptr + (pos * sizeof(INT64)))) # Int64 |-> ((Znth pos (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))))
  ** (int64Array.missing_i row_ptr pos (0 : Int) n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_3 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (acc >= need_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((acc < need_pre) -> (pos >= n_pre)) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc) ”
  &&  (((( &( "left" ) ) + (who * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "left" ) ) who (0 : Int) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_4 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (part : Int) (who : Int) (start : Int) (pos : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (CakeOrder ord)) (PreH11 : ((Zlength (ord)) = 3)) (PreH12 : ((0 : Int) <= part)) (PreH13 : (part < 2)) (PreH14 : (who = (Znth (part) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= start)) (PreH18 : (start <= pos)) (PreH19 : (pos <= n_pre)) (PreH20 : ((acc < need_pre) -> (pos >= n_pre))) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights)) (PreH22 : (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc)) ,
  (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1)) (lefts)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (acc >= need_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part < 2) ” &&
  “ (who = (Znth (part) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= start) ” &&
  “ (start <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((acc < need_pre) -> (pos >= n_pre)) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part start lefts rights) ” &&
  “ (SearchPrefixState (a :: (b :: (c :: (@List.nil (List Int))))) who start pos need_pre acc) ”
  &&  (((( &( "right" ) ) + (who * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "right" ) ) who (0 : Int) 3 rights)
  ** (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((start + 1)) (lefts)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_5 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (pos : Int) (lefts : (List Int)) (rights : (List Int)) (part : Int) (PreH1 : (part >= 2)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= part)) (PreH15 : (part <= 2)) (PreH16 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (part >= 2) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= part) ” &&
  “ (part <= 2) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre part pos lefts rights) ”
  &&  (((order_pre + (2 * sizeof(INT)))) # Int |-> ((Znth 2 ord (0 : Int))))
  ** (intArray.missing_i order_pre 2 (0 : Int) 3 ord)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_6 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row_ptr : Int) (lefts : (List Int)) (rights : (List Int)) (acc : Int) (i : Int) (pos : Int) (who : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH15 : ((0 : Int) <= who)) (PreH16 : (who < 3)) (PreH17 : ((0 : Int) <= pos)) (PreH18 : (pos <= i)) (PreH19 : (i <= n_pre)) (PreH20 : ((0 : Int) <= acc)) (PreH21 : (acc <= 200000000000)) (PreH22 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH23 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc)) ,
  (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (int64Array.full row_ptr n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (i < n_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ (who = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ” &&
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos i acc) ”
  &&  (((row_ptr + (i * sizeof(INT64)))) # Int64 |-> ((Znth i (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))) (0 : Int))))
  ** (int64Array.missing_i row_ptr i (0 : Int) n_pre (Znth (who) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int))))
  ** (int64PtrArray2.missing_i v_pre 3 who row_ptr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + (who * sizeof(PTR)))) # Ptr |-> (row_ptr))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_7 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (acc >= need_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ (who = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ” &&
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc) ”
  &&  (((( &( "left" ) ) + (who * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "left" ) ) who (0 : Int) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_8 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (pos : Int) (who : Int) (acc : Int) (PreH1 : (acc >= need_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (need_pre = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need_pre)) (PreH11 : (need_pre <= 200000000000)) (PreH12 : (CakeOrder ord)) (PreH13 : ((Zlength (ord)) = 3)) (PreH14 : ((0 : Int) <= pos)) (PreH15 : (pos <= n_pre)) (PreH16 : (who = (Znth (2) (ord) ((0 : Int))))) (PreH17 : ((0 : Int) <= who)) (PreH18 : (who < 3)) (PreH19 : ((0 : Int) <= acc)) (PreH20 : (acc <= 200000000000)) (PreH21 : (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights)) (PreH22 : (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc)) ,
  (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((pos + 1)) (lefts)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.undef_full out_pre 6)
|--
  “ (acc >= need_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need_pre = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need_pre) ” &&
  “ (need_pre <= 200000000000) ” &&
  “ (CakeOrder ord) ” &&
  “ ((Zlength (ord)) = 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ (who = (Znth (2) (ord) ((0 : Int)))) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ ((0 : Int) <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ (GreedyRawState (a :: (b :: (c :: (@List.nil (List Int))))) ord need_pre 2 pos lefts rights) ” &&
  “ (SuffixSumState (a :: (b :: (c :: (@List.nil (List Int))))) who pos n_pre acc) ”
  &&  (((( &( "right" ) ) + (who * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "right" ) ) who (0 : Int) 3 rights)
  ** (intArray.full ( &( "left" ) ) 3 (replace_Znth (who) ((pos + 1)) (lefts)))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.undef_full out_pre 6)

noncomputable def try_order_partial_solve_wit_9 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)
|--
  “ (i < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * i)) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (((( &( "left" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i lefts (0 : Int))))
  ** (intArray.missing_i ( &( "left" ) ) i (0 : Int) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)

noncomputable def try_order_partial_solve_wit_10 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.full ( &( "left" ) ) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)
  ** (intArray.undef_seg out_pre (2 * i) 6)
|--
  “ (i < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * i)) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (((out_pre + ((2 * i) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) (2 * i) raw_prefix)

noncomputable def try_order_partial_solve_wit_11 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
  ** (intArray.full ( &( "right" ) ) 3 rights)
|--
  “ (i < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * i)) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (((( &( "right" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i rights (0 : Int))))
  ** (intArray.missing_i ( &( "right" ) ) i (0 : Int) 3 rights)
  ** (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)

noncomputable def try_order_partial_solve_wit_12 : Prop :=
  forall (out_pre : Int) (order_pre : Int) (need_pre : Int) (n_pre : Int) (v_pre : Int) (ord : (List Int)) (c : (List Int)) (b : (List Int)) (a : (List Int)) (lefts : (List Int)) (rights : (List Int)) (raw_prefix : (List Int)) (i : Int) (acc : Int) (who : Int) (pos : Int) (PreH1 : (i < 3)) (PreH2 : ((0 : Int) <= pos)) (PreH3 : (pos <= n_pre)) (PreH4 : ((0 : Int) <= who)) (PreH5 : (who < 3)) (PreH6 : (need_pre <= acc)) (PreH7 : (acc <= 200000000000)) (PreH8 : ((0 : Int) <= i)) (PreH9 : (i <= 3)) (PreH10 : ((Zlength (raw_prefix)) = (2 * i))) (PreH11 : (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights)))))) (PreH12 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1)))) ,
  (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg out_pre ((2 * i) + 1) 6)
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)
|--
  “ (i < 3) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= n_pre) ” &&
  “ ((0 : Int) <= who) ” &&
  “ (who < 3) ” &&
  “ (need_pre <= acc) ” &&
  “ (acc <= 200000000000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= 3) ” &&
  “ ((Zlength (raw_prefix)) = (2 * i)) ” &&
  “ (TryOrderSpec a b c ord (Some ((OutputBounds (lefts) (rights))))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < (2 * i))) -> ((Znth j raw_prefix (0 : Int)) = ((Znth j (OutputBounds (lefts) (rights)) (0 : Int)) + 1))) ”
  &&  (((out_pre + (((2 * i) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg out_pre (((2 * i) + 1) + 1) 6)
  ** (intArray.full ( &( "right" ) ) 3 rights)
  ** (intArray.seg out_pre (0 : Int) ((2 * i) + 1) (raw_prefix ++ ((Znth i lefts (0 : Int)) :: (@List.nil Int))))
  ** (intArray.full ( &( "left" ) ) 3 lefts)
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full order_pre 3 ord)

noncomputable def solver_safety_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  ((( &( "total" ) )) # Int64 |->_)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: (repeat_Z ((0 : Int)) (1))))))))))))))))))))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_20 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0 : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (0 : Int))) ,
  ((( &( "row0" ) )) # Ptr |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0))
  ** (int64Array.full row0 n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_21 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0 : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (0 : Int))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "row0" ) )) # Ptr |-> (row0))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0))
  ** (int64Array.full row0 n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_22 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64Array.full row0_addr n_pre a)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> ((total + (Znth i a (0 : Int)))))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solver_safety_wit_23 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64Array.full row0_addr n_pre a)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((total + (Znth i a (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (Znth i a (0 : Int)))) ”
) \/
(
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64Array.full row0_addr n_pre a)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((total + (Znth i a (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + (Znth i a (0 : Int)))) ”
)

noncomputable def solver_safety_wit_23_split_goal_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64Array.full row0_addr n_pre a)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((total + (Znth i a (0 : Int))) <= 9223372036854775807) ”

noncomputable def solver_safety_wit_23_split_goal_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64Array.full row0_addr n_pre a)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((-9223372036854775808) <= (total + (Znth i a (0 : Int)))) ”

noncomputable def solver_safety_wit_24 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64 |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (((total + 2) ≠ (-9223372036854775808)) ∨ (3 ≠ (-1))) ” &&
  “ (3 ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_25 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64 |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((total + 2) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (total + 2)) ”

noncomputable def solver_safety_wit_26 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64 |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_27 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "need" ) )) # Int64 |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_28 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  ((( &( "z" ) )) # Int |->_)
  ** ((( &( "need" ) )) # Int64 |-> ((Z.quot (total + 2) 3)))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_29 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (z : Int) (need : Int) (total : Int) (row0_addr : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need)) (PreH11 : (need <= 200000000000)) (PreH12 : ((0 : Int) <= z)) (PreH13 : (z <= 6)) (PreH14 : (OrderTable table)) (PreH15 : (FailedOrders a b c z)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ (6 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 6) ”

noncomputable def solver_safety_wit_30 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (z : Int) (need : Int) (total : Int) (row0_addr : Int) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table)) (PreH16 : (FailedOrders a b c z)) ,
  ((( &( "ordp" ) )) # Ptr |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ ((3 * z) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (3 * z)) ”

noncomputable def solver_safety_wit_31 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (z : Int) (need : Int) (total : Int) (row0_addr : Int) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table)) (PreH16 : (FailedOrders a b c z)) ,
  ((( &( "ordp" ) )) # Ptr |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_32 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (z : Int) (need : Int) (total : Int) (row0_addr : Int) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table)) (PreH16 : (FailedOrders a b c z)) ,
  ((( &( "ordp" ) )) # Ptr |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ (3 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 3) ”

noncomputable def solver_safety_wit_33 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ordp : Int) (raw_result : (List Int)) (result : (List Int)) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result)))) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1)))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH9 : (Pre a b c)) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : ((0 : Int) <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z)) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH19 : (OrderTable table)) (PreH20 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH21 : ((Zlength (before)) = (3 * z))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH24 : (OrderAt z (OrderFor (z)))) (PreH25 : (CakeOrder (OrderFor (z)))) (PreH26 : (retval = (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.full out_pre 6 raw_result)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** ((( &( "ordp" ) )) # Ptr |-> (ordp))
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ False ”

noncomputable def solver_safety_wit_34 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ordp : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : ((0 : Int) <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z)) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH18 : (OrderTable table)) (PreH19 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH20 : ((Zlength (before)) = (3 * z))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH23 : (OrderAt z (OrderFor (z)))) (PreH24 : (CakeOrder (OrderFor (z)))) (PreH25 : (retval ≠ (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** ((( &( "ok" ) )) # Int |-> (retval))
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** ((( &( "ordp" ) )) # Ptr |-> (ordp))
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ False ”

noncomputable def solver_safety_wit_35 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (result : (List Int)) (raw_result : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH3 : ((0 : Int) <= z)) (PreH4 : (z < 6)) (PreH5 : (ok = 1)) (PreH6 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH7 : (Spec a b c (Some (result)))) (PreH8 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result (0 : Int)) = ((Znth j result (0 : Int)) + 1)))) (PreH9 : (OrderTable table)) (PreH10 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH11 : ((Zlength (before)) = (3 * z))) (PreH12 : ((Zlength ((OrderFor (z)))) = 3)) (PreH13 : ((Zlength (after)) = (18 - (3 * (z + 1))))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** ((( &( "ok" ) )) # Int |-> (ok))
  ** ((( &( "ordp" ) )) # Ptr |-> (ordp))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full out_pre 6 raw_result)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_36 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : ((0 : Int) <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = (0 : Int))) (PreH14 : (OrderTable table)) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH16 : (FailedOrders a b c (z + 1))) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ ((z + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (z + 1)) ”

noncomputable def solver_safety_wit_37 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH3 : (FailedOrders a b c 6)) (PreH4 : (Spec a b c None)) (PreH5 : (OrderTable table)) ,
  ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: (repeat_Z ((0 : Int)) (1))))))))))))))))))))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  EX row0 : Int,
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ ((0 : Int) = (0 : Int)) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0))
  ** (int64Array.full row0 n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
) \/
(
forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
|--
  EX row0 : Int,
  “ (((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: (repeat_Z ((0 : Int)) (1))))))))))))))))))) = ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int)))))))))))))))))))) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0))
  ** (int64Array.full row0 n_pre a)
)

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0 : Int) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (0 : Int))) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0))
  ** (int64Array.full row0 n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (total = (sum ((sublist ((0 : Int)) ((0 : Int)) (a))))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200000000000) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0))
  ** (int64Array.full row0 n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
) \/
(
forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (0 : Int))) ,
  TT && emp 
|--
  “ ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (a))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (0 : Int))) ,
  ((0 : Int) = (sum ((sublist ((0 : Int)) ((0 : Int)) (a)))))

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64Array.full row0_addr n_pre a)
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((total + (Znth i a (0 : Int))) = (sum ((sublist ((0 : Int)) ((i + 1)) (a))))) ” &&
  “ ((0 : Int) <= (total + (Znth i a (0 : Int)))) ” &&
  “ ((total + (Znth i a (0 : Int))) <= 200000000000) ”
  &&  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
) \/
(
forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  TT && emp 
|--
  “ ((total + (Znth i a (0 : Int))) <= 200000000000) ” &&
  “ ((0 : Int) <= (total + (Znth i a (0 : Int)))) ” &&
  “ ((total + (Znth i a (0 : Int))) = (sum ((sublist ((0 : Int)) ((i + 1)) (a))))) ”
  &&  emp
)

noncomputable def solver_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  ((total + (Znth i a (0 : Int))) <= 200000000000)

noncomputable def solver_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  ((0 : Int) <= (total + (Znth i a (0 : Int))))

noncomputable def solver_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  ((total + (Znth i a (0 : Int))) = (sum ((sublist ((0 : Int)) ((i + 1)) (a)))))

noncomputable def solver_entail_wit_4 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200000000000) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
) \/
(
forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
|--
  “ (total = (sum (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
)

noncomputable def solver_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
|--
  “ (total = (sum (a))) ”

noncomputable def solver_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”

noncomputable def solver_entail_wit_4_split_goal_spatial : Prop :=
  forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
|--
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))

noncomputable def solver_entail_wit_5 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  EX table : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ ((Z.quot (total + 2) 3) = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= (Z.quot (total + 2) 3)) ” &&
  “ ((Z.quot (total + 2) 3) <= 200000000000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 6) ” &&
  “ (OrderTable table) ” &&
  “ (FailedOrders a b c (0 : Int)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
) \/
(
forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  TT && emp 
|--
  “ (FailedOrders a b c (0 : Int)) ” &&
  “ (OrderTable ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int)))))))))))))))))))) ” &&
  “ ((Z.quot (total + 2) 3) <= 200000000000) ” &&
  “ (1 <= (Z.quot (total + 2) 3)) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_split_goal_1 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  (FailedOrders a b c (0 : Int))

noncomputable def solver_entail_wit_5_split_goal_2 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  (OrderTable ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))

noncomputable def solver_entail_wit_5_split_goal_3 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  ((Z.quot (total + 2) 3) <= 200000000000)

noncomputable def solver_entail_wit_5_split_goal_4 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (total : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 200000000000)) ,
  (1 <= (Z.quot (total + 2) 3))

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (z : Int) (need : Int) (total : Int) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2)) (PreH16 : (FailedOrders a b c z)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table_2)
|--
  EX before : (List Int), EX after : (List Int), EX table : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ ((( &( "orders" ) ) + ((3 * z) * sizeof(INT))) = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.full (( &( "orders" ) ) + ((3 * z) * sizeof(INT))) 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
) \/
(
forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (z : Int) (need : Int) (total : Int) (PreH1 : (z < 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2)) (PreH16 : (FailedOrders a b c z)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "orders" ) ) 18 table_2)
|--
  EX before : (List Int), EX after : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ ((( &( "orders" ) ) + ((3 * z) * sizeof(INT))) = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.full (( &( "orders" ) ) + ((3 * z) * sizeof(INT))) 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
)

noncomputable def solver_entail_wit_7_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : ((0 : Int) <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z)) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH18 : (OrderTable table)) (PreH19 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH20 : ((Zlength (before)) = (3 * z))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH23 : (OrderAt z (OrderFor (z)))) (PreH24 : (CakeOrder (OrderFor (z)))) (PreH25 : (retval = (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ (retval = (0 : Int)) ” &&
  “ (TryOrderSpec a b c (OrderFor (z)) None) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ” &&
  “ (retval = (0 : Int)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)

noncomputable def solver_entail_wit_7_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (raw_result : (List Int)) (result : (List Int)) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result)))) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1)))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH9 : (Pre a b c)) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : ((0 : Int) <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z)) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH19 : (OrderTable table)) (PreH20 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH21 : ((Zlength (before)) = (3 * z))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH24 : (OrderAt z (OrderFor (z)))) (PreH25 : (CakeOrder (OrderFor (z)))) (PreH26 : (retval = (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.full out_pre 6 raw_result)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ (retval = (0 : Int)) ” &&
  “ (TryOrderSpec a b c (OrderFor (z)) None) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ” &&
  “ (retval = (0 : Int)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)

noncomputable def solver_entail_wit_8_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : ((0 : Int) <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z)) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH18 : (OrderTable table)) (PreH19 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH20 : ((Zlength (before)) = (3 * z))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH23 : (OrderAt z (OrderFor (z)))) (PreH24 : (CakeOrder (OrderFor (z)))) (PreH25 : (retval ≠ (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  EX raw_result : (List Int), EX result : (List Int),
  “ (retval = 1) ” &&
  “ (TryOrderSpec a b c (OrderFor (z)) (Some (result))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1))) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.full out_pre 6 raw_result)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)

noncomputable def solver_entail_wit_8_2 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (raw_result : (List Int)) (result : (List Int)) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result)))) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1)))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH9 : (Pre a b c)) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : ((0 : Int) <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z)) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH19 : (OrderTable table)) (PreH20 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH21 : ((Zlength (before)) = (3 * z))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH24 : (OrderAt z (OrderFor (z)))) (PreH25 : (CakeOrder (OrderFor (z)))) (PreH26 : (retval ≠ (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.full out_pre 6 raw_result)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ (retval = 1) ” &&
  “ (TryOrderSpec a b c (OrderFor (z)) (Some (result))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1))) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ” &&
  “ (retval ≠ (0 : Int)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.full out_pre 6 raw_result)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)

noncomputable def solver_entail_wit_9 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (before_2 : (List Int)) (after_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (raw_result_2 : (List Int)) (result_2 : (List Int)) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result_2)))) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result_2 (0 : Int)) = ((Znth i result_2 (0 : Int)) + 1)))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH9 : (Pre a b c)) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : ((0 : Int) <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z)) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH19 : (OrderTable table_2)) (PreH20 : (table_2 = (before_2 ++ ((OrderFor (z)) ++ after_2)))) (PreH21 : ((Zlength (before_2)) = (3 * z))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after_2)) = (18 - (3 * (z + 1))))) (PreH24 : (OrderAt z (OrderFor (z)))) (PreH25 : (CakeOrder (OrderFor (z)))) (PreH26 : (retval ≠ (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.full out_pre 6 raw_result_2)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before_2)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after_2)
|--
  EX before : (List Int), EX after : (List Int), EX table : (List Int), EX raw_result : (List Int), EX result : (List Int),
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (retval = 1) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (Spec a b c (Some (result))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result (0 : Int)) = ((Znth j result (0 : Int)) + 1))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full out_pre 6 raw_result)
  ** (intArray.full ( &( "orders" ) ) 18 table)
) \/
(
forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (before_2 : (List Int)) (after_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (raw_result_2 : (List Int)) (result_2 : (List Int)) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) (Some (result_2)))) (PreH3 : forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result_2 (0 : Int)) = ((Znth i result_2 (0 : Int)) + 1)))) (PreH4 : (3 <= (Zlength (a)))) (PreH5 : ((Zlength (a)) <= 200000)) (PreH6 : ((Zlength (b)) = (Zlength (a)))) (PreH7 : ((Zlength (c)) = (Zlength (a)))) (PreH8 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH9 : (Pre a b c)) (PreH10 : (n_pre = (Zlength (a)))) (PreH11 : (total = (sum (a)))) (PreH12 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH13 : (1 <= need)) (PreH14 : (need <= 200000000000)) (PreH15 : ((0 : Int) <= z)) (PreH16 : (z < 6)) (PreH17 : (FailedOrders a b c z)) (PreH18 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH19 : (OrderTable table_2)) (PreH20 : (table_2 = (before_2 ++ ((OrderFor (z)) ++ after_2)))) (PreH21 : ((Zlength (before_2)) = (3 * z))) (PreH22 : ((Zlength ((OrderFor (z)))) = 3)) (PreH23 : ((Zlength (after_2)) = (18 - (3 * (z + 1))))) (PreH24 : (OrderAt z (OrderFor (z)))) (PreH25 : (CakeOrder (OrderFor (z)))) (PreH26 : (retval ≠ (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before_2)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after_2)
|--
  EX before : (List Int), EX after : (List Int), EX result : (List Int),
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (retval = 1) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (Spec a b c (Some (result))) ” &&
  “ forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result_2 (0 : Int)) = ((Znth j result (0 : Int)) + 1))) ” &&
  “ (OrderTable (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "orders" ) ) 18 (before ++ ((OrderFor (z)) ++ after)))
)

noncomputable def solver_entail_wit_10 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : ((0 : Int) <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z)) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH18 : (OrderTable table_2)) (PreH19 : (table_2 = (before ++ ((OrderFor (z)) ++ after)))) (PreH20 : ((Zlength (before)) = (3 * z))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH23 : (OrderAt z (OrderFor (z)))) (PreH24 : (CakeOrder (OrderFor (z)))) (PreH25 : (retval = (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  EX table : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (retval = (0 : Int)) ” &&
  “ (OrderTable table) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (FailedOrders a b c (z + 1)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
) \/
(
forall (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (retval : Int) (PreH1 : (retval = (0 : Int))) (PreH2 : (TryOrderSpec a b c (OrderFor (z)) None)) (PreH3 : (3 <= (Zlength (a)))) (PreH4 : ((Zlength (a)) <= 200000)) (PreH5 : ((Zlength (b)) = (Zlength (a)))) (PreH6 : ((Zlength (c)) = (Zlength (a)))) (PreH7 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH8 : (Pre a b c)) (PreH9 : (n_pre = (Zlength (a)))) (PreH10 : (total = (sum (a)))) (PreH11 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH12 : (1 <= need)) (PreH13 : (need <= 200000000000)) (PreH14 : ((0 : Int) <= z)) (PreH15 : (z < 6)) (PreH16 : (FailedOrders a b c z)) (PreH17 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH18 : (OrderTable table_2)) (PreH19 : (table_2 = (before ++ ((OrderFor (z)) ++ after)))) (PreH20 : ((Zlength (before)) = (3 * z))) (PreH21 : ((Zlength ((OrderFor (z)))) = 3)) (PreH22 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH23 : (OrderAt z (OrderFor (z)))) (PreH24 : (CakeOrder (OrderFor (z)))) (PreH25 : (retval = (0 : Int))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  EX table : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (retval = (0 : Int)) ” &&
  “ (OrderTable table) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (FailedOrders a b c (z + 1)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ( &( "orders" ) ) 18 table)
)

noncomputable def solver_entail_wit_11 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : ((0 : Int) <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = (0 : Int))) (PreH14 : (OrderTable table_2)) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH16 : (FailedOrders a b c (z + 1))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table_2)
|--
  EX table : (List Int),
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= (z + 1)) ” &&
  “ ((z + 1) <= 6) ” &&
  “ (OrderTable table) ” &&
  “ (FailedOrders a b c (z + 1)) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
) \/
(
forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : ((0 : Int) <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = (0 : Int))) (PreH14 : (OrderTable table_2)) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH16 : (FailedOrders a b c (z + 1))) ,
  TT && emp 
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”
  &&  emp
)

noncomputable def solver_entail_wit_11_split_goal_1 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : (Pre a b c)) (PreH6 : (n_pre = (Zlength (a)))) (PreH7 : (total = (sum (a)))) (PreH8 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH9 : (1 <= need)) (PreH10 : (need <= 200000000000)) (PreH11 : ((0 : Int) <= z)) (PreH12 : (z < 6)) (PreH13 : (ok = (0 : Int))) (PreH14 : (OrderTable table_2)) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH16 : (FailedOrders a b c (z + 1))) ,
  forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))

noncomputable def solver_entail_wit_12 : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (z : Int) (need : Int) (total : Int) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2)) (PreH16 : (FailedOrders a b c z)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table_2)
|--
  EX table : (List Int),
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (FailedOrders a b c 6) ” &&
  “ (Spec a b c None) ” &&
  “ (OrderTable table) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 table)
) \/
(
forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (z : Int) (need : Int) (total : Int) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2)) (PreH16 : (FailedOrders a b c z)) ,
  TT && emp 
|--
  “ (Spec a b c None) ” &&
  “ (FailedOrders a b c 6) ”
  &&  emp
)

noncomputable def solver_entail_wit_12_split_goal_1 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (z : Int) (need : Int) (total : Int) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2)) (PreH16 : (FailedOrders a b c z)) ,
  (Spec a b c None)

noncomputable def solver_entail_wit_12_split_goal_2 : Prop :=
  forall (n_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table_2 : (List Int)) (z : Int) (need : Int) (total : Int) (PreH1 : (z >= 6)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : (total = (sum (a)))) (PreH10 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH11 : (1 <= need)) (PreH12 : (need <= 200000000000)) (PreH13 : ((0 : Int) <= z)) (PreH14 : (z <= 6)) (PreH15 : (OrderTable table_2)) (PreH16 : (FailedOrders a b c z)) ,
  (FailedOrders a b c 6)

noncomputable def solver_return_wit_1 : Prop :=
  forall (out_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (total : Int) (need : Int) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH3 : (FailedOrders a b c 6)) (PreH4 : (Spec a b c None)) (PreH5 : (OrderTable table)) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (Spec a b c None) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)

noncomputable def solver_return_wit_2 : Prop :=
  (
forall (out_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (result_2 : (List Int)) (raw_result_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH3 : ((0 : Int) <= z)) (PreH4 : (z < 6)) (PreH5 : (ok = 1)) (PreH6 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH7 : (Spec a b c (Some (result_2)))) (PreH8 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result_2 (0 : Int)) = ((Znth j result_2 (0 : Int)) + 1)))) (PreH9 : (OrderTable table)) (PreH10 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH11 : ((Zlength (before)) = (3 * z))) (PreH12 : ((Zlength ((OrderFor (z)))) = 3)) (PreH13 : ((Zlength (after)) = (18 - (3 * (z + 1))))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full out_pre 6 raw_result_2)
|--
  EX raw_result : (List Int), EX result : (List Int),
  “ (1 = 1) ” &&
  “ (Spec a b c (Some (result))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result (0 : Int)) = ((Znth i result (0 : Int)) + 1))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full out_pre 6 raw_result)
) \/
(
forall (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (result_2 : (List Int)) (raw_result_2 : (List Int)) (total : Int) (need : Int) (z : Int) (ok : Int) (ordp : Int) (PreH1 : (total = (sum (a)))) (PreH2 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH3 : ((0 : Int) <= z)) (PreH4 : (z < 6)) (PreH5 : (ok = 1)) (PreH6 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH7 : (Spec a b c (Some (result_2)))) (PreH8 : forall (j : Int) , ((((0 : Int) <= j) ∧ (j < 6)) -> ((Znth j raw_result_2 (0 : Int)) = ((Znth j result_2 (0 : Int)) + 1)))) (PreH9 : (OrderTable table)) (PreH10 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH11 : ((Zlength (before)) = (3 * z))) (PreH12 : ((Zlength ((OrderFor (z)))) = 3)) (PreH13 : ((Zlength (after)) = (18 - (3 * (z + 1))))) ,
  TT && emp 
|--
  EX result : (List Int),
  “ (Spec a b c (Some (result))) ” &&
  “ forall (i : Int) , ((((0 : Int) <= i) ∧ (i < 6)) -> ((Znth i raw_result_2 (0 : Int)) = ((Znth i result (0 : Int)) + 1))) ”
  &&  emp
)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (row0_addr : Int) (total : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (3 <= (Zlength (a)))) (PreH3 : ((Zlength (a)) <= 200000)) (PreH4 : ((Zlength (b)) = (Zlength (a)))) (PreH5 : ((Zlength (c)) = (Zlength (a)))) (PreH6 : forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH7 : (Pre a b c)) (PreH8 : (n_pre = (Zlength (a)))) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (total = (sum ((sublist ((0 : Int)) (i) (a)))))) (PreH12 : ((0 : Int) <= total)) (PreH13 : (total <= 200000000000)) ,
  (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (int64Array.full row0_addr n_pre a)
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))
|--
  “ (i < n_pre) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (total = (sum ((sublist ((0 : Int)) (i) (a))))) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 200000000000) ”
  &&  (((row0_addr + (i * sizeof(INT64)))) # Int64 |-> ((Znth i a (0 : Int))))
  ** (int64Array.missing_i row0_addr i (0 : Int) n_pre a)
  ** (int64PtrArray2.missing_i v_pre 3 (0 : Int) row0_addr (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (((v_pre + ((0 : Int) * sizeof(PTR)))) # Ptr |-> (row0_addr))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.full ( &( "orders" ) ) 18 ((0 : Int) :: (1 :: (2 :: ((0 : Int) :: (2 :: (1 :: (1 :: ((0 : Int) :: (2 :: (1 :: (2 :: ((0 : Int) :: (2 :: ((0 : Int) :: (1 :: (2 :: (1 :: ((0 : Int) :: (@List.nil Int))))))))))))))))))))

noncomputable def solver_partial_solve_wit_2_pure : Prop :=
  (
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ordp : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need)) (PreH11 : (need <= 200000000000)) (PreH12 : ((0 : Int) <= z)) (PreH13 : (z < 6)) (PreH14 : (FailedOrders a b c z)) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH16 : (OrderTable table)) (PreH17 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH18 : ((Zlength (before)) = (3 * z))) (PreH19 : ((Zlength ((OrderFor (z)))) = 3)) (PreH20 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH21 : (OrderAt z (OrderFor (z)))) (PreH22 : (CakeOrder (OrderFor (z)))) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** ((( &( "ordp" ) )) # Ptr |-> (ordp))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (CakeOrder (OrderFor (z))) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ”
) \/
(
forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ordp : Int) (PreH1 : (need <= 9223372036854775807)) (PreH2 : (total <= 9223372036854775807)) (PreH3 : (need >= (-9223372036854775808))) (PreH4 : (total >= (-9223372036854775808))) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (z >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (3 <= (Zlength (a)))) (PreH10 : ((Zlength (a)) <= 200000)) (PreH11 : ((Zlength (b)) = (Zlength (a)))) (PreH12 : ((Zlength (c)) = (Zlength (a)))) (PreH13 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH14 : (Pre a b c)) (PreH15 : (n_pre = (Zlength (a)))) (PreH16 : (total = (sum (a)))) (PreH17 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH18 : (1 <= need)) (PreH19 : (need <= 200000000000)) (PreH20 : ((0 : Int) <= z)) (PreH21 : (z < 6)) (PreH22 : (FailedOrders a b c z)) (PreH23 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH24 : (OrderTable table)) (PreH25 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH26 : ((Zlength (before)) = (3 * z))) (PreH27 : ((Zlength ((OrderFor (z)))) = 3)) (PreH28 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH29 : (OrderAt z (OrderFor (z)))) (PreH30 : (CakeOrder (OrderFor (z)))) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** ((( &( "ordp" ) )) # Ptr |-> (ordp))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”
)

noncomputable def solver_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (row0_addr : Int) (total : Int) (need : Int) (z : Int) (ordp : Int) (PreH1 : (need <= 9223372036854775807)) (PreH2 : (total <= 9223372036854775807)) (PreH3 : (need >= (-9223372036854775808))) (PreH4 : (total >= (-9223372036854775808))) (PreH5 : (z <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (z >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (3 <= (Zlength (a)))) (PreH10 : ((Zlength (a)) <= 200000)) (PreH11 : ((Zlength (b)) = (Zlength (a)))) (PreH12 : ((Zlength (c)) = (Zlength (a)))) (PreH13 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH14 : (Pre a b c)) (PreH15 : (n_pre = (Zlength (a)))) (PreH16 : (total = (sum (a)))) (PreH17 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH18 : (1 <= need)) (PreH19 : (need <= 200000000000)) (PreH20 : ((0 : Int) <= z)) (PreH21 : (z < 6)) (PreH22 : (FailedOrders a b c z)) (PreH23 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH24 : (OrderTable table)) (PreH25 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH26 : ((Zlength (before)) = (3 * z))) (PreH27 : ((Zlength ((OrderFor (z)))) = 3)) (PreH28 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH29 : (OrderAt z (OrderFor (z)))) (PreH30 : (CakeOrder (OrderFor (z)))) ,
  ((( &( "ok" ) )) # Int |->_)
  ** ((( &( "v" ) )) # Ptr |-> (v_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "out" ) )) # Ptr |-> (out_pre))
  ** ((( &( "row0" ) )) # Ptr |-> (row0_addr))
  ** ((( &( "total" ) )) # Int64 |-> (total))
  ** ((( &( "need" ) )) # Int64 |-> (need))
  ** ((( &( "z" ) )) # Int |-> (z))
  ** ((( &( "ordp" ) )) # Ptr |-> (ordp))
  ** (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ”

noncomputable def solver_partial_solve_wit_2_aux : Prop :=
  forall (out_pre : Int) (n_pre : Int) (v_pre : Int) (c : (List Int)) (b : (List Int)) (a : (List Int)) (table : (List Int)) (before : (List Int)) (after : (List Int)) (total : Int) (need : Int) (z : Int) (ordp : Int) (PreH1 : (3 <= (Zlength (a)))) (PreH2 : ((Zlength (a)) <= 200000)) (PreH3 : ((Zlength (b)) = (Zlength (a)))) (PreH4 : ((Zlength (c)) = (Zlength (a)))) (PreH5 : forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000)))) (PreH6 : (Pre a b c)) (PreH7 : (n_pre = (Zlength (a)))) (PreH8 : (total = (sum (a)))) (PreH9 : (need = (Z.quot ((sum (a)) + 2) 3))) (PreH10 : (1 <= need)) (PreH11 : (need <= 200000000000)) (PreH12 : ((0 : Int) <= z)) (PreH13 : (z < 6)) (PreH14 : (FailedOrders a b c z)) (PreH15 : (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT))))) (PreH16 : (OrderTable table)) (PreH17 : (table = (before ++ ((OrderFor (z)) ++ after)))) (PreH18 : ((Zlength (before)) = (3 * z))) (PreH19 : ((Zlength ((OrderFor (z)))) = 3)) (PreH20 : ((Zlength (after)) = (18 - (3 * (z + 1))))) (PreH21 : (OrderAt z (OrderFor (z)))) (PreH22 : (CakeOrder (OrderFor (z)))) ,
  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)
|--
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row : Int) , forall (col : Int) , ((((((0 : Int) <= row) ∧ (row < 3)) ∧ ((0 : Int) <= col)) ∧ (col < (Zlength (a)))) -> ((1 <= (Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col) ((Znth (row) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (CakeOrder (OrderFor (z))) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ (3 <= (Zlength (a))) ” &&
  “ ((Zlength (a)) <= 200000) ” &&
  “ ((Zlength (b)) = (Zlength (a))) ” &&
  “ ((Zlength (c)) = (Zlength (a))) ” &&
  “ forall (row_2 : Int) , forall (col_2 : Int) , ((((((0 : Int) <= row_2) ∧ (row_2 < 3)) ∧ ((0 : Int) <= col_2)) ∧ (col_2 < (Zlength (a)))) -> ((1 <= (Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int)))) ∧ ((Znth (col_2) ((Znth (row_2) ((a :: (b :: (c :: (@List.nil (List Int)))))) ((@List.nil Int)))) ((0 : Int))) <= 1000000))) ” &&
  “ (Pre a b c) ” &&
  “ (n_pre = (Zlength (a))) ” &&
  “ (total = (sum (a))) ” &&
  “ (need = (Z.quot ((sum (a)) + 2) 3)) ” &&
  “ (1 <= need) ” &&
  “ (need <= 200000000000) ” &&
  “ ((0 : Int) <= z) ” &&
  “ (z < 6) ” &&
  “ (FailedOrders a b c z) ” &&
  “ (ordp = (( &( "orders" ) ) + ((3 * z) * sizeof(INT)))) ” &&
  “ (OrderTable table) ” &&
  “ (table = (before ++ ((OrderFor (z)) ++ after))) ” &&
  “ ((Zlength (before)) = (3 * z)) ” &&
  “ ((Zlength ((OrderFor (z)))) = 3) ” &&
  “ ((Zlength (after)) = (18 - (3 * (z + 1)))) ” &&
  “ (OrderAt z (OrderFor (z))) ” &&
  “ (CakeOrder (OrderFor (z))) ”
  &&  (int64PtrArray2.full v_pre 3 (a :: (b :: (c :: (@List.nil (List Int))))))
  ** (intArray.full ordp 3 (OrderFor (z)))
  ** (intArray.undef_full out_pre 6)
  ** (intArray.seg ( &( "orders" ) ) (0 : Int) (3 * z) before)
  ** (intArray.seg ( &( "orders" ) ) (3 * (z + 1)) 18 after)

noncomputable def solver_partial_solve_wit_2 : Prop := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_try_order_safety_wit_1 : try_order_safety_wit_1
  proof_of_try_order_safety_wit_2 : try_order_safety_wit_2
  proof_of_try_order_safety_wit_3 : try_order_safety_wit_3
  proof_of_try_order_safety_wit_4 : try_order_safety_wit_4
  proof_of_try_order_safety_wit_5 : try_order_safety_wit_5
  proof_of_try_order_safety_wit_6 : try_order_safety_wit_6
  proof_of_try_order_safety_wit_7 : try_order_safety_wit_7
  proof_of_try_order_safety_wit_8 : try_order_safety_wit_8
  proof_of_try_order_safety_wit_9 : try_order_safety_wit_9
  proof_of_try_order_safety_wit_10 : try_order_safety_wit_10
  proof_of_try_order_safety_wit_12 : try_order_safety_wit_12
  proof_of_try_order_safety_wit_13 : try_order_safety_wit_13
  proof_of_try_order_safety_wit_14 : try_order_safety_wit_14
  proof_of_try_order_safety_wit_15 : try_order_safety_wit_15
  proof_of_try_order_safety_wit_16 : try_order_safety_wit_16
  proof_of_try_order_safety_wit_17 : try_order_safety_wit_17
  proof_of_try_order_safety_wit_18 : try_order_safety_wit_18
  proof_of_try_order_safety_wit_19 : try_order_safety_wit_19
  proof_of_try_order_safety_wit_21 : try_order_safety_wit_21
  proof_of_try_order_safety_wit_22 : try_order_safety_wit_22
  proof_of_try_order_safety_wit_23 : try_order_safety_wit_23
  proof_of_try_order_safety_wit_24 : try_order_safety_wit_24
  proof_of_try_order_safety_wit_25 : try_order_safety_wit_25
  proof_of_try_order_safety_wit_26 : try_order_safety_wit_26
  proof_of_try_order_safety_wit_27 : try_order_safety_wit_27
  proof_of_try_order_safety_wit_28 : try_order_safety_wit_28
  proof_of_try_order_safety_wit_29 : try_order_safety_wit_29
  proof_of_try_order_safety_wit_30 : try_order_safety_wit_30
  proof_of_try_order_safety_wit_31 : try_order_safety_wit_31
  proof_of_try_order_safety_wit_32 : try_order_safety_wit_32
  proof_of_try_order_safety_wit_33 : try_order_safety_wit_33
  proof_of_try_order_return_wit_2 : try_order_return_wit_2
  proof_of_try_order_return_wit_3 : try_order_return_wit_3
  proof_of_try_order_partial_solve_wit_1 : try_order_partial_solve_wit_1
  proof_of_try_order_partial_solve_wit_2 : try_order_partial_solve_wit_2
  proof_of_try_order_partial_solve_wit_3 : try_order_partial_solve_wit_3
  proof_of_try_order_partial_solve_wit_4 : try_order_partial_solve_wit_4
  proof_of_try_order_partial_solve_wit_5 : try_order_partial_solve_wit_5
  proof_of_try_order_partial_solve_wit_6 : try_order_partial_solve_wit_6
  proof_of_try_order_partial_solve_wit_7 : try_order_partial_solve_wit_7
  proof_of_try_order_partial_solve_wit_8 : try_order_partial_solve_wit_8
  proof_of_try_order_partial_solve_wit_9 : try_order_partial_solve_wit_9
  proof_of_try_order_partial_solve_wit_10 : try_order_partial_solve_wit_10
  proof_of_try_order_partial_solve_wit_11 : try_order_partial_solve_wit_11
  proof_of_try_order_partial_solve_wit_12 : try_order_partial_solve_wit_12
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_safety_wit_20 : solver_safety_wit_20
  proof_of_solver_safety_wit_21 : solver_safety_wit_21
  proof_of_solver_safety_wit_22 : solver_safety_wit_22
  proof_of_solver_safety_wit_24 : solver_safety_wit_24
  proof_of_solver_safety_wit_25 : solver_safety_wit_25
  proof_of_solver_safety_wit_26 : solver_safety_wit_26
  proof_of_solver_safety_wit_27 : solver_safety_wit_27
  proof_of_solver_safety_wit_28 : solver_safety_wit_28
  proof_of_solver_safety_wit_29 : solver_safety_wit_29
  proof_of_solver_safety_wit_30 : solver_safety_wit_30
  proof_of_solver_safety_wit_31 : solver_safety_wit_31
  proof_of_solver_safety_wit_32 : solver_safety_wit_32
  proof_of_solver_safety_wit_33 : solver_safety_wit_33
  proof_of_solver_safety_wit_34 : solver_safety_wit_34
  proof_of_solver_safety_wit_35 : solver_safety_wit_35
  proof_of_solver_safety_wit_36 : solver_safety_wit_36
  proof_of_solver_safety_wit_37 : solver_safety_wit_37
  proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1
  proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2
  proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1
  proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_try_order_safety_wit_11 : try_order_safety_wit_11
  proof_of_try_order_safety_wit_20 : try_order_safety_wit_20
  proof_of_try_order_entail_wit_1 : try_order_entail_wit_1
  proof_of_try_order_entail_wit_2 : try_order_entail_wit_2
  proof_of_try_order_entail_wit_3 : try_order_entail_wit_3
  proof_of_try_order_entail_wit_4 : try_order_entail_wit_4
  proof_of_try_order_entail_wit_5_1 : try_order_entail_wit_5_1
  proof_of_try_order_entail_wit_5_2 : try_order_entail_wit_5_2
  proof_of_try_order_entail_wit_6 : try_order_entail_wit_6
  proof_of_try_order_entail_wit_7 : try_order_entail_wit_7
  proof_of_try_order_entail_wit_8 : try_order_entail_wit_8
  proof_of_try_order_entail_wit_9 : try_order_entail_wit_9
  proof_of_try_order_entail_wit_10 : try_order_entail_wit_10
  proof_of_try_order_entail_wit_11 : try_order_entail_wit_11
  proof_of_try_order_entail_wit_12 : try_order_entail_wit_12
  proof_of_try_order_entail_wit_13 : try_order_entail_wit_13
  proof_of_try_order_entail_wit_14 : try_order_entail_wit_14
  proof_of_try_order_entail_wit_15 : try_order_entail_wit_15
  proof_of_try_order_entail_wit_16 : try_order_entail_wit_16
  proof_of_try_order_return_wit_1 : try_order_return_wit_1
  proof_of_solver_safety_wit_23 : solver_safety_wit_23
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4 : solver_entail_wit_4
  proof_of_solver_entail_wit_5 : solver_entail_wit_5
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_9 : solver_entail_wit_9
  proof_of_solver_entail_wit_10 : solver_entail_wit_10
  proof_of_solver_entail_wit_11 : solver_entail_wit_11
  proof_of_solver_entail_wit_12 : solver_entail_wit_12
  proof_of_solver_return_wit_2 : solver_return_wit_2
  proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P040_1983C_have_your_cake_and_eat_it_too_goal
