From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib.
Local Open Scope sac.

(*----- Function mulmod -----*)

Definition mulmod_safety_wit_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  ((( &( "r" ) )) # UInt64  |->_)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mulmod_safety_wit_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  ((( &( "r" ) )) # UInt64  |-> 0)
  **  ((( &( "a" ) )) # UInt64  |-> a_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
|--
  “ (modulus_pre <> 0) ”
.

Definition mulmod_safety_wit_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  ((( &( "r" ) )) # UInt64  |-> 0)
  **  ((( &( "a" ) )) # UInt64  |-> (a_pre % ( modulus_pre ) ))
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
|--
  “ (modulus_pre <> 0) ”
.

Definition mulmod_safety_wit_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= a_pre)) (PreH7 : (0 <= b_pre)) (PreH8 : (0 <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH15 : (b <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_5 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((r + a ) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> ((r + a ) - modulus_pre ))
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_6 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((r + a ) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> ((r + a ) - modulus_pre ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_7 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((r + a ) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> (r + a ))
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_8 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((r + a ) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> (r + a ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_9 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= a_pre)) (PreH7 : (0 <= b_pre)) (PreH8 : (0 <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH15 : (b <> 0)) (PreH16 : ((Z.land b 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_10 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= a_pre)) (PreH7 : (0 <= b_pre)) (PreH8 : (0 <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH15 : (b <> 0)) (PreH16 : ((Z.land b 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_11 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> ((r + a ) - modulus_pre ))
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_12 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> ((r + a ) - modulus_pre ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_13 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> (r + a ))
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_14 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> (r + a ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_15 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_16 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_17 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> ((r + a ) - modulus_pre ))
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_18 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> ((r + a ) - modulus_pre ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_19 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> (r + a ))
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_20 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> (r + a ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_safety_wit_21 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition mulmod_safety_wit_22 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "a" ) )) # UInt64  |-> (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mulmod_entail_wit_1 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= (a_pre % ( modulus_pre ) )) ”
  &&  “ ((a_pre % ( modulus_pre ) ) < modulus_pre) ”
  &&  “ (0 <= (b_pre % ( modulus_pre ) )) ”
  &&  “ ((b_pre % ( modulus_pre ) ) < modulus_pre) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre (a_pre % ( modulus_pre ) ) (b_pre % ( modulus_pre ) ) 0 ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 (a0 % ( modulus0 ) ) (b0 % ( modulus0 ) ) 0 ) ”
  &&  “ ((b0 % ( modulus0 ) ) < modulus0) ”
  &&  “ (0 <= (b0 % ( modulus0 ) )) ”
  &&  “ ((a0 % ( modulus0 ) ) < modulus0) ”
  &&  “ (0 <= (a0 % ( modulus0 ) )) ”
  &&  emp
).

Definition mulmod_entail_wit_1_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  (MulLoopState a0 b0 modulus0 (a0 % ( modulus0 ) ) (b0 % ( modulus0 ) ) 0 )
.

Definition mulmod_entail_wit_1_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  ((b0 % ( modulus0 ) ) < modulus0)
.

Definition mulmod_entail_wit_1_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  (0 <= (b0 % ( modulus0 ) ))
.

Definition mulmod_entail_wit_1_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  ((a0 % ( modulus0 ) ) < modulus0)
.

Definition mulmod_entail_wit_1_split_goal_5 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= a0)) (PreH7 : (a0 <= UINT64_MAX)) (PreH8 : (0 <= b0)) (PreH9 : (b0 <= UINT64_MAX)),
  (0 <= (a0 % ( modulus0 ) ))
.

Definition mulmod_entail_wit_2_1 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre )) ”
  &&  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ) < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ ((Z.shiftr b 1) < modulus_pre) ”
  &&  “ (0 <= ((r + a ) - modulus_pre )) ”
  &&  “ (((r + a ) - modulus_pre ) < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ) (Z.shiftr b 1) ((r + a ) - modulus_pre ) ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) (Z.shiftr b 1) ((r + a ) - modulus0 ) ) ”
  &&  “ ((Z.shiftr b 1) < modulus0) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) < modulus0) ”
  &&  emp
).

Definition mulmod_entail_wit_2_1_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (MulLoopState a0 b0 modulus0 ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) (Z.shiftr b 1) ((r + a ) - modulus0 ) )
.

Definition mulmod_entail_wit_2_1_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((Z.shiftr b 1) < modulus0)
.

Definition mulmod_entail_wit_2_1_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (0 <= (Z.shiftr b 1))
.

Definition mulmod_entail_wit_2_1_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) < modulus0)
.

Definition mulmod_entail_wit_2_2 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre )) ”
  &&  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ) < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ ((Z.shiftr b 1) < modulus_pre) ”
  &&  “ (0 <= (r + a )) ”
  &&  “ ((r + a ) < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ) (Z.shiftr b 1) (r + a ) ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) (Z.shiftr b 1) (r + a ) ) ”
  &&  “ ((Z.shiftr b 1) < modulus0) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) < modulus0) ”
  &&  emp
).

Definition mulmod_entail_wit_2_2_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (MulLoopState a0 b0 modulus0 ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) (Z.shiftr b 1) (r + a ) )
.

Definition mulmod_entail_wit_2_2_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((Z.shiftr b 1) < modulus0)
.

Definition mulmod_entail_wit_2_2_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (0 <= (Z.shiftr b 1))
.

Definition mulmod_entail_wit_2_2_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) < modulus0)
.

Definition mulmod_entail_wit_2_3 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre )) ”
  &&  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ) < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ ((Z.shiftr b 1) < modulus_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre ) (Z.shiftr b 1) r ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) (Z.shiftr b 1) r ) ”
  &&  “ ((Z.shiftr b 1) < modulus0) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) < modulus0) ”
  &&  emp
).

Definition mulmod_entail_wit_2_3_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  (MulLoopState a0 b0 modulus0 ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) (Z.shiftr b 1) r )
.

Definition mulmod_entail_wit_2_3_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  ((Z.shiftr b 1) < modulus0)
.

Definition mulmod_entail_wit_2_3_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  (0 <= (Z.shiftr b 1))
.

Definition mulmod_entail_wit_2_3_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus0 ) < modulus0)
.

Definition mulmod_entail_wit_2_4 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ ((Z.shiftr b 1) < modulus_pre) ”
  &&  “ (0 <= ((r + a ) - modulus_pre )) ”
  &&  “ (((r + a ) - modulus_pre ) < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) ((r + a ) - modulus_pre ) ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) ((r + a ) - modulus0 ) ) ”
  &&  “ ((Z.shiftr b 1) < modulus0) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  emp
).

Definition mulmod_entail_wit_2_4_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (MulLoopState a0 b0 modulus0 (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) ((r + a ) - modulus0 ) )
.

Definition mulmod_entail_wit_2_4_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((Z.shiftr b 1) < modulus0)
.

Definition mulmod_entail_wit_2_4_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (0 <= (Z.shiftr b 1))
.

Definition mulmod_entail_wit_2_4_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
.

Definition mulmod_entail_wit_2_5 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ ((Z.shiftr b 1) < modulus_pre) ”
  &&  “ (0 <= (r + a )) ”
  &&  “ ((r + a ) < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) (r + a ) ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) (r + a ) ) ”
  &&  “ ((Z.shiftr b 1) < modulus0) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  emp
).

Definition mulmod_entail_wit_2_5_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (MulLoopState a0 b0 modulus0 (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) (r + a ) )
.

Definition mulmod_entail_wit_2_5_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  ((Z.shiftr b 1) < modulus0)
.

Definition mulmod_entail_wit_2_5_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (0 <= (Z.shiftr b 1))
.

Definition mulmod_entail_wit_2_5_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a ) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (0 <= a_pre)) (PreH9 : (0 <= b_pre)) (PreH10 : (0 <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : (0 <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH17 : (b <> 0)) (PreH18 : ((Z.land b 1) <> 0)),
  (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
.

Definition mulmod_entail_wit_2_6 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  “ ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ ((Z.shiftr b 1) < modulus_pre) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus_pre) ”
  &&  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) r ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  TT && emp 
|--
  “ (MulLoopState a0 b0 modulus0 (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) r ) ”
  &&  “ ((Z.shiftr b 1) < modulus0) ”
  &&  “ (0 <= (Z.shiftr b 1)) ”
  &&  “ (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  emp
).

Definition mulmod_entail_wit_2_6_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  (MulLoopState a0 b0 modulus0 (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) r )
.

Definition mulmod_entail_wit_2_6_split_goal_2 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  ((Z.shiftr b 1) < modulus0)
.

Definition mulmod_entail_wit_2_6_split_goal_3 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  (0 <= (Z.shiftr b 1))
.

Definition mulmod_entail_wit_2_6_split_goal_4 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (0 <= a_pre)) (PreH8 : (0 <= b_pre)) (PreH9 : (0 <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : (0 <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : (0 <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH16 : (b <> 0)) (PreH17 : ((Z.land b 1) = 0)),
  (0 <= (unsigned_last_nbits ((Z.shiftl a 1)) (64)))
.

Definition mulmod_return_wit_1 :=
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= a_pre)) (PreH7 : (0 <= b_pre)) (PreH8 : (0 <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH15 : (b = 0)),
  TT && emp 
|--
  “ (r = ((a0 * b0 ) % ( modulus0 ) )) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus0) ”
  &&  emp
) \/
(
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= a_pre)) (PreH7 : (0 <= b_pre)) (PreH8 : (0 <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH15 : (b = 0)),
  TT && emp 
|--
  “ (r = ((a0 * b0 ) % ( modulus0 ) )) ”
  &&  emp
).

Definition mulmod_return_wit_1_split_goal_1 :=
forall (modulus0: Z) (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (modulus_pre: Z) (r: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= a_pre)) (PreH7 : (0 <= b_pre)) (PreH8 : (0 <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r )) (PreH15 : (b = 0)),
  (r = ((a0 * b0 ) % ( modulus0 ) ))
.

(*----- Function powmod -----*)

Definition powmod_safety_wit_1 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  ((( &( "r" ) )) # UInt64  |->_)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
|--
  “ (modulus_pre <> 0) ”
.

Definition powmod_safety_wit_2 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  ((( &( "r" ) )) # UInt64  |->_)
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_safety_wit_3 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  ((( &( "r" ) )) # UInt64  |-> (1 % ( modulus_pre ) ))
  **  ((( &( "b" ) )) # UInt64  |-> b_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
|--
  “ (modulus_pre <> 0) ”
.

Definition powmod_safety_wit_4 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_safety_wit_5 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> retval_2)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> retval)
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition powmod_safety_wit_6 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> retval_2)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> retval)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_safety_wit_7 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> retval)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= 63) ”
  &&  “ (0 <= 1) ”
.

Definition powmod_safety_wit_8 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> retval)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition powmod_entail_wit_1 :=
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  TT && emp 
|--
  “ (base = b_pre) ”
  &&  “ (exponent = e_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= base) ”
  &&  “ (0 <= (b_pre % ( modulus_pre ) )) ”
  &&  “ ((b_pre % ( modulus_pre ) ) < modulus_pre) ”
  &&  “ (0 <= e_pre) ”
  &&  “ (e_pre <= exponent) ”
  &&  “ (0 <= (1 % ( modulus_pre ) )) ”
  &&  “ ((1 % ( modulus_pre ) ) < modulus_pre) ”
  &&  “ (PowLoopState base exponent modulus_pre (b_pre % ( modulus_pre ) ) e_pre (1 % ( modulus_pre ) ) ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  TT && emp 
|--
  “ (PowLoopState base exponent modulus0 (base % ( modulus0 ) ) exponent (1 % ( modulus0 ) ) ) ”
  &&  “ ((1 % ( modulus0 ) ) < modulus0) ”
  &&  “ (0 <= (1 % ( modulus0 ) )) ”
  &&  “ ((base % ( modulus0 ) ) < modulus0) ”
  &&  “ (0 <= (base % ( modulus0 ) )) ”
  &&  emp
).

Definition powmod_entail_wit_1_split_goal_1 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  (PowLoopState base exponent modulus0 (base % ( modulus0 ) ) exponent (1 % ( modulus0 ) ) )
.

Definition powmod_entail_wit_1_split_goal_2 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  ((1 % ( modulus0 ) ) < modulus0)
.

Definition powmod_entail_wit_1_split_goal_3 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  (0 <= (1 % ( modulus0 ) ))
.

Definition powmod_entail_wit_1_split_goal_4 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  ((base % ( modulus0 ) ) < modulus0)
.

Definition powmod_entail_wit_1_split_goal_5 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (base <= UINT64_MAX)) (PreH8 : (0 <= exponent)) (PreH9 : (exponent <= 100000000000000)),
  (0 <= (base % ( modulus0 ) ))
.

Definition powmod_entail_wit_2_1 :=
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (base = b_pre) ”
  &&  “ (exponent = e_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= base) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ ((Z.shiftr e 1) <= exponent) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < modulus_pre) ”
  &&  “ (PowLoopState base exponent modulus_pre retval_2 (Z.shiftr e 1) retval ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (PowLoopState base exponent modulus0 ((b * b ) % ( modulus0 ) ) (Z.shiftr e 1) ((r * b ) % ( modulus0 ) ) ) ”
  &&  “ ((Z.shiftr e 1) <= exponent) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  emp
).

Definition powmod_entail_wit_2_1_split_goal_1 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  (PowLoopState base exponent modulus0 ((b * b ) % ( modulus0 ) ) (Z.shiftr e 1) ((r * b ) % ( modulus0 ) ) )
.

Definition powmod_entail_wit_2_1_split_goal_2 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  ((Z.shiftr e 1) <= exponent)
.

Definition powmod_entail_wit_2_1_split_goal_3 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH5 : (0 <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : (0 <= base)) (PreH13 : (0 <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : (0 <= e)) (PreH16 : (e <= exponent)) (PreH17 : (0 <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r )) (PreH20 : (e <> 0)) (PreH21 : ((Z.land e 1) <> 0)),
  (0 <= (Z.shiftr e 1))
.

Definition powmod_entail_wit_2_2 :=
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (base = b_pre) ”
  &&  “ (exponent = e_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= base) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < modulus_pre) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  “ ((Z.shiftr e 1) <= exponent) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus_pre) ”
  &&  “ (PowLoopState base exponent modulus_pre retval (Z.shiftr e 1) r ) ”
  &&  emp
) \/
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (PowLoopState base exponent modulus0 ((b * b ) % ( modulus0 ) ) (Z.shiftr e 1) r ) ”
  &&  “ ((Z.shiftr e 1) <= exponent) ”
  &&  “ (0 <= (Z.shiftr e 1)) ”
  &&  emp
).

Definition powmod_entail_wit_2_2_split_goal_1 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  (PowLoopState base exponent modulus0 ((b * b ) % ( modulus0 ) ) (Z.shiftr e 1) r )
.

Definition powmod_entail_wit_2_2_split_goal_2 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  ((Z.shiftr e 1) <= exponent)
.

Definition powmod_entail_wit_2_2_split_goal_3 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((b * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) = 0)),
  (0 <= (Z.shiftr e 1))
.

Definition powmod_return_wit_1 :=
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e = 0)),
  TT && emp 
|--
  “ (r = ((base^exponent) % ( modulus0 ) )) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus0) ”
  &&  emp
) \/
(
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e = 0)),
  TT && emp 
|--
  “ (r = ((base^exponent) % ( modulus0 ) )) ”
  &&  emp
).

Definition powmod_return_wit_1_split_goal_1 :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e = 0)),
  (r = ((base^exponent) % ( modulus0 ) ))
.

Definition powmod_partial_solve_wit_1_pure :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e <> 0)) (PreH15 : ((Z.land e 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (r = r) ”
  &&  “ (b = b) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= UINT64_MAX) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
.

Definition powmod_partial_solve_wit_1_aux :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e <> 0)) (PreH15 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (r = r) ”
  &&  “ (b = b) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= r) ”
  &&  “ (r <= UINT64_MAX) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (base = b_pre) ”
  &&  “ (exponent = e_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= base) ”
  &&  “ (0 <= b) ”
  &&  “ (b < modulus_pre) ”
  &&  “ (0 <= e) ”
  &&  “ (e <= exponent) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus_pre) ”
  &&  “ (PowLoopState base exponent modulus_pre b e r ) ”
  &&  “ (e <> 0) ”
  &&  “ ((Z.land e 1) <> 0) ”
  &&  emp
.

Definition powmod_partial_solve_wit_1 := powmod_partial_solve_wit_1_pure -> powmod_partial_solve_wit_1_aux.

Definition powmod_partial_solve_wit_2_pure :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) <> 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> retval)
|--
  “ (b = b) ”
  &&  “ (b = b) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
.

Definition powmod_partial_solve_wit_2_aux :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (retval: Z) (PreH1 : (retval = ((r * b ) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : (0 <= base)) (PreH10 : (0 <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : (0 <= e)) (PreH13 : (e <= exponent)) (PreH14 : (0 <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r )) (PreH17 : (e <> 0)) (PreH18 : ((Z.land e 1) <> 0)),
  TT && emp 
|--
  “ (b = b) ”
  &&  “ (b = b) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (retval = ((r * b ) % ( modulus_pre ) )) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < modulus_pre) ”
  &&  “ (base = b_pre) ”
  &&  “ (exponent = e_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= base) ”
  &&  “ (0 <= b) ”
  &&  “ (b < modulus_pre) ”
  &&  “ (0 <= e) ”
  &&  “ (e <= exponent) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus_pre) ”
  &&  “ (PowLoopState base exponent modulus_pre b e r ) ”
  &&  “ (e <> 0) ”
  &&  “ ((Z.land e 1) <> 0) ”
  &&  emp
.

Definition powmod_partial_solve_wit_2 := powmod_partial_solve_wit_2_pure -> powmod_partial_solve_wit_2_aux.

Definition powmod_partial_solve_wit_3_pure :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e <> 0)) (PreH15 : ((Z.land e 1) = 0)),
  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "b" ) )) # UInt64  |-> b)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "r" ) )) # UInt64  |-> r)
|--
  “ (b = b) ”
  &&  “ (b = b) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
.

Definition powmod_partial_solve_wit_3_aux :=
forall (modulus0: Z) (exponent: Z) (base: Z) (b_pre: Z) (e_pre: Z) (modulus_pre: Z) (r: Z) (e: Z) (b: Z) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (0 <= base)) (PreH7 : (0 <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : (0 <= e)) (PreH10 : (e <= exponent)) (PreH11 : (0 <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r )) (PreH14 : (e <> 0)) (PreH15 : ((Z.land e 1) = 0)),
  TT && emp 
|--
  “ (b = b) ”
  &&  “ (b = b) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= UINT64_MAX) ”
  &&  “ (base = b_pre) ”
  &&  “ (exponent = e_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= base) ”
  &&  “ (0 <= b) ”
  &&  “ (b < modulus_pre) ”
  &&  “ (0 <= e) ”
  &&  “ (e <= exponent) ”
  &&  “ (0 <= r) ”
  &&  “ (r < modulus_pre) ”
  &&  “ (PowLoopState base exponent modulus_pre b e r ) ”
  &&  “ (e <> 0) ”
  &&  “ ((Z.land e 1) = 0) ”
  &&  emp
.

Definition powmod_partial_solve_wit_3 := powmod_partial_solve_wit_3_pure -> powmod_partial_solve_wit_3_aux.

(*----- Function gcd_ -----*)

Definition gcd__safety_wit_1 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b <> 0)),
  ((( &( "t" ) )) # UInt64  |->_)
  **  ((( &( "a" ) )) # UInt64  |-> a)
  **  ((( &( "b" ) )) # UInt64  |-> b)
|--
  “ (b <> 0) ”
.

Definition gcd__entail_wit_1 :=
(
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (0 <= a0)) (PreH4 : (a0 <= 100000000000000)) (PreH5 : (0 <= b0)) (PreH6 : (b0 <= 100000000000000)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (0 <= a0) ”
  &&  “ (0 <= b0) ”
  &&  “ (0 <= a_pre) ”
  &&  “ (a_pre <= 100000000000000) ”
  &&  “ (0 <= b_pre) ”
  &&  “ (b_pre <= 100000000000000) ”
  &&  “ (GcdLoopState a0 b0 a_pre b_pre ) ”
  &&  emp
) \/
(
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (0 <= a0)) (PreH4 : (a0 <= 100000000000000)) (PreH5 : (0 <= b0)) (PreH6 : (b0 <= 100000000000000)),
  TT && emp 
|--
  “ (GcdLoopState a0 b0 a0 b0 ) ”
  &&  emp
).

Definition gcd__entail_wit_1_split_goal_1 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (0 <= a0)) (PreH4 : (a0 <= 100000000000000)) (PreH5 : (0 <= b0)) (PreH6 : (b0 <= 100000000000000)),
  (GcdLoopState a0 b0 a0 b0 )
.

Definition gcd__entail_wit_2 :=
(
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b <> 0)),
  TT && emp 
|--
  “ (a0 = a_pre) ”
  &&  “ (b0 = b_pre) ”
  &&  “ (0 <= a0) ”
  &&  “ (0 <= b0) ”
  &&  “ (0 <= b) ”
  &&  “ (b <= 100000000000000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  “ ((a % ( b ) ) <= 100000000000000) ”
  &&  “ (GcdLoopState a0 b0 b (a % ( b ) ) ) ”
  &&  emp
) \/
(
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b <> 0)),
  TT && emp 
|--
  “ (GcdLoopState a0 b0 b (a % ( b ) ) ) ”
  &&  “ ((a % ( b ) ) <= 100000000000000) ”
  &&  “ (0 <= (a % ( b ) )) ”
  &&  emp
).

Definition gcd__entail_wit_2_split_goal_1 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b <> 0)),
  (GcdLoopState a0 b0 b (a % ( b ) ) )
.

Definition gcd__entail_wit_2_split_goal_2 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b <> 0)),
  ((a % ( b ) ) <= 100000000000000)
.

Definition gcd__entail_wit_2_split_goal_3 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b <> 0)),
  (0 <= (a % ( b ) ))
.

Definition gcd__return_wit_1 :=
(
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b = 0)),
  TT && emp 
|--
  “ (a = (Zgcd (a0) (b0))) ”
  &&  “ (0 <= a) ”
  &&  “ (a <= (a0 + b0 )) ”
  &&  emp
) \/
(
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b = 0)),
  TT && emp 
|--
  “ (a <= (a0 + b0 )) ”
  &&  “ (a = (Zgcd (a0) (b0))) ”
  &&  emp
).

Definition gcd__return_wit_1_split_goal_1 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b = 0)),
  (a <= (a0 + b0 ))
.

Definition gcd__return_wit_1_split_goal_2 :=
forall (b0: Z) (a0: Z) (a_pre: Z) (b_pre: Z) (b: Z) (a: Z) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (0 <= a0)) (PreH4 : (0 <= b0)) (PreH5 : (0 <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : (0 <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b )) (PreH10 : (b = 0)),
  (a = (Zgcd (a0) (b0)))
.

(*----- Function order -----*)

Definition order_safety_wit_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (x_pre = x0)) (PreH2 : (modulus_pre = modulus0)) (PreH3 : (phi_pre = phi0)) (PreH4 : (modulus0 <= 100000000000000)) (PreH5 : (OrderInput x0 modulus0 phi0 )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_safety_wit_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_safety_wit_3 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  ((( &( "q" ) )) # UInt64  |->_)
  **  ((( &( "t" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition order_safety_wit_4 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((q * q ) <= t)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000001)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (q <> 0) ”
.

Definition order_safety_wit_5 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((q * q ) <= t)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000001)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_safety_wit_6 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : (0 < t)) (PreH9 : (t <= phi_pre)) (PreH10 : (0 < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (q <> 0) ”
.

Definition order_safety_wit_7 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : (0 < t)) (PreH9 : (t <= phi_pre)) (PreH10 : (0 < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_safety_wit_8 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (q <> 0) ”
.

Definition order_safety_wit_9 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : (0 < t)) (PreH9 : (t <= phi_pre)) (PreH10 : (0 < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (q <> 0) ”
.

Definition order_safety_wit_10 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : (0 < t)) (PreH9 : (t <= phi_pre)) (PreH10 : (0 < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_safety_wit_11 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((ord % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (q <> 0) ”
.

Definition order_safety_wit_12 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : ((ord % ( q ) ) = 0)) (PreH5 : (x0 = x_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (phi0 = phi_pre)) (PreH8 : (1 < modulus_pre)) (PreH9 : (modulus_pre <= 100000000000000)) (PreH10 : (2 <= q)) (PreH11 : (q <= 10000000)) (PreH12 : (0 < t)) (PreH13 : (t <= phi_pre)) (PreH14 : (0 < ord)) (PreH15 : (ord <= phi_pre)) (PreH16 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_safety_wit_13 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (q <> 0) ”
.

Definition order_safety_wit_14 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((q * q ) > t)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000001)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_safety_wit_15 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (1 < t)) (PreH7 : (t <= phi_pre)) (PreH8 : (0 < ord)) (PreH9 : (ord <= phi_pre)) (PreH10 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (t <> 0) ”
.

Definition order_safety_wit_16 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (1 < t)) (PreH7 : (t <= phi_pre)) (PreH8 : (0 < ord)) (PreH9 : (ord <= phi_pre)) (PreH10 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition order_safety_wit_17 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : ((ord % ( t ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : (0 < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (t <> 0) ”
.

Definition order_safety_wit_18 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH2 : (0 <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : ((ord % ( t ) ) = 0)) (PreH5 : (x0 = x_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (phi0 = phi_pre)) (PreH8 : (1 < modulus_pre)) (PreH9 : (modulus_pre <= 100000000000000)) (PreH10 : (1 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition order_safety_wit_19 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (t <> 0) ”
.

Definition order_entail_wit_1 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 10000001) ”
  &&  “ (0 < phi_pre) ”
  &&  “ (phi_pre <= phi_pre) ”
  &&  “ (0 < phi_pre) ”
  &&  “ (phi_pre <= phi_pre) ”
  &&  “ (OrderTrialStateEx x_pre modulus_pre phi_pre 2 phi_pre phi_pre ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  TT && emp 
|--
  “ (OrderTrialStateEx x0 modulus0 phi0 2 phi0 phi0 ) ”
  &&  “ (0 < phi0) ”
  &&  “ (0 < phi0) ”
  &&  “ (1 < modulus0) ”
  &&  emp
).

Definition order_entail_wit_1_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  (OrderTrialStateEx x0 modulus0 phi0 2 phi0 phi0 )
.

Definition order_entail_wit_1_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  (0 < phi0)
.

Definition order_entail_wit_1_split_goal_3 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  (0 < phi0)
.

Definition order_entail_wit_1_split_goal_4 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre <> 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  (1 < modulus0)
.

Definition order_entail_wit_2 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= q) ”
  &&  “ (q <= 10000000) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderFactorStateEx x0 modulus0 phi0 q t ord ) ”
  &&  “ (q <= 10000000) ”
  &&  emp
).

Definition order_entail_wit_2_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderFactorStateEx x0 modulus0 phi0 q t ord )
.

Definition order_entail_wit_2_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  (q <= 10000000)
.

Definition order_entail_wit_3 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= q) ”
  &&  “ (q <= 10000000) ”
  &&  “ (0 < (t ÷ q )) ”
  &&  “ ((t ÷ q ) <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderFactorStateEx x_pre modulus_pre phi_pre q (t ÷ q ) ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderFactorStateEx x0 modulus0 phi0 q (t ÷ q ) ord ) ”
  &&  “ ((t ÷ q ) <= phi0) ”
  &&  “ (0 < (t ÷ q )) ”
  &&  emp
).

Definition order_entail_wit_3_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderFactorStateEx x0 modulus0 phi0 q (t ÷ q ) ord )
.

Definition order_entail_wit_3_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  ((t ÷ q ) <= phi0)
.

Definition order_entail_wit_3_split_goal_3 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  (0 < (t ÷ q ))
.

Definition order_entail_wit_4 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= q) ”
  &&  “ (q <= 10000000) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderStripStateEx x0 modulus0 phi0 q t ord ) ”
  &&  emp
).

Definition order_entail_wit_4_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderStripStateEx x0 modulus0 phi0 q t ord )
.

Definition order_entail_wit_5 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= q) ”
  &&  “ (q <= 10000000) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < (ord ÷ q )) ”
  &&  “ ((ord ÷ q ) <= phi_pre) ”
  &&  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t (ord ÷ q ) ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderStripStateEx x0 modulus0 phi0 q t (ord ÷ q ) ) ”
  &&  “ ((ord ÷ q ) <= phi0) ”
  &&  “ (0 < (ord ÷ q )) ”
  &&  emp
).

Definition order_entail_wit_5_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderStripStateEx x0 modulus0 phi0 q t (ord ÷ q ) )
.

Definition order_entail_wit_5_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((ord ÷ q ) <= phi0)
.

Definition order_entail_wit_5_split_goal_3 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  (0 < (ord ÷ q ))
.

Definition order_entail_wit_6_1 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((ord % ( q ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= 10000001) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1 ) t ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((ord % ( q ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderTrialStateEx x0 modulus0 phi0 (q + 1 ) t ord ) ”
  &&  emp
).

Definition order_entail_wit_6_1_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((ord % ( q ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderTrialStateEx x0 modulus0 phi0 (q + 1 ) t ord )
.

Definition order_entail_wit_6_2 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= 10000001) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1 ) t ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderTrialStateEx x0 modulus0 phi0 (q + 1 ) t ord ) ”
  &&  emp
).

Definition order_entail_wit_6_2_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = ((x_pre^(ord ÷ q )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( q ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : (0 < t)) (PreH14 : (t <= phi_pre)) (PreH15 : (0 < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderTrialStateEx x0 modulus0 phi0 (q + 1 ) t ord )
.

Definition order_entail_wit_6_3 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= (q + 1 )) ”
  &&  “ ((q + 1 ) <= 10000001) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1 ) t ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderTrialStateEx x0 modulus0 phi0 (q + 1 ) t ord ) ”
  &&  “ ((q + 1 ) <= 10000001) ”
  &&  emp
).

Definition order_entail_wit_6_3_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderTrialStateEx x0 modulus0 phi0 (q + 1 ) t ord )
.

Definition order_entail_wit_6_3_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((t % ( q ) ) <> 0)) (PreH2 : ((q * q ) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  ((q + 1 ) <= 10000001)
.

Definition order_entail_wit_7 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (t > 1)) (PreH2 : ((q * q ) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (1 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (t > 1)) (PreH2 : ((q * q ) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderFinalStateEx x0 modulus0 phi0 t ord ) ”
  &&  emp
).

Definition order_entail_wit_7_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (t > 1)) (PreH2 : ((q * q ) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderFinalStateEx x0 modulus0 phi0 t ord )
.

Definition order_entail_wit_8 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (1 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < (ord ÷ t )) ”
  &&  “ ((ord ÷ t ) <= phi_pre) ”
  &&  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t (ord ÷ t ) ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (OrderFinalStateEx x0 modulus0 phi0 t (ord ÷ t ) ) ”
  &&  “ ((ord ÷ t ) <= phi0) ”
  &&  “ (0 < (ord ÷ t )) ”
  &&  emp
).

Definition order_entail_wit_8_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  (OrderFinalStateEx x0 modulus0 phi0 t (ord ÷ t ) )
.

Definition order_entail_wit_8_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((ord ÷ t ) <= phi0)
.

Definition order_entail_wit_8_split_goal_3 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  (0 < (ord ÷ t ))
.

Definition order_return_wit_1 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : ((ord % ( t ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : (0 < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : ((ord % ( t ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : (0 < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord ) ”
  &&  emp
).

Definition order_return_wit_1_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : ((ord % ( t ) ) <> 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : (0 < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  (OrderResult x0 modulus0 ord )
.

Definition order_return_wit_2 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord ) ”
  &&  emp
).

Definition order_return_wit_2_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (retval: Z) (PreH1 : (retval <> 1)) (PreH2 : (retval = ((x_pre^(ord ÷ t )) % ( modulus_pre ) ))) (PreH3 : (0 <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((ord % ( t ) ) = 0)) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : (0 < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  (OrderResult x0 modulus0 ord )
.

Definition order_return_wit_3 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (t <= 1)) (PreH2 : ((q * q ) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (t <= 1)) (PreH2 : ((q * q ) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord ) ”
  &&  emp
).

Definition order_return_wit_3_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (t <= 1)) (PreH2 : ((q * q ) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : (0 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : (0 < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord )),
  (OrderResult x0 modulus0 ord )
.

Definition order_return_wit_4 :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 1 ) ”
  &&  emp
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  TT && emp 
|--
  “ (OrderResult x0 modulus0 1 ) ”
  &&  emp
).

Definition order_return_wit_4_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0 )),
  (OrderResult x0 modulus0 1 )
.

Definition order_partial_solve_wit_1_pure :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((ord % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (x_pre = x_pre) ”
  &&  “ ((ord ÷ q ) = (ord ÷ q )) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre <= UINT64_MAX) ”
  &&  “ ((ord ÷ q ) <= 100000000000000) ”
  &&  “ (0 <= (ord ÷ q )) ”
  &&  “ (x0 <= UINT64_MAX) ”
  &&  “ (0 <= x0) ”
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (ord <= UINT64_MAX)) (PreH2 : (t <= UINT64_MAX)) (PreH3 : (q <= UINT64_MAX)) (PreH4 : (phi_pre <= UINT64_MAX)) (PreH5 : (modulus_pre <= UINT64_MAX)) (PreH6 : (x_pre <= UINT64_MAX)) (PreH7 : (ord >= 0)) (PreH8 : (t >= 0)) (PreH9 : (q >= 0)) (PreH10 : (phi_pre >= 0)) (PreH11 : (modulus_pre >= 0)) (PreH12 : (x_pre >= 0)) (PreH13 : ((ord % ( q ) ) = 0)) (PreH14 : (x0 = x_pre)) (PreH15 : (modulus0 = modulus_pre)) (PreH16 : (phi0 = phi_pre)) (PreH17 : (1 < modulus_pre)) (PreH18 : (modulus_pre <= 100000000000000)) (PreH19 : (2 <= q)) (PreH20 : (q <= 10000000)) (PreH21 : (0 < t)) (PreH22 : (t <= phi_pre)) (PreH23 : (0 < ord)) (PreH24 : (ord <= phi_pre)) (PreH25 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= (ord ÷ q )) ”
  &&  “ ((ord ÷ q ) <= 100000000000000) ”
).

Definition order_partial_solve_wit_1_pure_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (ord <= UINT64_MAX)) (PreH2 : (t <= UINT64_MAX)) (PreH3 : (q <= UINT64_MAX)) (PreH4 : (phi_pre <= UINT64_MAX)) (PreH5 : (modulus_pre <= UINT64_MAX)) (PreH6 : (x_pre <= UINT64_MAX)) (PreH7 : (ord >= 0)) (PreH8 : (t >= 0)) (PreH9 : (q >= 0)) (PreH10 : (phi_pre >= 0)) (PreH11 : (modulus_pre >= 0)) (PreH12 : (x_pre >= 0)) (PreH13 : ((ord % ( q ) ) = 0)) (PreH14 : (x0 = x_pre)) (PreH15 : (modulus0 = modulus_pre)) (PreH16 : (phi0 = phi_pre)) (PreH17 : (1 < modulus_pre)) (PreH18 : (modulus_pre <= 100000000000000)) (PreH19 : (2 <= q)) (PreH20 : (q <= 10000000)) (PreH21 : (0 < t)) (PreH22 : (t <= phi_pre)) (PreH23 : (0 < ord)) (PreH24 : (ord <= phi_pre)) (PreH25 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= (ord ÷ q )) ”
.

Definition order_partial_solve_wit_1_pure_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : (ord <= UINT64_MAX)) (PreH2 : (t <= UINT64_MAX)) (PreH3 : (q <= UINT64_MAX)) (PreH4 : (phi_pre <= UINT64_MAX)) (PreH5 : (modulus_pre <= UINT64_MAX)) (PreH6 : (x_pre <= UINT64_MAX)) (PreH7 : (ord >= 0)) (PreH8 : (t >= 0)) (PreH9 : (q >= 0)) (PreH10 : (phi_pre >= 0)) (PreH11 : (modulus_pre >= 0)) (PreH12 : (x_pre >= 0)) (PreH13 : ((ord % ( q ) ) = 0)) (PreH14 : (x0 = x_pre)) (PreH15 : (modulus0 = modulus_pre)) (PreH16 : (phi0 = phi_pre)) (PreH17 : (1 < modulus_pre)) (PreH18 : (modulus_pre <= 100000000000000)) (PreH19 : (2 <= q)) (PreH20 : (q <= 10000000)) (PreH21 : (0 < t)) (PreH22 : (t <= phi_pre)) (PreH23 : (0 < ord)) (PreH24 : (ord <= phi_pre)) (PreH25 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "q" ) )) # UInt64  |-> q)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ ((ord ÷ q ) <= 100000000000000) ”
.

Definition order_partial_solve_wit_1_aux :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (q: Z) (PreH1 : ((ord % ( q ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : (0 < t)) (PreH10 : (t <= phi_pre)) (PreH11 : (0 < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord )),
  TT && emp 
|--
  “ (x_pre = x_pre) ”
  &&  “ ((ord ÷ q ) = (ord ÷ q )) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre <= UINT64_MAX) ”
  &&  “ ((ord ÷ q ) <= 100000000000000) ”
  &&  “ (0 <= (ord ÷ q )) ”
  &&  “ (x0 <= UINT64_MAX) ”
  &&  “ (0 <= x0) ”
  &&  “ ((ord % ( q ) ) = 0) ”
  &&  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (2 <= q) ”
  &&  “ (q <= 10000000) ”
  &&  “ (0 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t ord ) ”
  &&  emp
.

Definition order_partial_solve_wit_1 := order_partial_solve_wit_1_pure -> order_partial_solve_wit_1_aux.

Definition order_partial_solve_wit_2_pure :=
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : ((ord % ( t ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : (0 < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (x_pre = x_pre) ”
  &&  “ ((ord ÷ t ) = (ord ÷ t )) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre <= UINT64_MAX) ”
  &&  “ ((ord ÷ t ) <= 100000000000000) ”
  &&  “ (0 <= (ord ÷ t )) ”
  &&  “ (x0 <= UINT64_MAX) ”
  &&  “ (0 <= x0) ”
) \/
(
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : (ord <= UINT64_MAX)) (PreH2 : (t <= UINT64_MAX)) (PreH3 : (phi_pre <= UINT64_MAX)) (PreH4 : (modulus_pre <= UINT64_MAX)) (PreH5 : (x_pre <= UINT64_MAX)) (PreH6 : (ord >= 0)) (PreH7 : (t >= 0)) (PreH8 : (phi_pre >= 0)) (PreH9 : (modulus_pre >= 0)) (PreH10 : (x_pre >= 0)) (PreH11 : ((ord % ( t ) ) = 0)) (PreH12 : (x0 = x_pre)) (PreH13 : (modulus0 = modulus_pre)) (PreH14 : (phi0 = phi_pre)) (PreH15 : (1 < modulus_pre)) (PreH16 : (modulus_pre <= 100000000000000)) (PreH17 : (1 < t)) (PreH18 : (t <= phi_pre)) (PreH19 : (0 < ord)) (PreH20 : (ord <= phi_pre)) (PreH21 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= (ord ÷ t )) ”
  &&  “ ((ord ÷ t ) <= 100000000000000) ”
).

Definition order_partial_solve_wit_2_pure_split_goal_1 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : (ord <= UINT64_MAX)) (PreH2 : (t <= UINT64_MAX)) (PreH3 : (phi_pre <= UINT64_MAX)) (PreH4 : (modulus_pre <= UINT64_MAX)) (PreH5 : (x_pre <= UINT64_MAX)) (PreH6 : (ord >= 0)) (PreH7 : (t >= 0)) (PreH8 : (phi_pre >= 0)) (PreH9 : (modulus_pre >= 0)) (PreH10 : (x_pre >= 0)) (PreH11 : ((ord % ( t ) ) = 0)) (PreH12 : (x0 = x_pre)) (PreH13 : (modulus0 = modulus_pre)) (PreH14 : (phi0 = phi_pre)) (PreH15 : (1 < modulus_pre)) (PreH16 : (modulus_pre <= 100000000000000)) (PreH17 : (1 < t)) (PreH18 : (t <= phi_pre)) (PreH19 : (0 < ord)) (PreH20 : (ord <= phi_pre)) (PreH21 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ (0 <= (ord ÷ t )) ”
.

Definition order_partial_solve_wit_2_pure_split_goal_2 :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : (ord <= UINT64_MAX)) (PreH2 : (t <= UINT64_MAX)) (PreH3 : (phi_pre <= UINT64_MAX)) (PreH4 : (modulus_pre <= UINT64_MAX)) (PreH5 : (x_pre <= UINT64_MAX)) (PreH6 : (ord >= 0)) (PreH7 : (t >= 0)) (PreH8 : (phi_pre >= 0)) (PreH9 : (modulus_pre >= 0)) (PreH10 : (x_pre >= 0)) (PreH11 : ((ord % ( t ) ) = 0)) (PreH12 : (x0 = x_pre)) (PreH13 : (modulus0 = modulus_pre)) (PreH14 : (phi0 = phi_pre)) (PreH15 : (1 < modulus_pre)) (PreH16 : (modulus_pre <= 100000000000000)) (PreH17 : (1 < t)) (PreH18 : (t <= phi_pre)) (PreH19 : (0 < ord)) (PreH20 : (ord <= phi_pre)) (PreH21 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "modulus" ) )) # UInt64  |-> modulus_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "t" ) )) # UInt64  |-> t)
  **  ((( &( "ord" ) )) # UInt64  |-> ord)
|--
  “ ((ord ÷ t ) <= 100000000000000) ”
.

Definition order_partial_solve_wit_2_aux :=
forall (phi0: Z) (modulus0: Z) (x0: Z) (x_pre: Z) (modulus_pre: Z) (phi_pre: Z) (ord: Z) (t: Z) (PreH1 : ((ord % ( t ) ) = 0)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : (0 < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord )),
  TT && emp 
|--
  “ (x_pre = x_pre) ”
  &&  “ ((ord ÷ t ) = (ord ÷ t )) ”
  &&  “ (modulus_pre = modulus_pre) ”
  &&  “ (1 <= modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (0 <= x_pre) ”
  &&  “ (x_pre <= UINT64_MAX) ”
  &&  “ ((ord ÷ t ) <= 100000000000000) ”
  &&  “ (0 <= (ord ÷ t )) ”
  &&  “ (x0 <= UINT64_MAX) ”
  &&  “ (0 <= x0) ”
  &&  “ ((ord % ( t ) ) = 0) ”
  &&  “ (x0 = x_pre) ”
  &&  “ (modulus0 = modulus_pre) ”
  &&  “ (phi0 = phi_pre) ”
  &&  “ (1 < modulus_pre) ”
  &&  “ (modulus_pre <= 100000000000000) ”
  &&  “ (1 < t) ”
  &&  “ (t <= phi_pre) ”
  &&  “ (0 < ord) ”
  &&  “ (ord <= phi_pre) ”
  &&  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t ord ) ”
  &&  emp
.

Definition order_partial_solve_wit_2 := order_partial_solve_wit_2_pure -> order_partial_solve_wit_2_aux.

(*----- Function walk -----*)

Definition walk_safety_wit_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (i_pre = factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value )) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH8 : (0 < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values )) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ (ord_pre <> 0) ”
.

Definition walk_safety_wit_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition walk_safety_wit_4 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_5 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  ((( &( "ph" ) )) # UInt64  |->_)
  **  ((( &( "pk" ) )) # UInt64  |-> 1)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  ((( &( "p" ) )) # UInt64  |-> (Znth (i_pre - 0 ) pr_values 0))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_6 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  ((( &( "pk" ) )) # UInt64  |->_)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  ((( &( "p" ) )) # UInt64  |-> (Znth (i_pre - 0 ) pr_values 0))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_7 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  ((( &( "e" ) )) # UInt64  |->_)
  **  ((( &( "ph" ) )) # UInt64  |-> 1)
  **  ((( &( "pk" ) )) # UInt64  |-> 1)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  ((( &( "p" ) )) # UInt64  |-> (Znth (i_pre - 0 ) pr_values 0))
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_8 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH8 : (p = (Znth i_pre pr_values 0))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> (unsigned_last_nbits ((pk * p )) (64)))
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_9 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> (unsigned_last_nbits ((pk * p )) (64)))
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_safety_wit_10 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH9 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "o" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (pk <> 0) ”
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH9 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "o" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (pk <> 0) ”
).

Definition walk_safety_wit_10_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH9 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "o" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (pk <> 0) ”
.

Definition walk_safety_wit_11 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (g <> 0) ”
.

Definition walk_safety_wit_12 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ ((i_pre + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i_pre + 1 )) ”
.

Definition walk_safety_wit_13 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition walk_entail_wit_1 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (i_pre <> factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value )) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH8 : (0 < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values )) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (i_pre <> factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value )) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH8 : (0 < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values )) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  TT && emp 
|--
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre ) ”
  &&  emp
).

Definition walk_entail_wit_1_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (i_pre <> factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value )) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH8 : (0 < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values )) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )
.

Definition walk_entail_wit_1_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (i_pre <> factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value )) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH8 : (0 < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values )) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )
.

Definition walk_entail_wit_2 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  TT && emp 
|--
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 ) ”
  &&  emp
).

Definition walk_entail_wit_2_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )
.

Definition walk_entail_wit_3 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
|--
  EX (current: Z),
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= ((Znth i_pre pe_values 0) + 1 )) ”
  &&  “ ((Znth (i_pre - 0 ) pr_values 0) = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m (Znth (i_pre - 0 ) pr_values 0) 1 (Znth i_pre pe_values 0) 1 1 ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current 1 ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  TT && emp 
|--
  “ (WalkExponentState m (Znth (i_pre - 0 ) pr_values 0) 1 (Znth i_pre pe_values 0) 1 1 ) ”
  &&  “ ((Znth (i_pre - 0 ) pr_values 0) = (Znth i_pre pr_values 0)) ”
  &&  “ (1 <= ((Znth i_pre pe_values 0) + 1 )) ”
  &&  emp
).

Definition walk_entail_wit_3_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  (WalkExponentState m (Znth (i_pre - 0 ) pr_values 0) 1 (Znth i_pre pe_values 0) 1 1 )
.

Definition walk_entail_wit_3_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  ((Znth (i_pre - 0 ) pr_values 0) = (Znth i_pre pr_values 0))
.

Definition walk_entail_wit_3_split_goal_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  (1 <= ((Znth i_pre pe_values 0) + 1 ))
.

Definition walk_entail_wit_4_1 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current_2)
|--
  EX (current: Z),
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((p - 1 )) (64)) ) ”
  &&  “ (OrderInput (x_value % ( (unsigned_last_nbits ((pk * p )) (64)) ) ) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((p - 1 )) (64)) ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  TT && emp 
|--
  “ (OrderInput (x_value % ( (unsigned_last_nbits ((pk * p )) (64)) ) ) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((p - 1 )) (64)) ) ”
  &&  “ (WalkExponentState m p (1 + 1 ) (Znth i_pre pe_values 0) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((p - 1 )) (64)) ) ”
  &&  “ (1 <= (Znth i_pre pe_values 0)) ”
  &&  emp
).

Definition walk_entail_wit_4_1_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (OrderInput (x_value % ( (unsigned_last_nbits ((pk * p )) (64)) ) ) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((p - 1 )) (64)) )
.

Definition walk_entail_wit_4_1_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (WalkExponentState m p (1 + 1 ) (Znth i_pre pe_values 0) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((p - 1 )) (64)) )
.

Definition walk_entail_wit_4_1_split_goal_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (1 <= (Znth i_pre pe_values 0))
.

Definition walk_entail_wit_4_2 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e <> 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current_2)
|--
  EX (current: Z),
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((ph * p )) (64)) ) ”
  &&  “ (OrderInput (x_value % ( (unsigned_last_nbits ((pk * p )) (64)) ) ) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((ph * p )) (64)) ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e <> 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  TT && emp 
|--
  “ (OrderInput (x_value % ( (unsigned_last_nbits ((pk * p )) (64)) ) ) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((ph * p )) (64)) ) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((ph * p )) (64)) ) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  emp
).

Definition walk_entail_wit_4_2_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e <> 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (OrderInput (x_value % ( (unsigned_last_nbits ((pk * p )) (64)) ) ) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((ph * p )) (64)) )
.

Definition walk_entail_wit_4_2_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e <> 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) (unsigned_last_nbits ((pk * p )) (64)) (unsigned_last_nbits ((ph * p )) (64)) )
.

Definition walk_entail_wit_4_2_split_goal_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e <> 1)) (PreH2 : (e <= (Znth (i_pre - 0 ) pe_values 0))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH9 : (p = (Znth i_pre pr_values 0))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (e <= (Znth i_pre pe_values 0))
.

Definition walk_entail_wit_5 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current_2)
|--
  EX (current: Z),
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (0 < retval_2) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) ) ”
  &&  “ (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph retval retval_2 (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) ) ”
  &&  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  TT && emp 
|--
  “ (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) ) ”
  &&  “ (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph retval retval_2 (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) ) ”
  &&  “ (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) ) ”
  &&  “ (0 < retval_2) ”
  &&  emp
).

Definition walk_entail_wit_5_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )
.

Definition walk_entail_wit_5_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) )
.

Definition walk_entail_wit_5_split_goal_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph retval retval_2 (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) )
.

Definition walk_entail_wit_5_split_goal_4 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ retval_2 ) * retval ) )
.

Definition walk_entail_wit_5_split_goal_5 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval ))) (PreH4 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : (0 <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values 0))) (PreH11 : (p = (Znth i_pre pr_values 0))) (PreH12 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH13 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH14 : (WalkGlobalBounds m x_value )) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH16 : (0 < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values )) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (0 < retval_2)
.

Definition walk_entail_wit_6 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (current_2 + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ))
|--
  EX (current: Z),
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= (unsigned_last_nbits ((e + 1 )) (64))) ”
  &&  “ ((unsigned_last_nbits ((e + 1 )) (64)) <= ((Znth i_pre pe_values 0) + 1 )) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m p (unsigned_last_nbits ((e + 1 )) (64)) (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current (unsigned_last_nbits ((e + 1 )) (64)) ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  TT && emp 
|--
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (current_2 + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ) (unsigned_last_nbits ((e + 1 )) (64)) ) ”
  &&  “ (WalkExponentState m p (unsigned_last_nbits ((e + 1 )) (64)) (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ ((unsigned_last_nbits ((e + 1 )) (64)) <= ((Znth i_pre pe_values 0) + 1 )) ”
  &&  “ (1 <= (unsigned_last_nbits ((e + 1 )) (64))) ”
  &&  emp
).

Definition walk_entail_wit_6_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (current_2 + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ) (unsigned_last_nbits ((e + 1 )) (64)) )
.

Definition walk_entail_wit_6_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (WalkExponentState m p (unsigned_last_nbits ((e + 1 )) (64)) (Znth i_pre pe_values 0) pk ph )
.

Definition walk_entail_wit_6_split_goal_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  ((unsigned_last_nbits ((e + 1 )) (64)) <= ((Znth i_pre pe_values 0) + 1 ))
.

Definition walk_entail_wit_6_split_goal_4 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current_2: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e )),
  (1 <= (unsigned_last_nbits ((e + 1 )) (64)))
.

Definition walk_return_wit_1 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (unsigned_last_nbits ((before + (phi_pre ÷ ord_pre ) )) (64)))
|--
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ))
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  TT && emp 
|--
  “ ((unsigned_last_nbits ((before + (phi_pre ÷ ord_pre ) )) (64)) = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (factor_count) (d_pre)) )) ”
  &&  emp
).

Definition walk_return_wit_1_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  ((unsigned_last_nbits ((before + (phi_pre ÷ ord_pre ) )) (64)) = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (factor_count) (d_pre)) ))
.

Definition walk_return_wit_2 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre <= 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ))
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre <= 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  TT && emp 
|--
  “ (before = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (factor_count) (d_pre)) )) ”
  &&  emp
).

Definition walk_return_wit_2_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : (d_pre <= 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : (0 <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value )) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH9 : (0 < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )),
  (before = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (factor_count) (d_pre)) ))
.

Definition walk_return_wit_3 :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e > (Znth (i_pre - 0 ) pe_values 0))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH8 : (p = (Znth i_pre pr_values 0))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ))
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e > (Znth (i_pre - 0 ) pe_values 0))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH8 : (p = (Znth i_pre pr_values 0))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  TT && emp 
|--
  “ (current = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) ”
  &&  emp
).

Definition walk_return_wit_3_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : (e > (Znth (i_pre - 0 ) pe_values 0))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH8 : (p = (Znth i_pre pr_values 0))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (current = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ))
.

Definition walk_partial_solve_wit_1_pure :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= (i_pre + 1 )) ”
  &&  “ ((i_pre + 1 ) <= factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) ”
.

Definition walk_partial_solve_wit_1_aux :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre )) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= (i_pre + 1 )) ”
  &&  “ ((i_pre + 1 ) <= factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) d_pre phi_pre ord_pre ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> before)
.

Definition walk_partial_solve_wit_1 := walk_partial_solve_wit_1_pure -> walk_partial_solve_wit_1_aux.

Definition walk_partial_solve_wit_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value )) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH7 : (0 < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values )) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) )) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)) ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ) 1 ) ”
  &&  (((( &( "pr" ) ) + (i_pre * sizeof(UINT64)))) # UInt64  |-> (Znth (i_pre - 0 ) pr_values 0))
  **  (UInt64Array.missing_i ( &( "pr" ) ) i_pre 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) (d_pre)) ))
.

Definition walk_partial_solve_wit_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (pk: Z) (ph: Z) (p: Z) (e: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= ((Znth i_pre pe_values 0) + 1 ))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph )) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= ((Znth i_pre pe_values 0) + 1 )) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m p e (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (((( &( "pe" ) ) + (i_pre * sizeof(UINT64)))) # UInt64  |-> (Znth (i_pre - 0 ) pe_values 0))
  **  (UInt64Array.missing_i ( &( "pe" ) ) i_pre 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
.

Definition walk_partial_solve_wit_4_pure :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH9 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "o" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ ((x_value % ( pk ) ) = (x_value % ( pk ) )) ”
  &&  “ (pk = pk) ”
  &&  “ (ph = ph) ”
  &&  “ (OrderInput (x_value % ( pk ) ) pk ph ) ”
  &&  “ (pk <= 100000000000000) ”
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (pk <= UINT64_MAX)) (PreH4 : (ph <= UINT64_MAX)) (PreH5 : (p <= UINT64_MAX)) (PreH6 : (e <= UINT64_MAX)) (PreH7 : (ord_pre <= UINT64_MAX)) (PreH8 : (phi_pre <= UINT64_MAX)) (PreH9 : (d_pre <= UINT64_MAX)) (PreH10 : (current >= 0)) (PreH11 : (x_value >= 0)) (PreH12 : (pk >= 0)) (PreH13 : (ph >= 0)) (PreH14 : (p >= 0)) (PreH15 : (e >= 0)) (PreH16 : (ord_pre >= 0)) (PreH17 : (phi_pre >= 0)) (PreH18 : (d_pre >= 0)) (PreH19 : (factor_count <= INT_MAX)) (PreH20 : (i_pre <= INT_MAX)) (PreH21 : (factor_count >= INT_MIN)) (PreH22 : (i_pre >= INT_MIN)) (PreH23 : ((Zlength (pr_values)) = factor_count)) (PreH24 : ((Zlength (pe_values)) = factor_count)) (PreH25 : (0 <= i_pre)) (PreH26 : (i_pre < factor_count)) (PreH27 : (1 <= e)) (PreH28 : (e <= (Znth i_pre pe_values 0))) (PreH29 : (p = (Znth i_pre pr_values 0))) (PreH30 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH31 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH32 : (WalkGlobalBounds m x_value )) (PreH33 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH34 : (0 < ord_pre)) (PreH35 : (ValidFactorTable m pr_values pe_values )) (PreH36 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH37 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "o" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (pk <= 100000000000000) ”
).

Definition walk_partial_solve_wit_4_pure_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (pk <= UINT64_MAX)) (PreH4 : (ph <= UINT64_MAX)) (PreH5 : (p <= UINT64_MAX)) (PreH6 : (e <= UINT64_MAX)) (PreH7 : (ord_pre <= UINT64_MAX)) (PreH8 : (phi_pre <= UINT64_MAX)) (PreH9 : (d_pre <= UINT64_MAX)) (PreH10 : (current >= 0)) (PreH11 : (x_value >= 0)) (PreH12 : (pk >= 0)) (PreH13 : (ph >= 0)) (PreH14 : (p >= 0)) (PreH15 : (e >= 0)) (PreH16 : (ord_pre >= 0)) (PreH17 : (phi_pre >= 0)) (PreH18 : (d_pre >= 0)) (PreH19 : (factor_count <= INT_MAX)) (PreH20 : (i_pre <= INT_MAX)) (PreH21 : (factor_count >= INT_MIN)) (PreH22 : (i_pre >= INT_MIN)) (PreH23 : ((Zlength (pr_values)) = factor_count)) (PreH24 : ((Zlength (pe_values)) = factor_count)) (PreH25 : (0 <= i_pre)) (PreH26 : (i_pre < factor_count)) (PreH27 : (1 <= e)) (PreH28 : (e <= (Znth i_pre pe_values 0))) (PreH29 : (p = (Znth i_pre pr_values 0))) (PreH30 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH31 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH32 : (WalkGlobalBounds m x_value )) (PreH33 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH34 : (0 < ord_pre)) (PreH35 : (ValidFactorTable m pr_values pe_values )) (PreH36 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH37 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "o" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (pk <= 100000000000000) ”
.

Definition walk_partial_solve_wit_4_aux :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH9 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH10 : (WalkGlobalBounds m x_value )) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH12 : (0 < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values )) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ ((x_value % ( pk ) ) = (x_value % ( pk ) )) ”
  &&  “ (pk = pk) ”
  &&  “ (ph = ph) ”
  &&  “ (OrderInput (x_value % ( pk ) ) pk ph ) ”
  &&  “ (pk <= 100000000000000) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ (OrderInput (x_value % ( pk ) ) pk ph ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
.

Definition walk_partial_solve_wit_4 := walk_partial_solve_wit_4_pure -> walk_partial_solve_wit_4_aux.

Definition walk_partial_solve_wit_5_pure :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (PreH1 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= (Znth i_pre pe_values 0))) (PreH8 : (p = (Znth i_pre pr_values 0))) (PreH9 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH10 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "g" ) )) # UInt64  |->_)
  **  ((( &( "o" ) )) # UInt64  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (ord_pre = ord_pre) ”
  &&  “ (retval = retval) ”
  &&  “ (0 <= ord_pre) ”
  &&  “ (retval <= 100000000000000) ”
  &&  “ (0 <= retval) ”
  &&  “ (ord_pre <= 100000000000000) ”
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (pk <= UINT64_MAX)) (PreH4 : (ph <= UINT64_MAX)) (PreH5 : (p <= UINT64_MAX)) (PreH6 : (e <= UINT64_MAX)) (PreH7 : (ord_pre <= UINT64_MAX)) (PreH8 : (phi_pre <= UINT64_MAX)) (PreH9 : (d_pre <= UINT64_MAX)) (PreH10 : (retval <= UINT64_MAX)) (PreH11 : (current >= 0)) (PreH12 : (x_value >= 0)) (PreH13 : (pk >= 0)) (PreH14 : (ph >= 0)) (PreH15 : (p >= 0)) (PreH16 : (e >= 0)) (PreH17 : (ord_pre >= 0)) (PreH18 : (phi_pre >= 0)) (PreH19 : (d_pre >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (factor_count <= INT_MAX)) (PreH22 : (i_pre <= INT_MAX)) (PreH23 : (factor_count >= INT_MIN)) (PreH24 : (i_pre >= INT_MIN)) (PreH25 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH26 : ((Zlength (pr_values)) = factor_count)) (PreH27 : ((Zlength (pe_values)) = factor_count)) (PreH28 : (0 <= i_pre)) (PreH29 : (i_pre < factor_count)) (PreH30 : (1 <= e)) (PreH31 : (e <= (Znth i_pre pe_values 0))) (PreH32 : (p = (Znth i_pre pr_values 0))) (PreH33 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH34 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "g" ) )) # UInt64  |->_)
  **  ((( &( "o" ) )) # UInt64  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (ord_pre <= 100000000000000) ”
  &&  “ (retval <= 100000000000000) ”
).

Definition walk_partial_solve_wit_5_pure_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (pk <= UINT64_MAX)) (PreH4 : (ph <= UINT64_MAX)) (PreH5 : (p <= UINT64_MAX)) (PreH6 : (e <= UINT64_MAX)) (PreH7 : (ord_pre <= UINT64_MAX)) (PreH8 : (phi_pre <= UINT64_MAX)) (PreH9 : (d_pre <= UINT64_MAX)) (PreH10 : (retval <= UINT64_MAX)) (PreH11 : (current >= 0)) (PreH12 : (x_value >= 0)) (PreH13 : (pk >= 0)) (PreH14 : (ph >= 0)) (PreH15 : (p >= 0)) (PreH16 : (e >= 0)) (PreH17 : (ord_pre >= 0)) (PreH18 : (phi_pre >= 0)) (PreH19 : (d_pre >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (factor_count <= INT_MAX)) (PreH22 : (i_pre <= INT_MAX)) (PreH23 : (factor_count >= INT_MIN)) (PreH24 : (i_pre >= INT_MIN)) (PreH25 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH26 : ((Zlength (pr_values)) = factor_count)) (PreH27 : ((Zlength (pe_values)) = factor_count)) (PreH28 : (0 <= i_pre)) (PreH29 : (i_pre < factor_count)) (PreH30 : (1 <= e)) (PreH31 : (e <= (Znth i_pre pe_values 0))) (PreH32 : (p = (Znth i_pre pr_values 0))) (PreH33 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH34 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "g" ) )) # UInt64  |->_)
  **  ((( &( "o" ) )) # UInt64  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (ord_pre <= 100000000000000) ”
.

Definition walk_partial_solve_wit_5_pure_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (pk <= UINT64_MAX)) (PreH4 : (ph <= UINT64_MAX)) (PreH5 : (p <= UINT64_MAX)) (PreH6 : (e <= UINT64_MAX)) (PreH7 : (ord_pre <= UINT64_MAX)) (PreH8 : (phi_pre <= UINT64_MAX)) (PreH9 : (d_pre <= UINT64_MAX)) (PreH10 : (retval <= UINT64_MAX)) (PreH11 : (current >= 0)) (PreH12 : (x_value >= 0)) (PreH13 : (pk >= 0)) (PreH14 : (ph >= 0)) (PreH15 : (p >= 0)) (PreH16 : (e >= 0)) (PreH17 : (ord_pre >= 0)) (PreH18 : (phi_pre >= 0)) (PreH19 : (d_pre >= 0)) (PreH20 : (retval >= 0)) (PreH21 : (factor_count <= INT_MAX)) (PreH22 : (i_pre <= INT_MAX)) (PreH23 : (factor_count >= INT_MIN)) (PreH24 : (i_pre >= INT_MIN)) (PreH25 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH26 : ((Zlength (pr_values)) = factor_count)) (PreH27 : ((Zlength (pe_values)) = factor_count)) (PreH28 : (0 <= i_pre)) (PreH29 : (i_pre < factor_count)) (PreH30 : (1 <= e)) (PreH31 : (e <= (Znth i_pre pe_values 0))) (PreH32 : (p = (Znth i_pre pr_values 0))) (PreH33 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH34 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "g" ) )) # UInt64  |->_)
  **  ((( &( "o" ) )) # UInt64  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (retval <= 100000000000000) ”
.

Definition walk_partial_solve_wit_5_aux :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (ph: Z) (pk: Z) (retval: Z) (PreH1 : (OrderResult (x_value % ( pk ) ) pk retval )) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : (0 <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= (Znth i_pre pe_values 0))) (PreH8 : (p = (Znth i_pre pr_values 0))) (PreH9 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH10 : (OrderInput (x_value % ( pk ) ) pk ph )) (PreH11 : (WalkGlobalBounds m x_value )) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH13 : (0 < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values )) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (ord_pre = ord_pre) ”
  &&  “ (retval = retval) ”
  &&  “ (0 <= ord_pre) ”
  &&  “ (retval <= 100000000000000) ”
  &&  “ (0 <= retval) ”
  &&  “ (ord_pre <= 100000000000000) ”
  &&  “ (OrderResult (x_value % ( pk ) ) pk retval ) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ (OrderInput (x_value % ( pk ) ) pk ph ) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
.

Definition walk_partial_solve_wit_5 := walk_partial_solve_wit_5_pure -> walk_partial_solve_wit_5_aux.

Definition walk_partial_solve_wit_6_pure :=
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= (i_pre + 1 )) ”
  &&  “ ((i_pre + 1 ) <= factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
  &&  “ (0 < (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64))) ”
  &&  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
) \/
(
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (o <= UINT64_MAX)) (PreH4 : (pk <= UINT64_MAX)) (PreH5 : (ph <= UINT64_MAX)) (PreH6 : (g <= UINT64_MAX)) (PreH7 : (p <= UINT64_MAX)) (PreH8 : (e <= UINT64_MAX)) (PreH9 : (ord_pre <= UINT64_MAX)) (PreH10 : (phi_pre <= UINT64_MAX)) (PreH11 : (d_pre <= UINT64_MAX)) (PreH12 : (current >= 0)) (PreH13 : (x_value >= 0)) (PreH14 : (o >= 0)) (PreH15 : (pk >= 0)) (PreH16 : (ph >= 0)) (PreH17 : (g >= 0)) (PreH18 : (p >= 0)) (PreH19 : (e >= 0)) (PreH20 : (ord_pre >= 0)) (PreH21 : (phi_pre >= 0)) (PreH22 : (d_pre >= 0)) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : (0 <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values 0))) (PreH33 : (p = (Znth i_pre pr_values 0))) (PreH34 : (0 < g)) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH41 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
  &&  “ (0 < (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64))) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
  &&  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ) ”
).

Definition walk_partial_solve_wit_6_pure_split_goal_1 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (o <= UINT64_MAX)) (PreH4 : (pk <= UINT64_MAX)) (PreH5 : (ph <= UINT64_MAX)) (PreH6 : (g <= UINT64_MAX)) (PreH7 : (p <= UINT64_MAX)) (PreH8 : (e <= UINT64_MAX)) (PreH9 : (ord_pre <= UINT64_MAX)) (PreH10 : (phi_pre <= UINT64_MAX)) (PreH11 : (d_pre <= UINT64_MAX)) (PreH12 : (current >= 0)) (PreH13 : (x_value >= 0)) (PreH14 : (o >= 0)) (PreH15 : (pk >= 0)) (PreH16 : (ph >= 0)) (PreH17 : (g >= 0)) (PreH18 : (p >= 0)) (PreH19 : (e >= 0)) (PreH20 : (ord_pre >= 0)) (PreH21 : (phi_pre >= 0)) (PreH22 : (d_pre >= 0)) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : (0 <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values 0))) (PreH33 : (p = (Znth i_pre pr_values 0))) (PreH34 : (0 < g)) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH41 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
.

Definition walk_partial_solve_wit_6_pure_split_goal_2 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (o <= UINT64_MAX)) (PreH4 : (pk <= UINT64_MAX)) (PreH5 : (ph <= UINT64_MAX)) (PreH6 : (g <= UINT64_MAX)) (PreH7 : (p <= UINT64_MAX)) (PreH8 : (e <= UINT64_MAX)) (PreH9 : (ord_pre <= UINT64_MAX)) (PreH10 : (phi_pre <= UINT64_MAX)) (PreH11 : (d_pre <= UINT64_MAX)) (PreH12 : (current >= 0)) (PreH13 : (x_value >= 0)) (PreH14 : (o >= 0)) (PreH15 : (pk >= 0)) (PreH16 : (ph >= 0)) (PreH17 : (g >= 0)) (PreH18 : (p >= 0)) (PreH19 : (e >= 0)) (PreH20 : (ord_pre >= 0)) (PreH21 : (phi_pre >= 0)) (PreH22 : (d_pre >= 0)) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : (0 <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values 0))) (PreH33 : (p = (Znth i_pre pr_values 0))) (PreH34 : (0 < g)) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH41 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (0 < (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64))) ”
.

Definition walk_partial_solve_wit_6_pure_split_goal_3 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (o <= UINT64_MAX)) (PreH4 : (pk <= UINT64_MAX)) (PreH5 : (ph <= UINT64_MAX)) (PreH6 : (g <= UINT64_MAX)) (PreH7 : (p <= UINT64_MAX)) (PreH8 : (e <= UINT64_MAX)) (PreH9 : (ord_pre <= UINT64_MAX)) (PreH10 : (phi_pre <= UINT64_MAX)) (PreH11 : (d_pre <= UINT64_MAX)) (PreH12 : (current >= 0)) (PreH13 : (x_value >= 0)) (PreH14 : (o >= 0)) (PreH15 : (pk >= 0)) (PreH16 : (ph >= 0)) (PreH17 : (g >= 0)) (PreH18 : (p >= 0)) (PreH19 : (e >= 0)) (PreH20 : (ord_pre >= 0)) (PreH21 : (phi_pre >= 0)) (PreH22 : (d_pre >= 0)) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : (0 <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values 0))) (PreH33 : (p = (Znth i_pre pr_values 0))) (PreH34 : (0 < g)) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH41 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
.

Definition walk_partial_solve_wit_6_pure_split_goal_4 :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : (current <= UINT64_MAX)) (PreH2 : (x_value <= UINT64_MAX)) (PreH3 : (o <= UINT64_MAX)) (PreH4 : (pk <= UINT64_MAX)) (PreH5 : (ph <= UINT64_MAX)) (PreH6 : (g <= UINT64_MAX)) (PreH7 : (p <= UINT64_MAX)) (PreH8 : (e <= UINT64_MAX)) (PreH9 : (ord_pre <= UINT64_MAX)) (PreH10 : (phi_pre <= UINT64_MAX)) (PreH11 : (d_pre <= UINT64_MAX)) (PreH12 : (current >= 0)) (PreH13 : (x_value >= 0)) (PreH14 : (o >= 0)) (PreH15 : (pk >= 0)) (PreH16 : (ph >= 0)) (PreH17 : (g >= 0)) (PreH18 : (p >= 0)) (PreH19 : (e >= 0)) (PreH20 : (ord_pre >= 0)) (PreH21 : (phi_pre >= 0)) (PreH22 : (d_pre >= 0)) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : (0 <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values 0))) (PreH33 : (p = (Znth i_pre pr_values 0))) (PreH34 : (0 < g)) (PreH35 : (WalkGlobalBounds m x_value )) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH37 : (0 < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values )) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH40 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH41 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  ((( &( "i" ) )) # Int  |-> i_pre)
  **  ((( &( "d" ) )) # UInt64  |-> d_pre)
  **  ((( &( "phi" ) )) # UInt64  |-> phi_pre)
  **  ((( &( "ord" ) )) # UInt64  |-> ord_pre)
  **  ((( &( "e" ) )) # UInt64  |-> e)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  ((( &( "g" ) )) # UInt64  |-> g)
  **  ((( &( "ph" ) )) # UInt64  |-> ph)
  **  ((( &( "pk" ) )) # UInt64  |-> pk)
  **  ((( &( "o" ) )) # UInt64  |-> o)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ) ”
.

Definition walk_partial_solve_wit_6_aux :=
forall (pe_values: (@list Z)) (pr_values: (@list Z)) (before: Z) (factor_count: Z) (x_value: Z) (m: Z) (i_pre: Z) (d_pre: Z) (phi_pre: Z) (ord_pre: Z) (current: Z) (e: Z) (p: Z) (g: Z) (ph: Z) (pk: Z) (o: Z) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : (0 <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values 0))) (PreH7 : (p = (Znth i_pre pr_values 0))) (PreH8 : (0 < g)) (PreH9 : (WalkGlobalBounds m x_value )) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre )) (PreH11 : (0 < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values )) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre )) (PreH14 : (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph )) (PreH15 : (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) )) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) )) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= (i_pre + 1 )) ”
  &&  “ ((i_pre + 1 ) <= factor_count) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((unsigned_last_nbits ((d_pre * pk )) (64)))) ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
  &&  “ (0 < (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64))) ”
  &&  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk )) (64)) (unsigned_last_nbits ((phi_pre * ph )) (64)) (unsigned_last_nbits (((ord_pre ÷ g ) * o )) (64)) ) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= i_pre) ”
  &&  “ (i_pre < factor_count) ”
  &&  “ (1 <= e) ”
  &&  “ (e <= (Znth i_pre pe_values 0)) ”
  &&  “ (p = (Znth i_pre pr_values 0)) ”
  &&  “ (0 < g) ”
  &&  “ (WalkGlobalBounds m x_value ) ”
  &&  “ (WalkMachineBounds m d_pre phi_pre ord_pre ) ”
  &&  “ (0 < ord_pre) ”
  &&  “ (ValidFactorTable m pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre ) ”
  &&  “ (WalkExponentState m p (e + 1 ) (Znth i_pre pe_values 0) pk ph ) ”
  &&  “ (WalkMachineBounds m (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) ) ”
  &&  “ (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) ) ”
  &&  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1 ) (d_pre * pk ) (phi_pre * ph ) ((ord_pre ÷ g ) * o ) ) ”
  &&  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1 )) ((d_pre * pk ))) ) ”
  &&  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_value)
  **  ((( &( "total_" ) )) # UInt64  |-> current)
.

Definition walk_partial_solve_wit_6 := walk_partial_solve_wit_6_pure -> walk_partial_solve_wit_6_aux.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  ((( &( "t" ) )) # UInt64  |-> m_pre)
  **  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.undef_full ( &( "pr" ) ) 64 )
  **  (UInt64Array.undef_full ( &( "pe" ) ) 64 )
  **  ((( &( "nf" ) )) # Int  |->_)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  ((( &( "p" ) )) # UInt64  |->_)
  **  ((( &( "t" ) )) # UInt64  |-> m_pre)
  **  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.undef_full ( &( "pr" ) ) 64 )
  **  (UInt64Array.undef_full ( &( "pe" ) ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> 0)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_3 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((p * p ) <= remainder)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000001)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 < remainder)) (PreH14 : (remainder <= m_pre)) (PreH15 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (p <> 0) ”
.

Definition solver_safety_wit_4 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((p * p ) <= remainder)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000001)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 < remainder)) (PreH14 : (remainder <= m_pre)) (PreH15 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (p) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_6 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (2 <= p)) (PreH7 : (p <= 10000000)) (PreH8 : (0 <= factor_count)) (PreH9 : (factor_count < 64)) (PreH10 : ((Zlength (pr_values)) = factor_count)) (PreH11 : ((Zlength (pe_values)) = factor_count)) (PreH12 : (0 <= exponent)) (PreH13 : (exponent <= 47)) (PreH14 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (p <> 0) ”
.

Definition solver_safety_wit_7 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (2 <= p)) (PreH7 : (p <= 10000000)) (PreH8 : (0 <= factor_count)) (PreH9 : (factor_count < 64)) (PreH10 : ((Zlength (pr_values)) = factor_count)) (PreH11 : ((Zlength (pe_values)) = factor_count)) (PreH12 : (0 <= exponent)) (PreH13 : (exponent <= 47)) (PreH14 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_8 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (p <> 0) ”
.

Definition solver_safety_wit_9 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> (remainder ÷ p ))
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "p" ) )) # UInt64  |-> p)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ ((factor_count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (factor_count + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((p * p ) > remainder)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000001)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 < remainder)) (PreH14 : (remainder <= m_pre)) (PreH15 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_12 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (remainder) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_13 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pe" ) ) 0 (factor_count + 1 ) (app (pe_values) ((cons (1) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (remainder) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ ((factor_count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (factor_count + 1 )) ”
.

Definition solver_safety_wit_14 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_17 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_19 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (accumulator: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (accumulator = (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator )),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> accumulator)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  (UInt64Array.undef_full ( &( "pr" ) ) 64 )
  **  (UInt64Array.undef_full ( &( "pe" ) ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> 0)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= 2) ”
  &&  “ (2 <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < m_pre) ”
  &&  “ (m_pre <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre 2 m_pre pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  TT && emp 
|--
  “ (FactorMachineTrialState m_pre 2 m_pre (@nil Z) (@nil Z) ) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  (FactorMachineTrialState m_pre 2 m_pre (@nil Z) (@nil Z) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (m_pre: Z) (x_pre: Z) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )),
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_2 :=
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pe" ) ) 0 (factor_count_2 + 1 ) (app (pe_values_2) ((cons (0) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count_2 + 1 ) (app (pr_values_2) ((cons (p) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (original_remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000000) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= exponent) ”
  &&  “ (exponent <= 47) ”
  &&  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  TT && emp 
|--
  EX (original_remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)),
  “ ((Zlength (pr_values)) = ((Zlength (pr_values_2)) - 0 )) ”
  &&  “ ((app (pr_values_2) ((cons (p) ((@nil Z))))) = (app (pr_values) ((cons (p) ((@nil Z)))))) ”
  &&  “ ((Zlength (pe_values)) = ((Zlength (pr_values_2)) - 0 )) ”
  &&  “ ((app (pe_values_2) ((cons (0) ((@nil Z))))) = (app (pe_values) ((cons (exponent) ((@nil Z)))))) ”
  &&  “ (p <= 10000000) ”
  &&  “ ((Zlength (pr_values)) = (Zlength (pr_values_2))) ”
  &&  “ ((Zlength (pe_values)) = (Zlength (pr_values_2))) ”
  &&  “ (0 <= exponent) ”
  &&  “ (exponent <= 47) ”
  &&  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values ) ”
  &&  emp
).

Definition solver_entail_wit_3 :=
(
forall (m_pre: Z) (x_pre: Z) (original_remainder_2: Z) (remainder: Z) (exponent_2: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent_2)) (PreH14 : (exponent_2 <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder_2 remainder exponent_2 pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pe" ) ) factor_count_2 (factor_count_2 + 1 ) (replace_Znth ((factor_count_2 - factor_count_2 )) ((unsigned_last_nbits (((Znth (factor_count_2 - factor_count_2 ) (cons (exponent_2) ((@nil Z))) 0) + 1 )) (64))) ((cons (exponent_2) ((@nil Z))))) )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values_2 )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count_2 (factor_count_2 + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values_2 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (original_remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000000) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= exponent) ”
  &&  “ (exponent <= 47) ”
  &&  “ (FactorMachineAtPrime m_pre p original_remainder (remainder ÷ p ) exponent pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (original_remainder_2: Z) (remainder: Z) (exponent_2: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent_2)) (PreH14 : (exponent_2 <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder_2 remainder exponent_2 pr_values_2 pe_values_2 )),
  TT && emp 
|--
  EX (original_remainder: Z) (exponent: Z),
  “ ((replace_Znth (((Zlength (pr_values_2)) - (Zlength (pr_values_2)) )) ((unsigned_last_nbits (((Znth ((Zlength (pr_values_2)) - (Zlength (pr_values_2)) ) (cons (exponent_2) ((@nil Z))) 0) + 1 )) (64))) ((cons (exponent_2) ((@nil Z))))) = (cons (exponent) ((@nil Z)))) ”
  &&  “ (0 <= exponent) ”
  &&  “ (exponent <= 47) ”
  &&  “ (FactorMachineAtPrime m_pre p original_remainder (remainder ÷ p ) exponent pr_values_2 pe_values_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_1 :=
(
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values_2 )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count_2 (factor_count_2 + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values_2 )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count_2 (factor_count_2 + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> (factor_count_2 + 1 ))
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < remainder) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre (p + 1 ) remainder pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  TT && emp 
|--
  “ (FactorMachineTrialState m_pre (p + 1 ) remainder (app (pr_values_2) ((cons (p) ((@nil Z))))) (app (pe_values_2) ((cons (exponent) ((@nil Z))))) ) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (0 < remainder) ”
  &&  “ ((Zlength ((app (pe_values_2) ((cons (exponent) ((@nil Z))))))) = (factor_count_2 + 1 )) ”
  &&  “ ((Zlength ((app (pr_values_2) ((cons (p) ((@nil Z))))))) = (factor_count_2 + 1 )) ”
  &&  “ ((factor_count_2 + 1 ) < 64) ”
  &&  emp
).

Definition solver_entail_wit_4_1_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  (FactorMachineTrialState m_pre (p + 1 ) remainder (app (pr_values_2) ((cons (p) ((@nil Z))))) (app (pe_values_2) ((cons (exponent) ((@nil Z))))) )
.

Definition solver_entail_wit_4_1_split_goal_2 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  (remainder <= m_pre)
.

Definition solver_entail_wit_4_1_split_goal_3 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  (0 < remainder)
.

Definition solver_entail_wit_4_1_split_goal_4 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  ((Zlength ((app (pe_values_2) ((cons (exponent) ((@nil Z))))))) = (factor_count_2 + 1 ))
.

Definition solver_entail_wit_4_1_split_goal_5 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  ((Zlength ((app (pr_values_2) ((cons (p) ((@nil Z))))))) = (factor_count_2 + 1 ))
.

Definition solver_entail_wit_4_1_split_goal_6 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2 )),
  ((factor_count_2 + 1 ) < 64)
.

Definition solver_entail_wit_4_2 :=
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values_2 )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count_2 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values_2 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count_2 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= (p + 1 )) ”
  &&  “ ((p + 1 ) <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < remainder) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre (p + 1 ) remainder pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  TT && emp 
|--
  “ (FactorMachineTrialState m_pre (p + 1 ) remainder pr_values_2 pe_values_2 ) ”
  &&  emp
).

Definition solver_entail_wit_4_2_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) <> 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (FactorMachineTrialState m_pre (p + 1 ) remainder pr_values_2 pe_values_2 )
.

Definition solver_entail_wit_5_1 :=
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pe" ) ) 0 (factor_count_2 + 1 ) (app (pe_values_2) ((cons (1) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count_2 + 1 ) (app (pr_values_2) ((cons (remainder) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> (factor_count_2 + 1 ))
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count <= 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  TT && emp 
|--
  “ (ValidFactorTable m_pre (app (pr_values_2) ((cons (remainder) ((@nil Z))))) (app (pe_values_2) ((cons (1) ((@nil Z))))) ) ”
  &&  “ ((Zlength ((app (pe_values_2) ((cons (1) ((@nil Z))))))) = (factor_count_2 + 1 )) ”
  &&  “ ((Zlength ((app (pr_values_2) ((cons (remainder) ((@nil Z))))))) = (factor_count_2 + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_5_1_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (ValidFactorTable m_pre (app (pr_values_2) ((cons (remainder) ((@nil Z))))) (app (pe_values_2) ((cons (1) ((@nil Z))))) )
.

Definition solver_entail_wit_5_1_split_goal_2 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  ((Zlength ((app (pe_values_2) ((cons (1) ((@nil Z))))))) = (factor_count_2 + 1 ))
.

Definition solver_entail_wit_5_1_split_goal_3 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  ((Zlength ((app (pr_values_2) ((cons (remainder) ((@nil Z))))))) = (factor_count_2 + 1 ))
.

Definition solver_entail_wit_5_2 :=
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder <= 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values_2 )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count_2 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values_2 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count_2 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count <= 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder <= 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  TT && emp 
|--
  “ (ValidFactorTable m_pre pr_values_2 pe_values_2 ) ”
  &&  emp
).

Definition solver_entail_wit_5_2_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values_2: (@list Z)) (pr_values_2: (@list Z)) (factor_count_2: Z) (p: Z) (PreH1 : (remainder <= 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2 )),
  (ValidFactorTable m_pre pr_values_2 pe_values_2 )
.

Definition solver_entail_wit_6 :=
(
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values_2 )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count_2 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values_2 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count_2 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  EX (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count <= 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_pre 0 1 1 1 ) ”
  &&  “ (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1))) ”
  &&  “ ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
) \/
(
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )),
  TT && emp 
|--
  “ ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre) ”
  &&  “ (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1))) ”
  &&  “ (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )),
  ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)
.

Definition solver_entail_wit_6_split_goal_2 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )),
  (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))
.

Definition solver_entail_wit_6_split_goal_3 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )),
  (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )
.

Definition solver_entail_wit_7 :=
(
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values_2 )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count_2 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values_2 )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count_2 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> (0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ))
|--
  EX (accumulator: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z),
  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count <= 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  “ (accumulator = (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1))) ”
  &&  “ (CycleAnswer m_pre x_pre accumulator ) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> accumulator)
) \/
(
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  TT && emp 
|--
  “ (CycleAnswer m_pre x_pre (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) ”
  &&  “ ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1))) ”
  &&  “ ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1))) ”
  &&  “ ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1))) ”
  &&  “ ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1))) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  (CycleAnswer m_pre x_pre (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) )
.

Definition solver_entail_wit_7_split_goal_2 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))
.

Definition solver_entail_wit_7_split_goal_3 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))
.

Definition solver_entail_wit_7_split_goal_4 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))
.

Definition solver_entail_wit_7_split_goal_5 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (pr_values_2: (@list Z)) (pe_values_2: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2 )) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) <= m_pre)),
  ((0 + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)) ) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) (0) (1)))
.

Definition solver_return_wit_1 :=
(
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (accumulator_2: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count_2 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count_2 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count_2)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> accumulator_2)
|--
  EX (accumulator: Z) (base: Z) (factor_count: Z),
  “ (Spec m_pre x_pre (unsigned_last_nbits ((accumulator_2 + 1 )) (64)) ) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count <= 64) ”
  &&  (UInt64Array.seg_shape ( &( "pr" ) ) 0 factor_count )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg_shape ( &( "pe" ) ) 0 factor_count )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> base)
  **  ((( &( "total_" ) )) # UInt64  |-> accumulator)
) \/
(
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (accumulator_2: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values )
|--
  “ (Spec m_pre x_pre (unsigned_last_nbits ((accumulator_2 + 1 )) (64)) ) ”
  &&  (UInt64Array.seg_shape ( &( "pr" ) ) 0 factor_count_2 )
  **  (UInt64Array.seg_shape ( &( "pe" ) ) 0 factor_count_2 )
).

Definition solver_return_wit_1_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (accumulator_2: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values )
|--
  “ (Spec m_pre x_pre (unsigned_last_nbits ((accumulator_2 + 1 )) (64)) ) ”
.

Definition solver_return_wit_1_split_goal_spatial :=
forall (m_pre: Z) (x_pre: Z) (factor_count_2: Z) (accumulator_2: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2 )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count_2 pr_values )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count_2 pe_values )
|--
  (UInt64Array.seg_shape ( &( "pr" ) ) 0 factor_count_2 )
  **  (UInt64Array.seg_shape ( &( "pe" ) ) 0 factor_count_2 )
.

Definition solver_partial_solve_wit_1 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ ((remainder % ( p ) ) = 0) ”
  &&  “ ((p * p ) <= remainder) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < remainder) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values ) ”
  &&  (((( &( "pr" ) ) + (factor_count * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
.

Definition solver_partial_solve_wit_2 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : ((p * p ) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (p) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ ((remainder % ( p ) ) = 0) ”
  &&  “ ((p * p ) <= remainder) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < remainder) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values ) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (p) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
.

Definition solver_partial_solve_wit_3 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ ((remainder % ( p ) ) = 0) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000000) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= exponent) ”
  &&  “ (exponent <= 47) ”
  &&  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values ) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64  |-> (Znth (factor_count - factor_count ) (cons (exponent) ((@nil Z))) 0))
  **  (UInt64Array.missing_i ( &( "pe" ) ) factor_count factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
.

Definition solver_partial_solve_wit_4 :=
forall (m_pre: Z) (x_pre: Z) (original_remainder: Z) (remainder: Z) (exponent: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : ((remainder % ( p ) ) = 0)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre )) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : (0 <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : (0 <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values )),
  (UInt64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ ((remainder % ( p ) ) = 0) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000000) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= exponent) ”
  &&  “ (exponent <= 47) ”
  &&  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values ) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i ( &( "pe" ) ) factor_count factor_count (factor_count + 1 ) (cons (exponent) ((@nil Z))) )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1 ) (cons (p) ((@nil Z))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
.

Definition solver_partial_solve_wit_5 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (remainder > 1) ”
  &&  “ ((p * p ) > remainder) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < remainder) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values ) ”
  &&  (((( &( "pr" ) ) + (factor_count * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
.

Definition solver_partial_solve_wit_6 :=
forall (m_pre: Z) (x_pre: Z) (remainder: Z) (pe_values: (@list Z)) (pr_values: (@list Z)) (factor_count: Z) (p: Z) (PreH1 : (remainder > 1)) (PreH2 : ((p * p ) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre )) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : (0 <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : (0 < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values )),
  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (remainder) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
|--
  “ (remainder > 1) ”
  &&  “ ((p * p ) > remainder) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (2 <= p) ”
  &&  “ (p <= 10000001) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count < 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 < remainder) ”
  &&  “ (remainder <= m_pre) ”
  &&  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values ) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg ( &( "pe" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pr" ) ) 0 (factor_count + 1 ) (app (pr_values) ((cons (remainder) ((@nil Z))))) )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) (factor_count + 1 ) 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |->_)
  **  ((( &( "total_" ) )) # UInt64  |->_)
.

Definition solver_partial_solve_wit_7_pure :=
(
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (0 < 1) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_pre 0 1 1 1 ) ”
  &&  “ (WalkBudget m_pre 0 (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) ) ”
  &&  “ (WalkMachineBounds m_pre 1 1 1 ) ”
  &&  “ (WalkGlobalBounds m_pre x_pre ) ”
) \/
(
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (remainder <= UINT64_MAX)) (PreH3 : (x_pre <= UINT64_MAX)) (PreH4 : (m_pre <= UINT64_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (remainder >= 0)) (PreH7 : (x_pre >= 0)) (PreH8 : (m_pre >= 0)) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre )) (PreH16 : (0 <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values )) (PreH21 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH22 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (WalkGlobalBounds m_pre x_pre ) ”
  &&  “ (WalkMachineBounds m_pre 1 1 1 ) ”
  &&  “ (WalkBudget m_pre 0 (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) ) ”
).

Definition solver_partial_solve_wit_7_pure_split_goal_1 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (remainder <= UINT64_MAX)) (PreH3 : (x_pre <= UINT64_MAX)) (PreH4 : (m_pre <= UINT64_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (remainder >= 0)) (PreH7 : (x_pre >= 0)) (PreH8 : (m_pre >= 0)) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre )) (PreH16 : (0 <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values )) (PreH21 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH22 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (WalkGlobalBounds m_pre x_pre ) ”
.

Definition solver_partial_solve_wit_7_pure_split_goal_2 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (remainder <= UINT64_MAX)) (PreH3 : (x_pre <= UINT64_MAX)) (PreH4 : (m_pre <= UINT64_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (remainder >= 0)) (PreH7 : (x_pre >= 0)) (PreH8 : (m_pre >= 0)) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre )) (PreH16 : (0 <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values )) (PreH21 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH22 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (WalkMachineBounds m_pre 1 1 1 ) ”
.

Definition solver_partial_solve_wit_7_pure_split_goal_3 :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (remainder: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (remainder <= UINT64_MAX)) (PreH3 : (x_pre <= UINT64_MAX)) (PreH4 : (m_pre <= UINT64_MAX)) (PreH5 : (0 >= 0)) (PreH6 : (remainder >= 0)) (PreH7 : (x_pre >= 0)) (PreH8 : (m_pre >= 0)) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre )) (PreH16 : (0 <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values )) (PreH21 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH22 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  ((( &( "m" ) )) # UInt64  |-> m_pre)
  **  ((( &( "x" ) )) # UInt64  |-> x_pre)
  **  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "t" ) )) # UInt64  |-> remainder)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ (WalkBudget m_pre 0 (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) ) ”
.

Definition solver_partial_solve_wit_7_aux :=
forall (m_pre: Z) (x_pre: Z) (factor_count: Z) (pr_values: (@list Z)) (pe_values: (@list Z)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre )) (PreH6 : (0 <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values )) (PreH11 : (PrefixChoice pr_values pe_values x_pre 0 1 1 1 )) (PreH12 : (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre)),
  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
|--
  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (0 < 1) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_pre 0 1 1 1 ) ”
  &&  “ (WalkBudget m_pre 0 (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) ) ”
  &&  “ (WalkMachineBounds m_pre 1 1 1 ) ”
  &&  “ (WalkGlobalBounds m_pre x_pre ) ”
  &&  “ (2 <= m_pre) ”
  &&  “ (m_pre <= 100000000000000) ”
  &&  “ (1 <= x_pre) ”
  &&  “ (x_pre < m_pre) ”
  &&  “ (Pre m_pre x_pre ) ”
  &&  “ (0 <= factor_count) ”
  &&  “ (factor_count <= 64) ”
  &&  “ ((Zlength (pr_values)) = factor_count) ”
  &&  “ ((Zlength (pe_values)) = factor_count) ”
  &&  “ (ValidFactorTable m_pre pr_values pe_values ) ”
  &&  “ (PrefixChoice pr_values pe_values x_pre 0 1 1 1 ) ”
  &&  “ (0 <= (WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1))) ”
  &&  “ ((WalkSuffix (pr_values) (pe_values) (x_pre) (0) (1)) <= m_pre) ”
  &&  (UInt64Array.seg ( &( "pr" ) ) 0 factor_count pr_values )
  **  (UInt64Array.undef_seg ( &( "pr" ) ) factor_count 64 )
  **  (UInt64Array.seg ( &( "pe" ) ) 0 factor_count pe_values )
  **  (UInt64Array.undef_seg ( &( "pe" ) ) factor_count 64 )
  **  ((( &( "nf" ) )) # Int  |-> factor_count)
  **  ((( &( "x_" ) )) # UInt64  |-> x_pre)
  **  ((( &( "total_" ) )) # UInt64  |-> 0)
.

Definition solver_partial_solve_wit_7 := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux.

Module Type VC_Correct.


Axiom proof_of_mulmod_safety_wit_1 : mulmod_safety_wit_1.
Axiom proof_of_mulmod_safety_wit_2 : mulmod_safety_wit_2.
Axiom proof_of_mulmod_safety_wit_3 : mulmod_safety_wit_3.
Axiom proof_of_mulmod_safety_wit_4 : mulmod_safety_wit_4.
Axiom proof_of_mulmod_safety_wit_5 : mulmod_safety_wit_5.
Axiom proof_of_mulmod_safety_wit_6 : mulmod_safety_wit_6.
Axiom proof_of_mulmod_safety_wit_7 : mulmod_safety_wit_7.
Axiom proof_of_mulmod_safety_wit_8 : mulmod_safety_wit_8.
Axiom proof_of_mulmod_safety_wit_9 : mulmod_safety_wit_9.
Axiom proof_of_mulmod_safety_wit_10 : mulmod_safety_wit_10.
Axiom proof_of_mulmod_safety_wit_11 : mulmod_safety_wit_11.
Axiom proof_of_mulmod_safety_wit_12 : mulmod_safety_wit_12.
Axiom proof_of_mulmod_safety_wit_13 : mulmod_safety_wit_13.
Axiom proof_of_mulmod_safety_wit_14 : mulmod_safety_wit_14.
Axiom proof_of_mulmod_safety_wit_15 : mulmod_safety_wit_15.
Axiom proof_of_mulmod_safety_wit_16 : mulmod_safety_wit_16.
Axiom proof_of_mulmod_safety_wit_17 : mulmod_safety_wit_17.
Axiom proof_of_mulmod_safety_wit_18 : mulmod_safety_wit_18.
Axiom proof_of_mulmod_safety_wit_19 : mulmod_safety_wit_19.
Axiom proof_of_mulmod_safety_wit_20 : mulmod_safety_wit_20.
Axiom proof_of_mulmod_safety_wit_21 : mulmod_safety_wit_21.
Axiom proof_of_mulmod_safety_wit_22 : mulmod_safety_wit_22.
Axiom proof_of_mulmod_entail_wit_1 : mulmod_entail_wit_1.
Axiom proof_of_mulmod_entail_wit_2_1 : mulmod_entail_wit_2_1.
Axiom proof_of_mulmod_entail_wit_2_2 : mulmod_entail_wit_2_2.
Axiom proof_of_mulmod_entail_wit_2_3 : mulmod_entail_wit_2_3.
Axiom proof_of_mulmod_entail_wit_2_4 : mulmod_entail_wit_2_4.
Axiom proof_of_mulmod_entail_wit_2_5 : mulmod_entail_wit_2_5.
Axiom proof_of_mulmod_entail_wit_2_6 : mulmod_entail_wit_2_6.
Axiom proof_of_mulmod_return_wit_1 : mulmod_return_wit_1.
Axiom proof_of_powmod_safety_wit_1 : powmod_safety_wit_1.
Axiom proof_of_powmod_safety_wit_2 : powmod_safety_wit_2.
Axiom proof_of_powmod_safety_wit_3 : powmod_safety_wit_3.
Axiom proof_of_powmod_safety_wit_4 : powmod_safety_wit_4.
Axiom proof_of_powmod_safety_wit_5 : powmod_safety_wit_5.
Axiom proof_of_powmod_safety_wit_6 : powmod_safety_wit_6.
Axiom proof_of_powmod_safety_wit_7 : powmod_safety_wit_7.
Axiom proof_of_powmod_safety_wit_8 : powmod_safety_wit_8.
Axiom proof_of_powmod_entail_wit_1 : powmod_entail_wit_1.
Axiom proof_of_powmod_entail_wit_2_1 : powmod_entail_wit_2_1.
Axiom proof_of_powmod_entail_wit_2_2 : powmod_entail_wit_2_2.
Axiom proof_of_powmod_return_wit_1 : powmod_return_wit_1.
Axiom proof_of_powmod_partial_solve_wit_1_pure : powmod_partial_solve_wit_1_pure.
Axiom proof_of_powmod_partial_solve_wit_1 : powmod_partial_solve_wit_1.
Axiom proof_of_powmod_partial_solve_wit_2_pure : powmod_partial_solve_wit_2_pure.
Axiom proof_of_powmod_partial_solve_wit_2 : powmod_partial_solve_wit_2.
Axiom proof_of_powmod_partial_solve_wit_3_pure : powmod_partial_solve_wit_3_pure.
Axiom proof_of_powmod_partial_solve_wit_3 : powmod_partial_solve_wit_3.
Axiom proof_of_gcd__safety_wit_1 : gcd__safety_wit_1.
Axiom proof_of_gcd__entail_wit_1 : gcd__entail_wit_1.
Axiom proof_of_gcd__entail_wit_2 : gcd__entail_wit_2.
Axiom proof_of_gcd__return_wit_1 : gcd__return_wit_1.
Axiom proof_of_order_safety_wit_1 : order_safety_wit_1.
Axiom proof_of_order_safety_wit_2 : order_safety_wit_2.
Axiom proof_of_order_safety_wit_3 : order_safety_wit_3.
Axiom proof_of_order_safety_wit_4 : order_safety_wit_4.
Axiom proof_of_order_safety_wit_5 : order_safety_wit_5.
Axiom proof_of_order_safety_wit_6 : order_safety_wit_6.
Axiom proof_of_order_safety_wit_7 : order_safety_wit_7.
Axiom proof_of_order_safety_wit_8 : order_safety_wit_8.
Axiom proof_of_order_safety_wit_9 : order_safety_wit_9.
Axiom proof_of_order_safety_wit_10 : order_safety_wit_10.
Axiom proof_of_order_safety_wit_11 : order_safety_wit_11.
Axiom proof_of_order_safety_wit_12 : order_safety_wit_12.
Axiom proof_of_order_safety_wit_13 : order_safety_wit_13.
Axiom proof_of_order_safety_wit_14 : order_safety_wit_14.
Axiom proof_of_order_safety_wit_15 : order_safety_wit_15.
Axiom proof_of_order_safety_wit_16 : order_safety_wit_16.
Axiom proof_of_order_safety_wit_17 : order_safety_wit_17.
Axiom proof_of_order_safety_wit_18 : order_safety_wit_18.
Axiom proof_of_order_safety_wit_19 : order_safety_wit_19.
Axiom proof_of_order_entail_wit_1 : order_entail_wit_1.
Axiom proof_of_order_entail_wit_2 : order_entail_wit_2.
Axiom proof_of_order_entail_wit_3 : order_entail_wit_3.
Axiom proof_of_order_entail_wit_4 : order_entail_wit_4.
Axiom proof_of_order_entail_wit_5 : order_entail_wit_5.
Axiom proof_of_order_entail_wit_6_1 : order_entail_wit_6_1.
Axiom proof_of_order_entail_wit_6_2 : order_entail_wit_6_2.
Axiom proof_of_order_entail_wit_6_3 : order_entail_wit_6_3.
Axiom proof_of_order_entail_wit_7 : order_entail_wit_7.
Axiom proof_of_order_entail_wit_8 : order_entail_wit_8.
Axiom proof_of_order_return_wit_1 : order_return_wit_1.
Axiom proof_of_order_return_wit_2 : order_return_wit_2.
Axiom proof_of_order_return_wit_3 : order_return_wit_3.
Axiom proof_of_order_return_wit_4 : order_return_wit_4.
Axiom proof_of_order_partial_solve_wit_1_pure : order_partial_solve_wit_1_pure.
Axiom proof_of_order_partial_solve_wit_1 : order_partial_solve_wit_1.
Axiom proof_of_order_partial_solve_wit_2_pure : order_partial_solve_wit_2_pure.
Axiom proof_of_order_partial_solve_wit_2 : order_partial_solve_wit_2.
Axiom proof_of_walk_safety_wit_1 : walk_safety_wit_1.
Axiom proof_of_walk_safety_wit_2 : walk_safety_wit_2.
Axiom proof_of_walk_safety_wit_3 : walk_safety_wit_3.
Axiom proof_of_walk_safety_wit_4 : walk_safety_wit_4.
Axiom proof_of_walk_safety_wit_5 : walk_safety_wit_5.
Axiom proof_of_walk_safety_wit_6 : walk_safety_wit_6.
Axiom proof_of_walk_safety_wit_7 : walk_safety_wit_7.
Axiom proof_of_walk_safety_wit_8 : walk_safety_wit_8.
Axiom proof_of_walk_safety_wit_9 : walk_safety_wit_9.
Axiom proof_of_walk_safety_wit_10 : walk_safety_wit_10.
Axiom proof_of_walk_safety_wit_11 : walk_safety_wit_11.
Axiom proof_of_walk_safety_wit_12 : walk_safety_wit_12.
Axiom proof_of_walk_safety_wit_13 : walk_safety_wit_13.
Axiom proof_of_walk_entail_wit_1 : walk_entail_wit_1.
Axiom proof_of_walk_entail_wit_2 : walk_entail_wit_2.
Axiom proof_of_walk_entail_wit_3 : walk_entail_wit_3.
Axiom proof_of_walk_entail_wit_4_1 : walk_entail_wit_4_1.
Axiom proof_of_walk_entail_wit_4_2 : walk_entail_wit_4_2.
Axiom proof_of_walk_entail_wit_5 : walk_entail_wit_5.
Axiom proof_of_walk_entail_wit_6 : walk_entail_wit_6.
Axiom proof_of_walk_return_wit_1 : walk_return_wit_1.
Axiom proof_of_walk_return_wit_2 : walk_return_wit_2.
Axiom proof_of_walk_return_wit_3 : walk_return_wit_3.
Axiom proof_of_walk_partial_solve_wit_1_pure : walk_partial_solve_wit_1_pure.
Axiom proof_of_walk_partial_solve_wit_1 : walk_partial_solve_wit_1.
Axiom proof_of_walk_partial_solve_wit_2 : walk_partial_solve_wit_2.
Axiom proof_of_walk_partial_solve_wit_3 : walk_partial_solve_wit_3.
Axiom proof_of_walk_partial_solve_wit_4_pure : walk_partial_solve_wit_4_pure.
Axiom proof_of_walk_partial_solve_wit_4 : walk_partial_solve_wit_4.
Axiom proof_of_walk_partial_solve_wit_5_pure : walk_partial_solve_wit_5_pure.
Axiom proof_of_walk_partial_solve_wit_5 : walk_partial_solve_wit_5.
Axiom proof_of_walk_partial_solve_wit_6_pure : walk_partial_solve_wit_6_pure.
Axiom proof_of_walk_partial_solve_wit_6 : walk_partial_solve_wit_6.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.

End VC_Correct.
