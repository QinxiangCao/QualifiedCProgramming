From SimpleC.EE.LLM_bench.Algorithms.stock_trading Require Import stock_trading_goal stock_trading_proof_auto stock_trading_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array2_strategy_proof.
  Include stock_trading_proof_auto.
  Include stock_trading_proof_manual.
End VC_Correctness.
