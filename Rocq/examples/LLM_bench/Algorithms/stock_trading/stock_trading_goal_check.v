From SimpleC.EE.LLM_bench.Algorithms.stock_trading Require Import stock_trading_goal stock_trading_proof_auto stock_trading_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include stock_trading_proof_auto.
  Include stock_trading_proof_manual.
End VC_Correctness.
