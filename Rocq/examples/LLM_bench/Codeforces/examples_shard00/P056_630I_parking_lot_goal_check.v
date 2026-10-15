From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P056_630I_parking_lot_goal P056_630I_parking_lot_proof_auto P056_630I_parking_lot_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P056_630I_parking_lot_proof_auto.
  Include P056_630I_parking_lot_proof_manual.
End VC_Correctness.
