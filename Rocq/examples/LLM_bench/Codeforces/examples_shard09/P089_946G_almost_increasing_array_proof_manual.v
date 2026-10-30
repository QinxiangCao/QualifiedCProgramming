From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib.
Local Open Scope sac.

(* The 768 proof bodies live in the _partN files below.  Each part carries
   this same header, depends only on the goal/proof_auto/lib triple, and
   compiles independently of its siblings -- no lemma in one part is cited
   by another.  They are Included rather than merely Required so that this
   file remains a single module whose fields are every proof_of_* lemma,
   which is what P089_946G_almost_increasing_array_goal_check.v Includes. *)

Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part1.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part2.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part3.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part4.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part5.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part6.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part7.

Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part1.
Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part2.
Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part3.
Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part4.
Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part5.
Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part6.
Include SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_proof_manual_part7.
