#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_dir"

if [[ ! -x "linux-binary/symexec" ]]; then
  echo "[ERROR] linux-binary/symexec was not found or is not executable." >&2
  exit 2
fi
if [[ ! -x "linux-binary/StrategyCheck" ]]; then
  echo "[ERROR] linux-binary/StrategyCheck was not found or is not executable." >&2
  exit 2
fi

lean_out="Lean/examples/SimpleC/EE/QCP_demos_LLM/generated"
lean_logic="SimpleC.EE.QCP_demos_LLM.generated"
common_args=(
  "-IQCP_examples/QCP_demos_LLM/"
  "-slp" "QCP_examples/QCP_demos_LLM/" "SimpleC.EE.QCP_demos_LLM"
)

mkdir -p "$lean_out"

cases=(
  "poly_sll"
  "sll"
  "sll_insert_sort"
  "functional_queue"
  "dll_queue"
  "sll_queue"
  "simple_arith/abs"
  "simple_arith/add"
  "simple_arith/max3"
  "simple_arith/gcd"
  "simple_arith/Always_pos"
  "simple_arith/div_test"
  "simple_arith/exgcd"
  "simple_arith/delta"
  "simple_arith/test_prime"
  "sum"
  "bst_insert"
  "bst_insert_rec"
  "bst_fp_insert"
  "bst_fp_delete"
  "swap"
  "bst_delete_rec"
  "bst_delete_rec2"
  "avl_insert"
  "sll_auto"
  "dll_auto"
  "array_auto"
  "chars"
  "bubble_sort"
  "array_cases"
)

for case_name in "${cases[@]}"; do
  linux-binary/symexec \
    --no-coq-gen \
    --lean-output-dir="$lean_out" \
    --lean-logic-path="$lean_logic" \
    "${common_args[@]}" \
    --input-file="QCP_examples/QCP_demos_LLM/${case_name}.c" \
    --no-exec-info
done

strategies=(
  "common"
  "dll_queue"
  "bst"
)

for strategy_name in "${strategies[@]}"; do
  linux-binary/StrategyCheck \
    --no-coq-gen \
    --lean-output-dir="$lean_out" \
    --lean-logic-path="$lean_logic" \
    "${common_args[@]}" \
    --input-file="QCP_examples/QCP_demos_LLM/${strategy_name}.strategies" \
    --no-exec-info
done

echo "QCP_demos_LLM Lean files generated in $lean_out."
