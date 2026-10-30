#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_dir/.."
scope="${1:-all}"
case "$scope" in
  all|qcp-demos-llm|llm-bench) ;;
  *) echo "Usage: $0 [all|qcp-demos-llm|llm-bench]" >&2; exit 2 ;;
esac
scratch="$(mktemp -d)"
cleanup() {
  rm -f -- "$scratch"/*.lean "$scratch"/*.sacgen.tmp
  rmdir -- "$scratch"
}
trap cleanup EXIT

while IFS='|' read -r tool source relative_output stem; do
  [[ -z "$tool" || "$tool" == \#* ]] && continue
  stem="${stem%$'\r'}"
  case "$scope:$relative_output" in
    qcp-demos-llm:SimpleC/EE/LLM_bench/*|llm-bench:SimpleC/EE/QCP_demos_LLM/*) continue ;;
  esac
  binary="bin/linux/$tool"
  [[ -x "$binary" ]] || { echo "Missing executable: $binary" >&2; exit 2; }
  [[ -f "$source" ]] || { echo "Missing input: $source" >&2; exit 2; }
  source_dir="${source%/*}/"
  source_namespace="${source_dir#QCP_examples/}"
  source_namespace="SimpleC.EE.${source_namespace%/}"
  source_namespace="${source_namespace//\//.}"
  output_namespace="${relative_output//\//.}"
  [[ "$source" == QCP_examples/* ]] || source_namespace="$output_namespace"
  name_args=()
  if [[ "$tool" == symexec && "${source##*/}" != "$stem.${source##*.}" ]]; then
    name_args=("--input-file-name=$stem.${source##*.}")
  fi
  echo "Generating Lean: $source"
  "$binary" \
    "-I$source_dir" -slp "$source_dir" "$source_namespace" \
    -slp QCP_examples/LLM_bench/ SimpleC.EE.LLM_bench \
    -IQCP_examples/verification/ -slp QCP_examples/verification/ SimpleC.Verification \
    -IQCP_examples/QCP_demos_LLM/ -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
    -IQCP_examples/LLM_bench/Codeforces/ \
    -IQCP_examples/stdlib/ -slp QCP_examples/stdlib/ SimpleC.stdlib \
    "--input-file=$source" "${name_args[@]}" \
    --no-exec-info --no-coq-gen \
    "--lean-output-dir=$scratch" "--lean-logic-path=$output_namespace"
  generated_stem="$stem"
  [[ "$tool" != StrategyCheck ]] || generated_stem="${stem}_strategy"
  for suffix in _goal.lean _goal_check.lean; do
    [[ -f "$scratch/$generated_stem$suffix" ]] || {
      echo "Generator did not produce $generated_stem$suffix" >&2; exit 1;
    }
  done
  destination="Lean/examples/$relative_output"
  mkdir -p "$destination"
  # Publish native VCs unchanged, retaining existing reviewed proof files.
  for file in "$scratch"/*.lean; do
    name="${file##*/}"
    if [[ "$name" == *_goal.lean || "$name" == *_goal_check.lean || ! -f "$destination/$name" ]]; then
      cp -- "$file" "$destination/$name"
    fi
  done
  rm -f -- "$scratch"/*.lean "$scratch"/*.sacgen.tmp
done < "$script_dir/lean-generation-inputs.txt"
echo "Lean generation completed ($scope)."
