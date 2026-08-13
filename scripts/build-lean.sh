#!/usr/bin/env sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root/Lean"

task="${1:-build}"
case "$task" in
  build)
    make build
    ;;
  clean)
    make clean
    ;;
  *)
    printf 'usage: %s [build|clean]\n' "$0" >&2
    exit 2
    ;;
esac
