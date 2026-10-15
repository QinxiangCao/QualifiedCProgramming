#!/usr/bin/env bash
#
# Standalone canonical symexec runner for a single QCP C case.
#
# Mirrors the argv built by
#   .agents/scripts/verification-orchestrator/symexec_tooling.py, calling that
#   module's build_symexec_plan for the canonical search paths and mirroring
#   its _driver_for_platform plus the formal path derivation in
#   .agents/scripts/vc-proving/path_utils.py (target_files_for_c),
# with output_root == main root, exactly as the annotation phase runs it.
#
# This is a debugging convenience only. The verification workflow itself must
# still go through controller.py; do not use this script as a substitute inside
# a run.
#
# Usage:
#   ./symexec.sh QCP_examples/<dir>/<case>.c
#   ./symexec.sh -C_FILE=QCP_examples/<dir>/<case>.c
#   ./symexec.sh --c-file=QCP_examples/<dir>/<case>.c [extra symexec flags...]
#
# Examples:
#   ./symexec.sh QCP_examples/LLM_bench/Codeforces/examples_100_code/P081_22A_second_order_statistics.c
#   ./symexec.sh -C_FILE=.../case.c --print-exec-info   # append/override driver flags
#
# The driver never overwrites an existing generated file, so this script first
# removes the four generated files (backing them up under .tmp/symexec-backups/),
# exactly as the controller's generated-refresh transaction does. A proof manual
# containing real proofs (Qed./Defined.) is protected: it is kept and NOT
# regenerated unless you pass --force-manual.
#
# Options:
#   -c, --clean        remove this case's generated files (and their .vo/.glob/
#                      .aux build products) and exit without running symexec
#       --lsp          run the lsp binary instead: parse/typecheck only, no Coq
#                      generation and no file refresh. Defaults to -s 1; pass a
#                      different -s N to override. Source is fed on stdin.
#   -n, --dry-run      print the command that would run, then exit
#       --force-manual refresh/remove the proof manual even if it holds proofs
#       --keep         do not remove anything (driver will skip existing files)
#   -h, --help         show this help
#
# Clean this case, leaving the hand-written <case>_lib.v alone:
#   ./symexec.sh --clean QCP_examples/<dir>/<case>.c

set -uo pipefail

MAIN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

die() { printf 'symexec.sh: %s\n' "$1" >&2; exit 2; }

usage() { sed -n '3,43p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

C_FILE=""
DRY_RUN=0
FORCE_MANUAL=0
KEEP=0
CLEAN=0
LSP=0
EXTRA_ARGS=()

while [ $# -gt 0 ]; do
  case "$1" in
    -h|--help)      usage; exit 0 ;;
    -n|--dry-run)   DRY_RUN=1 ;;
    --force-manual) FORCE_MANUAL=1 ;;
    --keep)         KEEP=1 ;;
    -c|--clean)     CLEAN=1 ;;
    --lsp)          LSP=1 ;;
    -C_FILE=*)      C_FILE="${1#-C_FILE=}" ;;
    -C_FIEL=*)      C_FILE="${1#-C_FIEL=}" ;;   # tolerate the common typo
    --c-file=*)     C_FILE="${1#--c-file=}" ;;
    --c-file|-C_FILE)
                    shift; [ $# -gt 0 ] || die "$1 needs a value"; C_FILE="$1" ;;
    -s)             shift; [ $# -gt 0 ] || die "-s needs a value"; EXTRA_ARGS+=("-s" "$1") ;;
    -*)             EXTRA_ARGS+=("$1") ;;
    *)              if [ -z "$C_FILE" ]; then C_FILE="$1"; else EXTRA_ARGS+=("$1"); fi ;;
  esac
  shift
done

[ -n "$C_FILE" ] || { usage >&2; die "no C file given"; }

# ---- normalize the target to a main-root-relative path ---------------------
case "$C_FILE" in
  /*) C_REL="${C_FILE#"$MAIN_ROOT"/}"
      [ "$C_REL" != "$C_FILE" ] || die "target C file is outside the repository: $C_FILE" ;;
  *)  C_REL="$C_FILE" ;;
esac
C_REL="${C_REL#./}"

case "$C_REL" in
  *..*) die "target C path must not contain '..': $C_REL" ;;
  *.c)  ;;
  *)    die "target must be a .c file: $C_REL" ;;
esac

[ -f "$MAIN_ROOT/$C_REL" ] || die "target C file not found: $MAIN_ROOT/$C_REL"
[ -d "$MAIN_ROOT/QCP_examples" ] && [ -d "$MAIN_ROOT/Rocq" ] \
  || die "main root does not look like the QCP repository: $MAIN_ROOT"

# ---- derive every generated path from the C path (target_files_for_c) ------
CASE_NAME="$(basename "$C_REL" .c)"
C_DIR="$(dirname "$C_REL")"

# Logical parts = directory components, dropping a leading "QCP_examples".
LOGICAL_DIR="$C_DIR"
case "$LOGICAL_DIR" in
  QCP_examples)    LOGICAL_DIR="" ;;
  QCP_examples/*)  LOGICAL_DIR="${LOGICAL_DIR#QCP_examples/}" ;;
  .)               LOGICAL_DIR="" ;;
esac

if [ -n "$LOGICAL_DIR" ]; then
  FORMAL_DIR="Rocq/examples/$LOGICAL_DIR"
  ACTIVE_CASE_THEORY="SimpleC.EE.$(printf '%s' "$LOGICAL_DIR" | tr '/' '.')"
else
  FORMAL_DIR="Rocq/examples"
  ACTIVE_CASE_THEORY="SimpleC.EE"
fi

GOAL_FILE="$MAIN_ROOT/$FORMAL_DIR/${CASE_NAME}_goal.v"
PROOF_AUTO_FILE="$MAIN_ROOT/$FORMAL_DIR/${CASE_NAME}_proof_auto.v"
PROOF_MANUAL_FILE="$MAIN_ROOT/$FORMAL_DIR/${CASE_NAME}_proof_manual.v"
GOAL_CHECK_FILE="$MAIN_ROOT/$FORMAL_DIR/${CASE_NAME}_goal_check.v"   # written implicitly

# ---- platform driver (same selection as _driver_for_platform) -------------
UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"
if [ "$LSP" -eq 1 ]; then BIN="lsp"; else BIN="symexec"; fi

case "$UNAME_S" in
  Darwin)
    case "$UNAME_M" in
      arm64|aarch64) DRIVER="$MAIN_ROOT/mac-arm64-binary/$BIN" ;;
      x86_64|amd64)  DRIVER="$MAIN_ROOT/mac-x86-64-binary/$BIN" ;;
      *) die "unsupported macOS architecture for symexec: $UNAME_M" ;;
    esac ;;
  Linux)
    case "$UNAME_M" in
      x86_64|amd64) DRIVER="$MAIN_ROOT/linux-binary/$BIN" ;;
      *) die "unsupported Linux architecture for bundled symexec: $UNAME_M" ;;
    esac ;;
  MINGW*|MSYS*|CYGWIN*) DRIVER="$MAIN_ROOT/win-binary/$BIN.exe" ;;
  *) die "unsupported platform for symexec: $UNAME_S/$UNAME_M" ;;
esac

[ -f "$DRIVER" ]  || die "canonical symexec driver not found: $DRIVER"
[ -x "$DRIVER" ]  || die "canonical symexec driver is not executable: $DRIVER (see scripts/fix-binary-exec-bit.sh)"

# ---- canonical include / SLP / extra flags --------------------------------
# Derived by the controller's own resolver, which walks the target's include
# graph, so a case that includes a header or strategy outside QCP_demos_LLM
# gets the search paths that header needs.
SEARCH_ARGS=()
while IFS= read -r line; do
  SEARCH_ARGS+=("$line")
done < <(python3 - "$MAIN_ROOT" "$C_REL" "$CASE_NAME" <<'DERIVE'
import sys
from pathlib import Path

main_root = Path(sys.argv[1]).resolve()
scripts = main_root / ".agents" / "scripts"
sys.path[:0] = [
    str(scripts / "verification-orchestrator"),
    str(scripts / "vc-proving"),
]

from path_utils import target_files_for_c
from symexec_tooling import build_symexec_plan

target_relative, case_name = sys.argv[2], sys.argv[3]
plan = build_symexec_plan(
    main_root=main_root,
    target_c_file=main_root / target_relative,
    output_root=main_root,
    target_files=target_files_for_c(target_relative, case_name),
)
for argument in plan["include_args"]:
    print(f"-I{argument}")
for index, argument in enumerate(plan["slp_args"]):
    if index % 2 == 0:
        print("-slp")
    print(argument)
for argument in plan["extra_flags"]:
    print(argument)
DERIVE
)
[ ${#SEARCH_ARGS[@]} -gt 0 ] || die "cannot derive symexec search paths for $C_REL"

# lsp always reads the source on stdin; --input-file-path only names it for
# diagnostics and relative include resolution.
if [ "$LSP" -eq 1 ]; then
  CMD=(
    "$DRIVER"
    "--input-file-path" "$C_REL"
    "--no-coq-gen"
    "${SEARCH_ARGS[@]}"
    "--no-exec-info"
  )
  case " ${EXTRA_ARGS[*]-} " in *" -s "*) ;; *) CMD+=("-s" "1") ;; esac
else
  CMD=(
    "$DRIVER"
    "--goal-file=$GOAL_FILE"
    "--proof-auto-file=$PROOF_AUTO_FILE"
    "--proof-manual-file=$PROOF_MANUAL_FILE"
    "${SEARCH_ARGS[@]}"
    "--coq-logic-path=$ACTIVE_CASE_THEORY"
    "--input-file=$C_REL"
    "--no-exec-info"
  )
fi
[ ${#EXTRA_ARGS[@]} -gt 0 ] && CMD+=("${EXTRA_ARGS[@]}")

if [ "$DRY_RUN" -eq 1 ]; then
  printf 'cwd: %s\n' "$MAIN_ROOT"
  printf '%q ' "${CMD[@]}"
  [ "$LSP" -eq 1 ] && printf '< %q' "$C_REL"
  printf '\n'
  exit 0
fi

if [ "$LSP" -eq 1 ]; then
  cd "$MAIN_ROOT" || die "cannot enter main root: $MAIN_ROOT"
  "${CMD[@]}" < "$C_REL"
  RC=$?
  printf '\n--- lsp exit code: %d ---\n' "$RC"
  exit $RC
fi

# ---- generated refresh / clean --------------------------------------------
# The driver skips any output file that already exists, so stale files must go
# first. Anything removed is copied to .tmp/symexec-backups/<case>/<stamp>/.
BACKUP_DIR="$MAIN_ROOT/.tmp/symexec-backups/$CASE_NAME/$(date '+%Y%m%d%H%M%S')"
REMOVED=0

backup_and_remove() {
  local path="$1" verb="${2:-refreshed}"
  [ -f "$path" ] || return 0
  mkdir -p "$BACKUP_DIR"
  cp -p "$path" "$BACKUP_DIR/" || die "cannot back up $path"
  rm -f "$path"  || die "cannot remove $path"
  REMOVED=$((REMOVED + 1))
  printf '%s: %s (backup in %s)\n' "$verb" "${path#"$MAIN_ROOT"/}" "${BACKUP_DIR#"$MAIN_ROOT"/}"
}

# Remove the four generated .v files. The proof manual is protected when it
# holds finished proofs, mirroring the controller's protected-proof-manual rule.
remove_generated() {
  local verb="$1"
  backup_and_remove "$GOAL_FILE"       "$verb"
  backup_and_remove "$PROOF_AUTO_FILE" "$verb"
  backup_and_remove "$GOAL_CHECK_FILE" "$verb"

  if [ -s "$PROOF_MANUAL_FILE" ] \
     && grep -Eq '^[[:space:]]*(Qed|Defined)\.' "$PROOF_MANUAL_FILE" \
     && [ "$FORCE_MANUAL" -eq 0 ]; then
    printf 'protected: %s holds finished proofs; keeping it (pass --force-manual to remove it too)\n' \
      "${PROOF_MANUAL_FILE#"$MAIN_ROOT"/}"
  else
    backup_and_remove "$PROOF_MANUAL_FILE" "$verb"
  fi
}

if [ "$CLEAN" -eq 1 ]; then
  remove_generated "removed"
  # Stale Coq side products of the generated modules only; <case>_lib.v and its
  # build products are hand-written source and are never touched.
  for base in "${CASE_NAME}_goal" "${CASE_NAME}_proof_auto" \
              "${CASE_NAME}_proof_manual" "${CASE_NAME}_goal_check"; do
    for ext in vo vok vos glob; do
      f="$MAIN_ROOT/$FORMAL_DIR/$base.$ext"
      [ -f "$f" ] && { rm -f "$f" && REMOVED=$((REMOVED + 1)) \
        && printf 'removed: %s\n' "${f#"$MAIN_ROOT"/}"; }
    done
    f="$MAIN_ROOT/$FORMAL_DIR/.$base.aux"
    [ -f "$f" ] && { rm -f "$f" && REMOVED=$((REMOVED + 1)) \
      && printf 'removed: %s\n' "${f#"$MAIN_ROOT"/}"; }
  done
  [ "$REMOVED" -eq 0 ] && printf 'nothing to clean for %s\n' "$CASE_NAME"
  exit 0
fi

mkdir -p "$MAIN_ROOT/$FORMAL_DIR"

[ "$KEEP" -eq 0 ] && remove_generated "refreshed"

cd "$MAIN_ROOT" || die "cannot enter main root: $MAIN_ROOT"
"${CMD[@]}"
RC=$?

printf '\n--- symexec exit code: %d ---\n' "$RC"
if [ "$RC" -eq 0 ]; then
  for f in "$GOAL_FILE" "$PROOF_AUTO_FILE" "$PROOF_MANUAL_FILE" "$GOAL_CHECK_FILE"; do
    if [ -f "$f" ]; then
      printf 'generated: %s\n' "${f#"$MAIN_ROOT"/}"
    else
      printf 'MISSING:   %s\n' "${f#"$MAIN_ROOT"/}"
    fi
  done
fi
exit $RC
