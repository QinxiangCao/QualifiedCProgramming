#!/bin/sh
set -eu

binary_dirs='
linux-binary
mac-arm64-binary
mac-x86-64-binary
win-binary
'

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

mark_executable() {
  path=$1

  case "$path" in
    linux-binary/*|mac-arm64-binary/*|mac-x86-64-binary/*|win-binary/*) ;;
    *) return 0 ;;
  esac

  if git ls-files --error-unmatch -- "$path" >/dev/null 2>&1; then
    git update-index --chmod=+x -- "$path"
  fi
}

# Existing tracked binaries.
for dir in $binary_dirs; do
  git ls-files -- "$dir" |
    while IFS= read -r path; do
      mark_executable "$path"
    done
done

# Newly staged binaries.
git diff --cached --name-only --diff-filter=ACMR |
  while IFS= read -r path; do
    mark_executable "$path"
  done

exit 0
