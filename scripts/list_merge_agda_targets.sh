#!/usr/bin/env bash
set -euo pipefail

mode="${1:-merge-smoke}"

emit_existing_files() {
  local file
  for file in "$@"; do
    if [ -f "$file" ]; then
      printf '%s\n' "$file"
    fi
  done
}

emit_recursive_tree() {
  local dir
  for dir in "$@"; do
    if [ -d "$dir" ]; then
      find "$dir" -type f -name '*.agda'
    fi
  done | LC_ALL=C sort
}

case "$mode" in
  authoritative)
    emit_existing_files "DASHI/Everything.agda"
    ;;
  merge-smoke|record)
    {
      emit_existing_files \
        "ActionMonotonicity.agda" \
        "DASHI_Tests.agda" \
        "JFixedPoint.agda" \
        "Moonshine.agda" \
        "MoonshineEarn.agda" \
        "SelfTrace.agda"
      emit_recursive_tree \
        "Kernel" \
        "Monster" \
        "Verification"
    } | awk '!seen[$0]++'
    ;;
  all)
    {
      "$0" authoritative
      "$0" merge-smoke
    } | awk '!seen[$0]++'
    ;;
  *)
    echo "usage: $0 [authoritative|merge-smoke|record|all]" >&2
    exit 2
    ;;
esac
