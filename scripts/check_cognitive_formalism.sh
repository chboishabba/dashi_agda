#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

mapfile -t cognition_files < <(
  find DASHI/Cognition -maxdepth 1 -type f -name '*.agda' -print | sort
)

if [ "${#cognition_files[@]}" -eq 0 ]; then
  echo "No cognition modules found for placeholder audit." >&2
  exit 1
fi

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{-# TERMINATING #-\}|\{-# NON_TERMINATING #-\}|TODO|FIXME' \
  "${cognition_files[@]}"; then
  echo "Cognition formalism placeholder audit failed." >&2
  exit 1
fi

export DASHI_REPO_ROOT="$repo_root"
if [ -z "${AGDA_BIN:-}" ] && command -v agda >/dev/null 2>&1; then
  export AGDA_BIN="$(command -v agda)"
fi

scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/LanguagePhaseEverything.agda
