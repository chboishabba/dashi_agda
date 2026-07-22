#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

mapfile -t cognition_files < <(
  find DASHI/Cognition -maxdepth 1 -type f \( -name '*.agda' -o -name '*.md' \) \
    | LC_ALL=C sort
)

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{-# TERMINATING #-\}|\{-# NON_TERMINATING #-\}|\?|TODO|FIXME' \
  "${cognition_files[@]}"; then
  echo "Cognition formalism placeholder audit failed." >&2
  exit 1
fi

scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/LanguagePhaseEverything.agda
