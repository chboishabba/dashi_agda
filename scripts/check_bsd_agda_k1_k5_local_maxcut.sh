#!/usr/bin/env bash
# Agda-golden local-only BSD cut. No CI, Docker or trust in status flags.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Mathematics/Arithmetic/EllipticSupportedSquareClassSieveExact.agda
  DASHI/Mathematics/Arithmetic/EllipticRationalPlaceTwoDescentProducerExact.agda
  DASHI/Mathematics/Automorphic/EllipticSelectedHeckePrimePowerExact.agda
)

for f in "${files[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "BLOCKED: missing $f" >&2
    exit 11
  fi
  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check' "$f"; then
    echo "BLOCKED: non-golden or unfinished declaration in $f" >&2
    exit 13
  fi
done

if ! command -v agda >/dev/null 2>&1; then
  echo 'BLOCKED: Agda executable unavailable; source-written is NOT kernel accepted.' >&2
  exit 12
fi

# Use the repository's own Agda 2.9 pinned parallel checker and
# dependency/library arguments; do not infer authority from CI.
bash scripts/run_agda29_parallel_check.sh "${files[@]}"

echo 'Agda local checker completed; retain actual receipt/logs and module hashes.'
echo 'This checks finite sieve and prime-power recurrence, NOT actual H¹/Sha/BSD.'
