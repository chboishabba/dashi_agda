#!/usr/bin/env bash
# Local-only, fail-closed BH4 SG/PNP maximum-cut acceptance runner.
# No CI, Docker, remote services, synthetic source substitution or promotion.
set -euo pipefail
cd "$(dirname "$0")/.."
export DASHI_NO_TMUX=1

targets=(
  DASHI/Biology/Molecular/BH4OriginalSGPhysicalMaxCutCounterexamplesExact.agda
  DASHI/Biology/Molecular/BH4OriginalScharfetterGummelDissipationExact.agda
  DASHI/Biology/Molecular/BH4OriginalBishopSGComputedRHSExact.agda
  DASHI/Biology/KitzerowBH4EvidenceEverything.agda
)
for target in "${targets[@]}"; do
  printf '\n[AGDA PENDING -> CHECK] %s\n' "$target"
  bash scripts/run_agda29_parallel_check.sh "$target"
  printf '[AGDA LOCAL PASS] %s\n' "$target"
done
printf '\n[PYTEST LOCAL] SG/physical negative controls\n'
python -m pytest -q scripts/test_bh4_original_sg_physical_maxcut.py
printf '\n[LOCAL CHECKS PASS] Source-only SG modules and numerical regression.\n'
printf 'Original Rhea certificate, physical Poisson/SG weld, Brouwer,\n'
printf 'chemical detailed balance and total free energy remain separate gates.\n'
