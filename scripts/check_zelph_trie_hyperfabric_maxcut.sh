#!/usr/bin/env bash
# Local, pinned Agda 2.9 acceptance root for DASHI's Zelph/Trie/Hyperformal
# mathematical source contracts.  Deliberately separate from physical-HF
# byte evidence, Cap'n Proto decoder refinement and SLR S29 acceptance.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if ! command -v git >/dev/null 2>&1; then
  echo "git required for exact-head source provenance" >&2
  exit 2
fi
HEAD="$(git rev-parse HEAD)"
printf '%s\n' "DASHI Zelph trie/hyperfabric kernel acceptance" "HEAD=$HEAD"

# A dirty worktree may be a legitimate local iteration, but cannot be
# mistaken for a verified GitHub PR head.
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "WARNING: tracked working tree differs from HEAD; result is NOT an exact-head receipt." >&2
fi

TARGETS=(
  DASHI/Core/TypedDependencyCore.agda
  DASHI/Core/AdmissibleReachability.agda
  DASHI/Core/FutureObservationLanguageQuotientExact.agda
  DASHI/Core/ReopenableConsumerInterventionKernelExact.agda
  DASHI/Core/QueryIndexedProjectionSpineAdapterExact.agda
  DASHI/Interop/ZelphBoundedGraphCoverageExact.agda
  DASHI/Interop/ZelphPhysicalShardQueryMaxCutExact.agda
)

for target in "${TARGETS[@]}"; do
  if [ ! -r "$target" ]; then
    echo "Missing required golden source: $target" >&2
    exit 2
  fi
done

# Reuse repository-pinned Nix/Agda/stdlib runner; run from the exact
# checkout, not a new ad hoc Agda environment. Avoid CI-only acceptance.
DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
  bash scripts/run_agda29_parallel_check.sh -- "${TARGETS[@]}"

echo "Agda kernel source check PASS at local checkout $HEAD"
echo "NOT VERIFIED BY THIS CHECK: HF object bytes, original graph partition,"
echo "Cap'n Proto decoder semantics, scoped closed-world answers, native P854,"
echo "SLR persisted review, external NORA export or Wikidata write authority."
