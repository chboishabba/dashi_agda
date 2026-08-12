#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_future_equivalence_frontier_round13.sh"
if [[ -x "$BASE_CHECKER" ]]; then
  "$BASE_CHECKER"
fi

FILES=(
  DASHI/Core/FutureQuotientResidualExact.agda
  DASHI/Cognition/PNF/RestrictedConstraintMetastabilityExact.agda
  DASHI/Cognition/PNF/SpokenTelescopeFutureEquivalenceExact.agda
  DASHI/Foundations/CantorCylinderMassExact.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'classAndResidualDetermineState' DASHI/Core/FutureQuotientResidualExact.agda
grep -q 'exactResidualIsRelevant' DASHI/Core/FutureQuotientResidualExact.agda

grep -q 'metastableIsOneStepLocalMinimum' DASHI/Cognition/PNF/RestrictedConstraintMetastabilityExact.agda
grep -q 'globalMinimumUnreachableFromMetastable' DASHI/Cognition/PNF/RestrictedConstraintMetastabilityExact.agda
grep -q 'canonicalRestrictedMetastability' DASHI/Cognition/PNF/RestrictedConstraintMetastabilityExact.agda

grep -q 'parsesAreNotFutureEquivalent' DASHI/Cognition/PNF/SpokenTelescopeFutureEquivalenceExact.agda
grep -q 'currentWhoSeenStillEqual' DASHI/Cognition/PNF/SpokenTelescopeFutureEquivalenceExact.agda

grep -q 'parentMassEqualsChildrenAtCommonScale' DASHI/Foundations/CantorCylinderMassExact.agda
grep -q 'polarLayerHasUnitMass' DASHI/Foundations/CantorCylinderMassExact.agda
grep -q 'polarDepthThreeStillEight' DASHI/Foundations/CantorCylinderMassExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed round-14 scan completed; no kernel-clean claim"
fi
