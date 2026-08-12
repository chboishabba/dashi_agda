#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_terminalisation_provenance_symmetry_round10.sh"
if [[ -x "$BASE_CHECKER" ]]; then
  "$BASE_CHECKER"
fi

FILES=(
  DASHI/Core/RecoverableQuotientCompositionExact.agda
  DASHI/Core/MinimalDynamicResidualExact.agda
  DASHI/Core/ApproximateMDLResidualBudgetExact.agda
  DASHI/Cognition/PNF/ConstraintPhaseFrustrationExact.agda
  DASHI/Cognition/PNF/IndependentWheelMemoryGradeExact.agda
  DASHI/Cognition/PNF/PhasedRelationalLatticeExact.agda
  DASHI/Foundations/CantorUnitMassDynamicBridgeExact.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'composeRecoverable' DASHI/Core/RecoverableQuotientCompositionExact.agda
grep -q 'compositeResidualIsProduct' DASHI/Core/RecoverableQuotientCompositionExact.agda
grep -q 'phaseReceiptReopensExactly' DASHI/Core/MinimalDynamicResidualExact.agda
grep -q 'hiddenPhaseMinimalResidual' DASHI/Core/MinimalDynamicResidualExact.agda
grep -q 'arXiv:2606.04834v1' DASHI/Core/ApproximateMDLResidualBudgetExact.agda
grep -q 'costTwoDoesNotFitFixedUnit' DASHI/Core/ApproximateMDLResidualBudgetExact.agda
grep -q 'asynchronousNextPhaseHasZeroConstraintCost' DASHI/Cognition/PNF/ConstraintPhaseFrustrationExact.agda
grep -q 'sameAndNextCannotBothHold' DASHI/Cognition/PNF/ConstraintPhaseFrustrationExact.agda
grep -q 'attachPreservesLegacyMemoryPhase' DASHI/Cognition/PNF/IndependentWheelMemoryGradeExact.agda
grep -q 'OptionalPhaseAlignment' DASHI/Cognition/PNF/IndependentWheelMemoryGradeExact.agda
grep -q 'semanticPhaseDerived' DASHI/Cognition/PNF/PhasedRelationalLatticeExact.agda
grep -q 'horizonExpansionCommutesWithProcessAdvance' DASHI/Cognition/PNF/PhasedRelationalLatticeExact.agda
grep -q 'toConsumerSafeCompression' DASHI/Foundations/CantorUnitMassDynamicBridgeExact.agda
grep -q 'unitTaskMassClaimsWorldTruthIsFalse' DASHI/Foundations/CantorUnitMassDynamicBridgeExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed round-11 scan completed; no kernel-clean claim"
fi
