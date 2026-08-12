#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_future_residual_cantor_metastability_round14.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Cognition/PNF/NarrativeClaimProvenanceExact.agda
  DASHI/Cognition/PNF/NarrativeConflictStateExact.agda
  DASHI/Cognition/PNF/DissTrackNarrativeDynamicsExact.agda
  DASHI/Cognition/PNF/ConsumerIndexedNarrativeProjectionExact.agda
  DASHI/Cognition/PNF/NarrativeMDLReplicationExact.agda
  DASHI/Cognition/PNF/NarrativeAmplificationWithoutEvidencePromotionExact.agda
  DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'replicationDoesNotCreateIndependentEvidence' DASHI/Cognition/PNF/NarrativeClaimProvenanceExact.agda
grep -q 'signalReplicationRaisesSalience' DASHI/Cognition/PNF/NarrativeClaimProvenanceExact.agda
grep -q 'rhetoricalUpdatePreservesFact' DASHI/Cognition/PNF/NarrativeClaimProvenanceExact.agda

grep -q 'audienceUpdatePreservesResidual' DASHI/Cognition/PNF/NarrativeConflictStateExact.agda
grep -q 'sameProjectionDoesNotChooseReconstruction' DASHI/Cognition/PNF/NarrativeConflictStateExact.agda
grep -q 'VerifiedReconstruction' DASHI/Cognition/PNF/NarrativeConflictStateExact.agda

grep -q 'familyToMeet' DASHI/Cognition/PNF/DissTrackNarrativeDynamicsExact.agda
grep -q 'phaseCaptureChangesPublicState' DASHI/Cognition/PNF/DissTrackNarrativeDynamicsExact.agda
grep -q 'orderChangesOutcome' DASHI/Cognition/PNF/DissTrackNarrativeDynamicsExact.agda

grep -q 'nonActionableOpinionDoesNotSettleSupported' DASHI/Cognition/PNF/ConsumerIndexedNarrativeProjectionExact.agda
grep -q 'notLikeUsParallelState' DASHI/Cognition/PNF/ConsumerIndexedNarrativeProjectionExact.agda

grep -q 'anthemFitsBroadcastBudget' DASHI/Cognition/PNF/NarrativeMDLReplicationExact.agda
grep -q 'reopeningDoesNotFitSameBudget' DASHI/Cognition/PNF/NarrativeMDLReplicationExact.agda
grep -q 'shorterDoesNotProveSupported' DASHI/Cognition/PNF/NarrativeMDLReplicationExact.agda

grep -q 'canonicalAmplificationSeparation' DASHI/Cognition/PNF/NarrativeAmplificationWithoutEvidencePromotionExact.agda
grep -q 'amplificationPreservesFact' DASHI/Cognition/PNF/NarrativeAmplificationWithoutEvidencePromotionExact.agda

grep -q 'coarseBoundaryCannotDetermineAllActions' DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda
grep -q 'threatenedIsNotActual' DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda
grep -q 'wideningPreservesProvenance' DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed round-15 scan completed; no kernel-clean claim"
fi
