#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -x scripts/check_crypto_blue_team_adversary_closure_round16.sh ]]; then
  scripts/check_crypto_blue_team_adversary_closure_round16.sh
fi

FILES=(
  DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
  DASHI/Crypto/MLKEMNTTPriorCutNoGoExact.agda
  DASHI/Crypto/MLKEMNTTParityBlockPriorExact.agda
  DASHI/Crypto/ObservationAcquisitionCostExact.agda
  DASHI/Crypto/KeyConfirmationObservationRefinementExact.agda
  DASHI/Crypto/MLKEMImplicitRejectProtocolObservationExact.agda
  DASHI/Crypto/MLKEMImplicitRejectTimingCompositionExact.agda
  DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
  DASHI/Crypto/BlueTeamSearchObservationRound17.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'algorithm9StageCount' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'zeroIndex128' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'sevenStageScalarDependencyWidth' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'quadraticCoordinateSeesWholePolynomial' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'mlKem1024QuadraticSourceWidth' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'constantComponentHasNoNontrivialDisconnectedCut' DASHI/Crypto/MLKEMNTTPriorCutNoGoExact.agda
grep -q 'linearComponentHasNoNontrivialDisconnectedCut' DASHI/Crypto/MLKEMNTTPriorCutNoGoExact.agda
grep -q 'targetPriorFactorsByParity' DASHI/Crypto/MLKEMNTTParityBlockPriorExact.agda
grep -q 'mlKem1024TwoParityBlocksCoverSecret' DASHI/Crypto/MLKEMNTTParityBlockPriorExact.agda
grep -q 'baseCaseOutput0UsesBoth' DASHI/Crypto/MLKEMNTTParityBlockPriorExact.agda
grep -q 'cheapLabObservationNetGain' DASHI/Crypto/ObservationAcquisitionCostExact.agda
grep -q 'expensiveLabObservationIsNetHarmful' DASHI/Crypto/ObservationAcquisitionCostExact.agda
grep -q 'confirmationSplitGivesHiddenDependentObservation' DASHI/Crypto/KeyConfirmationObservationRefinementExact.agda
grep -q 'afterConfirmationCount' DASHI/Crypto/KeyConfirmationObservationRefinementExact.agda
grep -q 'opaqueInternalRouteDifference' DASHI/Crypto/MLKEMImplicitRejectProtocolObservationExact.agda
grep -q 'opaqueInternalDifferenceCannotBecomeObservableSplit' DASHI/Crypto/MLKEMImplicitRejectProtocolObservationExact.agda
grep -q 'directRouteLeakIsHiddenDependent' DASHI/Crypto/MLKEMImplicitRejectProtocolObservationExact.agda
grep -q 'routeTimingIsHiddenDependent' DASHI/Crypto/MLKEMImplicitRejectTimingCompositionExact.agda
grep -q 'constantRouteHasNoTimingSplit' DASHI/Crypto/MLKEMImplicitRejectTimingCompositionExact.agda
grep -q '10.1007/3-540-68697-5_9' DASHI/Crypto/MLKEMImplicitRejectTimingCompositionExact.agda
grep -q 'labConfirmationIsHiddenDependent' DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
grep -q 'labConfirmationCost2NetGain' DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
grep -q 'labConfirmationCost6IsHarmful' DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q '10.6028/NIST.SP.800-227' DASHI/Crypto/KeyConfirmationObservationRefinementExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Crypto/BlueTeamSearchObservationRound17.agda
else
  echo "agda unavailable: structural/fail-closed round-17 scan completed; no kernel-clean claim"
fi
