#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -x scripts/check_crypto_local_constraint_search_round15.sh ]]; then
  scripts/check_crypto_local_constraint_search_round15.sh
fi

FILES=(
  DASHI/Crypto/BlueTeamAdversaryObservationExact.agda
  DASHI/Crypto/BlueTeamThreatModelExact.agda
  DASHI/Crypto/ComputationalCandidateFibreExact.agda
  DASHI/Crypto/FiniteCandidateFibreCardinalityExact.agda
  DASHI/Crypto/TranscriptProtectedLabelExact.agda
  DASHI/Crypto/IndexedSearchCostExact.agda
  DASHI/Crypto/FiniteSecurityGameBoundaryExact.agda
  DASHI/Crypto/FiniteAdvantageAccountingExact.agda
  DASHI/Crypto/PriorScoreSearchFactorisationExact.agda
  DASHI/Crypto/PublicFactoredObservationTraceInvariantExact.agda
  DASHI/Crypto/AlgorithmRelativeRecoveryCostExact.agda
  DASHI/Crypto/FiniteMLWEVectorLabExact.agda
  DASHI/Crypto/FiniteMLWEGameRegressionExact.agda
  DASHI/Crypto/FiniteMLWEPriorScoreSearchRegressionExact.agda
  DASHI/Crypto/MLKEMFIPS203SourceExact.agda
  DASHI/Crypto/MLKEMFIPS203SearchGeometryExact.agda
  DASHI/Crypto/MLKEMNTTLocalPriorCouplingExact.agda
  DASHI/Crypto/BlueTeamAdversaryClosureRound16.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'publicFactoredCannotSplitSamePublicFibre' DASHI/Crypto/BlueTeamAdversaryObservationExact.agda
grep -q 'publicProtectedLabelSplitRefutesExactRecovery' DASHI/Crypto/BlueTeamThreatModelExact.agda
grep -q 'publicFactoredThreatObservationCannotSplit' DASHI/Crypto/BlueTeamThreatModelExact.agda
grep -q 'candidateRefinementCannotIncrease' DASHI/Crypto/BlueTeamThreatModelExact.agda
grep -q 'injectiveFibreHasUniqueCandidate' DASHI/Crypto/ComputationalCandidateFibreExact.agda
grep -q 'CandidateFalsePositive' DASHI/Crypto/ComputationalCandidateFibreExact.agda
grep -q 'injectiveImpliesEfficientInverseIsFalse' DASHI/Crypto/ComputationalCandidateFibreExact.agda
grep -q 'refinementCannotIncreaseCardinality' DASHI/Crypto/FiniteCandidateFibreCardinalityExact.agda
grep -q 'canonicalTwoToOneShrink' DASHI/Crypto/FiniteCandidateFibreCardinalityExact.agda
grep -q 'transcriptLabelSplitRefutesExactRecovery' DASHI/Crypto/TranscriptProtectedLabelExact.agda
grep -q 'factorisationGivesExactTranscriptRecovery' DASHI/Crypto/TranscriptProtectedLabelExact.agda
grep -q 'indexedCartesianSearchCost' DASHI/Crypto/IndexedSearchCostExact.agda
grep -q 'indexedFunctionalSearchCost' DASHI/Crypto/IndexedSearchCostExact.agda
grep -q 'exactRecoveryYieldsPerfectDistinguisher' DASHI/Crypto/FiniteSecurityGameBoundaryExact.agda
grep -q 'collisionRefutesExactRecovery' DASHI/Crypto/FiniteSecurityGameBoundaryExact.agda
grep -q 'perfectTwoTrialsGain' DASHI/Crypto/FiniteAdvantageAccountingExact.agda
grep -q 'crossedLocalsCannotReconcile' DASHI/Crypto/PriorScoreSearchFactorisationExact.agda
grep -q 'scoreFactorisationImpliesCheapSearchIsFalse' DASHI/Crypto/PriorScoreSearchFactorisationExact.agda
grep -q 'samePublicSameTrace' DASHI/Crypto/PublicFactoredObservationTraceInvariantExact.agda
grep -q 'samePublicSameAdaptiveTwoRoundTranscript' DASHI/Crypto/PublicFactoredObservationTraceInvariantExact.agda
grep -q 'candidateShrinkButCostRises' DASHI/Crypto/AlgorithmRelativeRecoveryCostExact.agda
grep -q 'algorithmRelativeInformationGain' DASHI/Crypto/AlgorithmRelativeRecoveryCostExact.agda
grep -q 'public22CandidateCount' DASHI/Crypto/FiniteMLWEVectorLabExact.agda
grep -q 'afterFirstBitFalseCount' DASHI/Crypto/FiniteMLWEVectorLabExact.agda
grep -q 'noExactSecretRecoveryFromPublic22' DASHI/Crypto/FiniteMLWEVectorLabExact.agda
grep -q 'publicObservationCannotExactlyRecoverProtectedBit' DASHI/Crypto/FiniteMLWEGameRegressionExact.agda
grep -q 'scoreDecomposesByRows' DASHI/Crypto/FiniteMLWEPriorScoreSearchRegressionExact.agda
grep -q 'zeroScoreDoesNotIdentifyUniqueSecret' DASHI/Crypto/FiniteMLWEPriorScoreSearchRegressionExact.agda
grep -q 'labObservationSearchCostDrop' DASHI/Crypto/FiniteMLWEPriorScoreSearchRegressionExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMFIPS203SourceExact.agda
grep -q 'params512CiphertextBytes' DASHI/Crypto/MLKEMFIPS203SourceExact.agda
grep -q 'params768CiphertextBytes' DASHI/Crypto/MLKEMFIPS203SourceExact.agda
grep -q 'params1024CiphertextBytes' DASHI/Crypto/MLKEMFIPS203SourceExact.agda
grep -q 'mismatchingCiphertextUsesFallback' DASHI/Crypto/MLKEMFIPS203SourceExact.agda
grep -q 'canonicalFIPS203BlueTeamBoundary' DASHI/Crypto/MLKEMFIPS203SourceExact.agda
grep -q 'secret512CoefficientCount' DASHI/Crypto/MLKEMFIPS203SearchGeometryExact.agda
grep -q 'secret512SupportWidth' DASHI/Crypto/MLKEMFIPS203SearchGeometryExact.agda
grep -q 'ciphertext1024Bits' DASHI/Crypto/MLKEMFIPS203SearchGeometryExact.agda
grep -q 'matrixCouplingMustBeReconciledIsTrue' DASHI/Crypto/MLKEMFIPS203SearchGeometryExact.agda
grep -q 'nttQuadraticCoordinateCount' DASHI/Crypto/MLKEMNTTLocalPriorCouplingExact.agda
grep -q 'crossedLocalsFailReconciliation' DASHI/Crypto/MLKEMNTTLocalPriorCouplingExact.agda
grep -q 'localAlgebraAloneCollapsesSearchIsFalse' DASHI/Crypto/MLKEMNTTLocalPriorCouplingExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Crypto/BlueTeamAdversaryClosureRound16.agda
else
  echo "agda unavailable: structural/fail-closed round-16 scan completed; no kernel-clean claim"
fi
