#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -x scripts/check_future_residual_cantor_metastability_round14.sh ]]; then
  scripts/check_future_residual_cantor_metastability_round14.sh
elif [[ -x scripts/check_crypto_topten_blue_team_round12.sh ]]; then
  scripts/check_crypto_topten_blue_team_round12.sh
fi

FILES=(
  DASHI/Crypto/ResidualConstraintDecompositionExact.agda
  DASHI/Crypto/TransformLocalFibreGeometryExact.agda
  DASHI/Crypto/ConstraintCouplingSearchExact.agda
  DASHI/Crypto/SearchFactorisationExact.agda
  DASHI/Crypto/AdaptiveFibreShrinkExact.agda
  DASHI/Crypto/ThresholdPartitionGeometryExact.agda
  DASHI/Crypto/TimingObservationSideChannelExact.agda
  DASHI/Crypto/MLKEMLocalSearchGeometryExact.agda
  DASHI/Crypto/TopTenSearchGeometryControlsExact.agda
  DASHI/Crypto/CryptoLocalConstraintSearchRound15.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'globalPlausibleIffIndexed' DASHI/Crypto/ResidualConstraintDecompositionExact.agda
grep -q 'indexedGlobalImpliesEveryLocal' DASHI/Crypto/ResidualConstraintDecompositionExact.agda
grep -q 'globalPlausibleIffLocal' DASHI/Crypto/ResidualConstraintDecompositionExact.agda
grep -q 'globalScoreIsLocalPlusCoupling' DASHI/Crypto/ResidualConstraintDecompositionExact.agda
grep -q 'localTestabilityDoesNotGiveIndependentSolvability' DASHI/Crypto/ResidualConstraintDecompositionExact.agda
grep -q 'exactTransformPreservesDistinctness' DASHI/Crypto/TransformLocalFibreGeometryExact.agda
grep -q 'ConstraintCouplingGraph' DASHI/Crypto/ConstraintCouplingSearchExact.agda
grep -q 'disconnectedSearchFactors' DASHI/Crypto/ConstraintCouplingSearchExact.agda
grep -q 'connectedConstraintHasEasyWitness' DASHI/Crypto/ConstraintCouplingSearchExact.agda
grep -q 'separatorDPBound' DASHI/Crypto/ConstraintCouplingSearchExact.agda
grep -q 'reconciledLocalSolutionsGiveGlobal' DASHI/Crypto/SearchFactorisationExact.agda
grep -q 'genericReconciliationBound' DASHI/Crypto/SearchFactorisationExact.agda
grep -q 'functionalReconciliationBound' DASHI/Crypto/SearchFactorisationExact.agda
grep -q 'strictRefinementFromSplit' DASHI/Crypto/AdaptiveFibreShrinkExact.agda
grep -q 'oneSplitShrinksTwoToOne' DASHI/Crypto/AdaptiveFibreShrinkExact.agda
grep -q 'StrictShrinkChain' DASHI/Crypto/AdaptiveFibreShrinkExact.agda
grep -q 'twoStepShrinkChain' DASHI/Crypto/AdaptiveFibreShrinkExact.agda
grep -q 'twoLossyBitsJointlyRecover' DASHI/Crypto/ThresholdPartitionGeometryExact.agda
grep -q 'timingSplitRefutesFibreConstant' DASHI/Crypto/TimingObservationSideChannelExact.agda
grep -q 'timingSplitGivesObservationSplit' DASHI/Crypto/TimingObservationSideChannelExact.agda
grep -q 'timingFactorisationRevealsOutcome' DASHI/Crypto/TimingObservationSideChannelExact.agda
grep -q '10.1007/3-540-68697-5_9' DASHI/Crypto/TimingObservationSideChannelExact.agda
grep -q 'collapseCertificateGivesCandidateSearch' DASHI/Crypto/MLKEMLocalSearchGeometryExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMLocalSearchGeometryExact.agda
grep -q 'allSearchControlsCount' DASHI/Crypto/TopTenSearchGeometryControlsExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
else
  echo "agda unavailable: structural/fail-closed round-15 scan completed; no kernel-clean claim"
fi
