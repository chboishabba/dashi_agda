#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_same_object_sharp_gain_round33.sh

files=(
  DASHI/Physics/Closure/NSTriadKNComplex3GalerkinEquationAudit.agda
  DASHI/Physics/Closure/NSTriadKNProjectedNonlinearityTransverseRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainL2Round34Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadSummableDyadicGainRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourierStrainHHBadRound34Validation.agda
)

doc=docs/ns-clay-contract/ns-fourier-strain-hhbad-round34.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round thirty-four contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNComplex3GalerkinEquationAudit.agda:integerEmbedding'
  'NSTriadKNComplex3GalerkinEquationAudit.agda:inverseSquare'
  'NSTriadKNComplex3GalerkinEquationAudit.agda:projectedOrderedTerm'
  'NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.agda:retainedModeNonzero'
  'NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact.agda:Coefficient.retainedModeNonzero'
  'NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.agda:reconstructedModeNonzero'
  'NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.agda:canonicalVelocityTransverseOnRetained'
  'NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.agda:canonicalPhysicalFiniteSystem'
  'NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.agda:canonicalSameCarrierSameObjectBuilder'
  'NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact.agda:cutoffSameObjectFamilyConstructedForRawStateCarrier = false'
  'NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda:partitionTriads'
  'NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda:safeFullCutoffCanonicalTriadOrbitEnumeration'
  'NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda:safeCanonicalTriadOrbitQuotientClosed = true'
  'NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda:literalComplexThreeLegEnergyTransferConstructed = false'
  'NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda:fourierStrainTraceFree'
  'NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda:stretchingQuadraticFactorization'
  'NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda:fourierStrainOwnModeActionVanishes'
  'NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda:fourierStrainFrobeniusTransverseExact'
  'NSTriadKNPeriodicFourierStrainL2Round34Exact.agda:finitePeriodicStrainL2Exact'
  'NSTriadKNHHBadSummableDyadicGainRound34Exact.agda:requiredGainPrefixClosedForm'
  'NSTriadKNHHBadSummableDyadicGainRound34Exact.agda:requiredGainPrefixPlusTail'
  'NSTriadKNHHBadSummableDyadicGainRound34Exact.agda:physicalHHBadGainProfileProduced = false'
  'NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda:criticalTargetTimesRawRatio'
  'NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda:criticalDissipationAbsorbsRawHHBadRatio'
  'NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda:criticalDissipationControlsPhysicalHHBadGain'
  'NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda:physicalLuoCriticalDissipationEstimateConstructed = false'
  'NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda:physicalHHBadGainToLuoDissipationLinkConstructed = false'
  'NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda:cotlarSymmetricMassClosedForm'
  'NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda:directRadiusBudgetPlusTailExact'
  'NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda:quarterSymmetricMassClosedForm'
  'NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda:quarterSymmetricMassPlusTail'
  'NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda:rootEnvelopeSquaresToProductEnvelope'
  'NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda:physicalTwoSidedComPairDecayConstructed = false'
  'NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact.agda:bishopBilinearAtomDifferenceFactorisation'
  'NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact.agda:bishopFiniteGalerkinDifferenceFactorisation'
  'NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact.agda:physicalBishopCoordinateEquivalenceConstructed = false'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

# Provenance markers on genuinely imported mathematics.
grep -q '10.1007/BF02547354' \
  DASHI/Physics/Closure/NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda
grep -q '10.7208/chicago/9780226115498.001.0001' \
  DASHI/Physics/Closure/NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact.agda
grep -q '10.1080/03605309608821197' \
  DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda
grep -q '10.1007/BF01240221' \
  DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainMultiplierRound34Exact.agda
grep -q '10.1007/s00021-019-0411-z' \
  DASHI/Physics/Closure/NSTriadKNHHBadSummableDyadicGainRound34Exact.agda
grep -q '10.1007/s00021-019-0411-z' \
  DASHI/Physics/Closure/NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact.agda
grep -q '10.1002/cpa.3160410704' \
  DASHI/Physics/Closure/NSTriadKNComCotlarDyadicEnvelopeRound34Exact.agda
grep -q '10.1007/978-3-642-61667-9' \
  DASHI/Physics/Closure/NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact.agda
grep -q '10.48550/arXiv.2205.08354' \
  DASHI/Physics/Closure/NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact.agda

grep -q 'does \*\*not\*\* add a terminal Clay wrapper' "$doc"
grep -q 'total target mass is exactly' "$doc"
grep -q 'limiting cutoff-independent mass `3C`' "$doc"
grep -q 'rational physical trajectory' "$doc"
grep -q 'termination pragma' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoFourierStrainHHBadRound34Validation.agda
