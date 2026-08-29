#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
  DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
  DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
  DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
  DASHI/Physics/Foundations/BalabanCommonActionVariationValidation.agda
  DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
  DASHI/Physics/Foundations/EinsteinCommonActionVariationValidation.agda
  DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'
for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required QFT/GR file missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

qft=DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
gr=DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
cap=DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda

grep -q 'finiteStressShared' "$qft"
grep -q 'finiteVariationRepresentedByFiniteStress' "$qft"
grep -q 'finiteFirstVariationConverges' "$qft"
grep -q 'finiteStressPairingConvergesToLiteralContinuumStress' "$qft"
grep -q '^balabanSectorContinuumFirstVariationIsLiteralStressPairing :' "$qft"
grep -q '^balabanAggregateSectorVariationIsAggregateStressPairing :' "$qft"
grep -q 'aggregateStressPairingCommutes' "$qft"
grep -q 'finiteBalabanDensityVariationIsLiteralContinuumStressWithoutLimitIsFalse' "$qft"
grep -q 'measureContinuumLimitAloneCommutesWithMetricVariationIsFalse' "$qft"
grep -q 'tensorAggregationAutomaticallyCommutesWithMetricPairingIsFalse' "$qft"

grep -q 'effectiveSourceRepresentsCommonMetricVariation' "$gr"
grep -q 'commonMetricVariationEqualsEinsteinPairing' "$gr"
grep -q 'pairingSeparatesStressOnAdmittedDomain' "$gr"
grep -q '^commonVariationEqualsEinsteinTensor :' "$gr"
grep -q '^einsteinTensorVariationBuildsGRIdentification :' "$gr"
grep -q 'equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheoremIsFalse' "$gr"

grep -q '^record CommonMetricVariationLanguage' "$cap"
grep -q 'grPairingCommutes' "$cap"
grep -q 'qftPairingCommutes' "$cap"
grep -q 'commonAdmissibleImpliesGRAdmissible' "$cap"
grep -q 'commonAdmissibleImpliesQFTAdmissible' "$cap"
grep -q '^commonEinsteinAndBalabanVariationImpliesStressWeld :' "$cap"
grep -q '^stressWeldImpliesCommonMetricPairingEquality :' "$cap"
grep -q 'independentGRAndQFTMetricLanguagesAutomaticallyMeanSameVariationIsFalse' "$cap"

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda executable not available; static QFT/GR checks passed, kernel typecheck not run." >&2
  exit 2
fi

agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/BalabanCommonActionVariationValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/EinsteinCommonActionVariationValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/Everything.agda

echo "Finite-to-continuum Balaban-QFT, pairing-exact Einstein-GR, and common-metric weld checks passed."
