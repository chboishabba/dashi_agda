#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
  DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
  DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryValidation.agda
  DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
  DASHI/Physics/Foundations/CommonEffectiveActionVariationValidation.agda
  DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
  DASHI/Physics/Foundations/BalabanCommonActionVariationValidation.agda
  DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
  DASHI/Physics/Foundations/EinsteinCommonActionVariationValidation.agda
  DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required shared-source file missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^actualQFTSectorStressShared :' DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
grep -q 'qftStressAggregation' DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
grep -q 'qftTotalStressShared' DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
grep -q '^sharedSourceImpliesSameStressEnergy :' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
grep -q '^commonVariationImpliesStressWeld :' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda

grep -q '^record BalabanSectorFlow' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q '^record BalabanSectorMetricVariation' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q '^record BalabanAllSectorVariationReceipt' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q 'CommonAdmissibleMetricPerturbation' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q 'aggregateStressPairingCommutes' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q '^balabanAggregateSectorVariationIsAggregateStressPairing :' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q 'sectorSpecificMetricLanguagesAutomaticallyDefineOneGravitatingMetricIsFalse' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q 'tensorAggregationAutomaticallyCommutesWithMetricPairingIsFalse' DASHI/Physics/Foundations/BalabanCommonActionVariationFrontierExact.agda
grep -q '^balabanSectorFamilyProducesQFTIdentification :' DASHI/Physics/Foundations/BalabanCommonActionVariationValidation.agda

grep -q '^actualGRFieldEquation :' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
grep -q 'effectiveSourceRepresentsCommonMetricVariation' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
grep -q 'commonMetricVariationEqualsEinsteinPairing' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
grep -q 'pairingSeparatesStressOnAdmittedDomain' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
grep -q '^commonVariationEqualsEinsteinTensor :' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
grep -q '^einsteinTensorVariationBuildsGRIdentification :' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda
grep -q 'equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheoremIsFalse' DASHI/Physics/Foundations/EinsteinCommonActionVariationFrontierExact.agda

grep -q '^record CommonMetricVariationLanguage' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q 'grPairingCommutes' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q 'qftPairingCommutes' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q 'commonAdmissibleImpliesGRAdmissible' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q 'commonAdmissibleImpliesQFTAdmissible' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q '^commonEinsteinAndBalabanVariationImpliesStressWeld :' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q '^stressWeldImpliesCommonMetricPairingEquality :' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q 'independentGRAndQFTMetricLanguagesAutomaticallyMeanSameVariationIsFalse' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda
grep -q 'separateExtraStressWeldTheoremStillNeededAfterBothReceiptsIsFalse' DASHI/Physics/Foundations/CommonActionQFTGRVariationCompilerExact.agda

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda executable not available; static shared-source checks passed, kernel typecheck not run." >&2
  exit 2
fi

agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/CommonEffectiveActionVariationValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/BalabanCommonActionVariationValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/EinsteinCommonActionVariationValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/Everything.agda

echo "Shared-source, common-metric Balaban-QFT, pairing-exact Einstein-GR, and QFT/GR BIDI checks passed."
