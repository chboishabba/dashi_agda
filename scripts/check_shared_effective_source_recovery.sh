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
grep -q '^sharedSourceControlImpliesCommonRegimeRecovery :' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
grep -q '^sharedSourceCrossSectorReceiptCompiles :' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
grep -q 'exactAggregationAndTwoFactorisationsProveWeldIsTrue' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
grep -q 'oneGaugeSectorStressEqualsTotalEinsteinSourceIsFalse' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
grep -q 'separateGRAndQFTSourceFitsProveSameObjectIsFalse' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryExact.agda
grep -q '^sharedSourceProducesStressWeld :' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryValidation.agda
grep -q '^sharedSourceProducesCommonRegime :' DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryValidation.agda

grep -q '^variationBuildsSharedEffectiveSource :' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
grep -q '^variationIdentifiesGRSource :' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
grep -q '^variationIdentifiesQFTSource :' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
grep -q '^commonVariationImpliesStressWeld :' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
grep -q 'finiteAdditiveNatActionDefinesMetricFunctionalDerivativeIsFalse' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
grep -q 'commonVariationPlusLiteralIdentificationsClosesStressWeldIsTrue' DASHI/Physics/Foundations/CommonEffectiveActionVariationExact.agda
grep -q '^variationIdentificationsCloseStressWeld :' DASHI/Physics/Foundations/CommonEffectiveActionVariationValidation.agda

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda executable not available; static shared-source checks passed, kernel typecheck not run." >&2
  exit 2
fi

agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/SharedEffectiveSourceRecoveryValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/CommonEffectiveActionVariationValidation.agda
agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Foundations/Everything.agda

echo "Shared effective-source, total-QFT-stress, and common-action-variation BIDI checks passed."
