#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ATLAS=DASHI/Education/DigitalESDPrimarySourceMethodologyAtlasExact.agda
OWNER=DASHI/Education/DigitalESDManuscriptMethodologyExact.agda
REGRESSION=DASHI/Education/DigitalESDManuscriptMethodologyRegression.agda
DRAFT=docs/digital-esd-integrative-review-draft.md

for file in "$ATLAS" "$OWNER" "$REGRESSION" "$DRAFT"; do
  [[ -f "$file" ]] || { echo "required manuscript-methodology source is missing: $file" >&2; exit 1; }
done

for file in "$ATLAS" "$OWNER" "$REGRESSION"; do
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'Education for sustainable development: a roadmap' "$ATLAS"
grep -q 'Mid-term evaluation of the ESD for 2030 framework, 2021-2024' "$ATLAS"
grep -q '10.1787/062a7394-en' "$ATLAS"
grep -q 'Fifth evaluation report of the Strategy for Education for Sustainable Development' "$ATLAS"
grep -q 'Ministerial Statement: Sustaining education as a common good in the age of AI' "$ATLAS"
grep -q 'Sustaining education as a common good in the age of AI: The case for deliberative governance' "$ATLAS"
grep -q 'AI procurement in education: the missing lever in AI governance' "$ATLAS"
grep -q 'Beyond the price tag: Rethinking total cost of ownership for AI in education systems' "$ATLAS"
grep -q '^primaryMethodologySourceAtlas :' "$ATLAS"
grep -q '^uneceFifthESDEvaluationSourceRoleReceipt :' "$ATLAS"
grep -q '^unescoAICommonGoodMinisterialSourceRoleReceipt :' "$ATLAS"
grep -q '^unescoAICommonGoodDiscussionSourceRoleReceipt :' "$ATLAS"
grep -q '^unescoAIProcurementBackgroundSourceRoleReceipt :' "$ATLAS"
grep -q '^unescoAITCOBackgroundSourceRoleReceipt :' "$ATLAS"
grep -q '^regionalImplementationReportsDoNotCreateDigitalESDEffect :' "$ATLAS"
grep -q '^consultationBackgroundDoesNotCreateAdoptedPolicy :' "$ATLAS"
grep -q '^canonicalPrimarySourceMethodologyBoundary :' "$ATLAS"

grep -q '^researchQuestionCount : Nat' "$OWNER"
grep -q '^canonicalIntegrativeReviewStages :' "$OWNER"
grep -q '^canonicalEligibilityPolicy :' "$OWNER"
grep -q '^canonicalExtractionSchema :' "$OWNER"
grep -q '^record SynthesisCell :' "$OWNER"
grep -q '^unescoESD2030RoadmapReceipt :' "$OWNER"
grep -q '^unescoESD2030MidtermReceipt :' "$OWNER"
grep -q '^oecdDigitalEducationOutlook2026Receipt :' "$OWNER"
grep -q '^uneceFifthESDEvaluationReceipt :' "$OWNER"
grep -q '^unescoAICommonGoodMinisterialReceipt :' "$OWNER"
grep -q '^unescoAIConsultationDiscussionReceipt :' "$OWNER"
grep -q '^unescoAIProcurementBackgroundReceipt :' "$OWNER"
grep -q '^unescoAITCOBackgroundReceipt :' "$OWNER"
grep -q '^consultationDiscussionPaperDoesNotEqualAdoptedMinisterialStatement :' "$OWNER"
grep -q '^consultationBackgroundPaperDoesNotEqualAdoptedPolicy :' "$OWNER"
grep -q '^regionalImplementationReportsDoNotCreateDigitalESDEffect :' "$OWNER"
grep -q '^activityDoesNotDetermineSystemTransformation :' "$OWNER"
grep -q '^taskPerformanceDoesNotDetermineLearning :' "$OWNER"
grep -q '^searchClosureDoesNotEqualEvidenceSynthesis :' "$OWNER"
grep -q '^canonicalMethodologyBoundary :' "$OWNER"

grep -q '^paperTypeRegression :' "$REGRESSION"
grep -q '^researchQuestionCountRegression :' "$REGRESSION"
grep -q '^methodRetainsStructuredSearchRegression :' "$REGRESSION"
grep -q '^unescoMidtermReceiptRegression :' "$REGRESSION"
grep -q '^oecdOutlookReceiptRegression :' "$REGRESSION"
grep -q '^uneceFifthEvaluationReceiptRegression :' "$REGRESSION"
grep -q '^unescoAICommonGoodMinisterialReceiptRegression :' "$REGRESSION"
grep -q '^unescoAIConsultationDiscussionReceiptRegression :' "$REGRESSION"
grep -q '^unescoAIProcurementBackgroundReceiptRegression :' "$REGRESSION"
grep -q '^unescoAITCOBackgroundReceiptRegression :' "$REGRESSION"
grep -q '^consultationDoesNotEqualAdoptedStatementRegression :' "$REGRESSION"
grep -q '^backgroundPaperDoesNotEqualAdoptedPolicyRegression :' "$REGRESSION"
grep -q '^regionalReportsDoNotCreateDigitalESDEffectRegression :' "$REGRESSION"
grep -q '^systemTransformationNotActivityRegression :' "$REGRESSION"
grep -q '^performanceNotLearningRegression :' "$REGRESSION"
grep -q '^paperMethodologyDoesNotPromoteSystematicReviewRegression :' "$REGRESSION"

grep -q '^## 4. Methods$' "$DRAFT"
grep -q '^### 4.3 Search strategy$' "$DRAFT"
grep -q '^### 4.4 Eligibility principles$' "$DRAFT"
grep -q '^### 4.6 Data extraction$' "$DRAFT"
grep -q '^### 4.7 Synthesis$' "$DRAFT"
grep -q 'Ministerial Statement: Sustaining education as a common good in the age of AI' "$DRAFT"
grep -q 'database searches, deduplication, eligibility screening and structured extraction remain unexecuted' "$DRAFT"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "digital ESD manuscript methodology source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
