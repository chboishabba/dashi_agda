#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ATLAS=DASHI/Education/DigitalESDPrimarySourceMethodologyAtlasExact.agda
OWNER=DASHI/Education/DigitalESDManuscriptMethodologyExact.agda
REGRESSION=DASHI/Education/DigitalESDManuscriptMethodologyRegression.agda
DERIVATION=DASHI/Education/DigitalESDTransferablePrincipleDerivationMethodExact.agda
PRINCIPLES=DASHI/Education/DigitalESDTransferablePedagogicalPrinciplesExact.agda
MATRIX=DASHI/Education/DigitalESDTransformativePrincipleMatrixExact.agda
DRAFT=docs/digital-esd-integrative-review-draft.md

for file in "$ATLAS" "$OWNER" "$REGRESSION" "$DERIVATION" "$PRINCIPLES" "$MATRIX" "$DRAFT"; do
  [[ -f "$file" ]] || { echo "required manuscript-methodology source is missing: $file" >&2; exit 1; }
done

for file in "$ATLAS" "$OWNER" "$REGRESSION" "$DERIVATION" "$PRINCIPLES" "$MATRIX"; do
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
grep -q '^regionalImplementationReportsDoNotCreateDigitalESDEffect :' "$ATLAS"
grep -q '^canonicalPrimarySourceMethodologyBoundary :' "$ATLAS"

grep -q '^researchQuestionCount : Nat' "$OWNER"
grep -q '^canonicalIntegrativeReviewStages :' "$OWNER"
grep -q '^canonicalEligibilityPolicy :' "$OWNER"
grep -q '^canonicalExtractionSchema :' "$OWNER"
grep -q '^record SynthesisCell :' "$OWNER"
grep -q '^principleDerivationBoundary :' "$OWNER"
grep -q '^uneceFifthESDEvaluationReceipt :' "$OWNER"
grep -q '^regionalImplementationReportsDoNotCreateDigitalESDEffect :' "$OWNER"
grep -q '^activityDoesNotDetermineSystemTransformation :' "$OWNER"
grep -q '^taskPerformanceDoesNotDetermineLearning :' "$OWNER"
grep -q '^searchClosureDoesNotEqualEvidenceSynthesis :' "$OWNER"
grep -q '^canonicalMethodologyBoundary :' "$OWNER"

grep -q '^paperTypeRegression :' "$REGRESSION"
grep -q '^researchQuestionCountRegression :' "$REGRESSION"
grep -q '^methodRetainsStructuredSearchRegression :' "$REGRESSION"
grep -q '^methodRetainsPrincipleDerivationRegression :' "$REGRESSION"
grep -q '^preSearchFrameworkNotReviewResultRegression :' "$REGRESSION"
grep -q '^uneceFifthEvaluationReceiptRegression :' "$REGRESSION"
grep -q '^regionalReportsDoNotCreateDigitalESDEffectRegression :' "$REGRESSION"
grep -q '^systemTransformationNotActivityRegression :' "$REGRESSION"
grep -q '^performanceNotLearningRegression :' "$REGRESSION"
grep -q '^paperMethodologyDoesNotPromoteSystematicReviewRegression :' "$REGRESSION"

grep -q '^principleDerivationStageCount : Nat' "$DERIVATION"
grep -q 'candidatePrincipleGenerationMayPrecedeSearchClosure' "$DERIVATION"
grep -q 'finalPrinciplePromotionBeforeSearchClosureIsFalse' "$DERIVATION"
grep -q '^transferablePrincipleCount : Nat' "$PRINCIPLES"
grep -q '^transformativePrincipleMatrixRowCount : Nat' "$MATRIX"
grep -q 'professionalDevelopmentCondition' "$MATRIX"

grep -q '^## 4. Methods$' "$DRAFT"
grep -q '^### 4.2 Candidate principle derivation$' "$DRAFT"
grep -q '^### 4.3 Information sources$' "$DRAFT"
grep -q '^### 4.4 Search strategy$' "$DRAFT"
grep -q '^### 4.5 Eligibility principles$' "$DRAFT"
grep -q '^### 4.7 Data extraction$' "$DRAFT"
grep -q '^### 4.8 Synthesis and framework challenge$' "$DRAFT"
grep -q '^## 5. Candidate transformative-principle matrix$' "$DRAFT"
grep -q '^## 7. Candidate contribution positioning$' "$DRAFT"
grep -q 'seven provisional transferable principles' "$DRAFT"
grep -q 'professional development' "$DRAFT"
grep -q 'pre-search candidate framework' "$DRAFT"
grep -q 'declared Scopus, Web of Science, ERIC, ACM Digital Library and IEEE Xplore searches have not yet been executed' "$DRAFT"
grep -q '10.1057/s41599-026-06845-5' "$DRAFT"
grep -q '10.3390/educsci16050721' "$DRAFT"
grep -q '10.3390/su18157979' "$DRAFT"

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
