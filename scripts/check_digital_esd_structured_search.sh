#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDStructuredSearchExact.agda
REGRESSION=DASHI/Education/DigitalESDStructuredSearchRegression.agda
PAYMENT_ADAPTER=DASHI/Education/DigitalESDManuscriptDependencyPaymentAdapterExact.agda

for file in "$OWNER" "$REGRESSION" "$PAYMENT_ADAPTER"; do
  [[ -f "$file" ]] || { echo "required structured-search source is missing: $file" >&2; exit 1; }
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '10.1186/s13643-020-01542-z' "$OWNER"
grep -q '10.1016/j.jclinepi.2016.01.021' "$OWNER"
grep -q '^canonicalSearchQueryFamilies :' "$OWNER"
grep -q '^canonicalObservedOpenWebSearches :' "$OWNER"
grep -q '^canonicalStructuredSearchLedger :' "$OWNER"
grep -q '^openWebSnowballDoesNotCloseTransparentStructuredSearch :' "$OWNER"
grep -q '^searchMethodCitationDoesNotPromoteSystematicReview :' "$OWNER"
grep -q '^plannedDatabaseDoesNotCreateExecutionReceipt :' "$OWNER"
grep -q '^searchHitDoesNotCreateIncludedStudy :' "$OWNER"
grep -q '^searchResultSnippetDoesNotPayFullSourceClaim :' "$OWNER"
grep -q '^unobservedDatabaseDoesNotCloseStructuredSearch :' "$OWNER"
grep -q '^structuredSearchClosureDoesNotPayEvidenceSynthesis :' "$OWNER"

# Same-object search execution lineage: database exports -> dedup -> screening
# -> extraction -> closure. There is deliberately no canonical closed receipt.
grep -q '^record DatabaseExecutionReceipt (searchSurface : SearchSurface)' "$OWNER"
grep -q '^record DeduplicationReceipt' "$OWNER"
grep -q '^record EligibilityScreeningReceipt' "$OWNER"
grep -q '^record StructuredExtractionReceipt' "$OWNER"
grep -q '^record TransparentStructuredSearchClosureReceipt :' "$OWNER"
grep -q '^closeTransparentStructuredSearch :' "$OWNER"
grep -q 'sourceRoleAndExecutionLineageRetained' "$OWNER"

# Manuscript dependency/payment adapter must reuse the repository-wide typed
# provenance graph and canonical assessment/feedback loop. Acquisition order
# remains free; required downstream payment cannot residualize away search.
grep -q 'import DASHI.Core.TypedProvenanceDependencyGraphExact as Provenance' "$PAYMENT_ADAPTER"
grep -q 'import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback' "$PAYMENT_ADAPTER"
grep -q 'import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment' "$PAYMENT_ADAPTER"
grep -q '^canonicalManuscriptDependencyGraph :' "$PAYMENT_ADAPTER"
grep -q '^searchToEligibleCorpus :' "$PAYMENT_ADAPTER"
grep -q '^eligibleCorpusToSourceScope :' "$PAYMENT_ADAPTER"
grep -q '^sourceScopeToLifecycleSynthesis :' "$PAYMENT_ADAPTER"
grep -q '^sourceScopeToParticipantGovernanceSynthesis :' "$PAYMENT_ADAPTER"
grep -q '^sourceScopeToLongitudinalSynthesis :' "$PAYMENT_ADAPTER"
grep -q '^record SourceScopeMatrixPayment' "$PAYMENT_ADAPTER"
grep -q '^record ManuscriptEvidenceSynthesisAdmission :' "$PAYMENT_ADAPTER"
grep -q '^requiredStructuredSearchSupportCannotBeResidualized :' "$PAYMENT_ADAPTER"
grep -q '^earlyAcquisitionDoesNotPaySkippedDependency :' "$PAYMENT_ADAPTER"
grep -q '^admittedSearchNarrowingRerunsPareto :' "$PAYMENT_ADAPTER"
grep -q '^reopenedSearchFrontierRerunsPareto :' "$PAYMENT_ADAPTER"
grep -q '^canonicalFeedbackBoundaryRetained :' "$PAYMENT_ADAPTER"
grep -q '^canonicalManuscriptDependencyPaymentBoundary :' "$PAYMENT_ADAPTER"

grep -q '^queryFamilyRegression :' "$REGRESSION"
grep -q '^openWebExecutionRegression :' "$REGRESSION"
grep -q '^scopusExecutionRegression :' "$REGRESSION"
grep -q '^wosExecutionRegression :' "$REGRESSION"
grep -q '^ericExecutionRegression :' "$REGRESSION"
grep -q '^acmExecutionRegression :' "$REGRESSION"
grep -q '^ieeeExecutionRegression :' "$REGRESSION"
grep -q '^structuredSearchStillOpenRegression :' "$REGRESSION"
grep -q '^closureRequiresExecutedDatabasesRegression :' "$REGRESSION"
grep -q '^closureDoesNotPromoteSystematicReviewRegression :' "$REGRESSION"
grep -q '^executionReceiptRetainsQueryRegression :' "$REGRESSION"
grep -q '^executionReceiptRetainsExportRegression :' "$REGRESSION"
grep -q '^closureWithoutExecutionBlockedRegression :' "$REGRESSION"
grep -q '^searchClosureDoesNotCloseSynthesisRegression :' "$REGRESSION"
grep -q '^canonicalManuscriptDependencyGraphRegression :' "$REGRESSION"
grep -q '^searchToEligibleCorpusRequiredRegression :' "$REGRESSION"
grep -q '^eligibleCorpusToSourceScopeRequiredRegression :' "$REGRESSION"
grep -q '^sourceScopeToLifecycleRequiredRegression :' "$REGRESSION"
grep -q '^sourceScopeToParticipantGovernanceRequiredRegression :' "$REGRESSION"
grep -q '^sourceScopeToLongitudinalRequiredRegression :' "$REGRESSION"
grep -q '^requiredSearchSupportCannotBeResidualizedRegression :' "$REGRESSION"
grep -q '^admittedSearchNarrowingRerunsParetoRegression :' "$REGRESSION"
grep -q '^reopenedSearchFrontierRerunsParetoRegression :' "$REGRESSION"
grep -q '^canonicalProvenanceBoundaryRegression :' "$REGRESSION"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "structured-search source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
