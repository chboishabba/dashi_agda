#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/BalabanBishopRatioMonotoneTermsExact.agda
  DASHI/Physics/YangMills/BalabanBishopAlternatingFirstOmittedExact.agda
  DASHI/Physics/YangMills/BalabanP06CanonicalAnimalConstantExact.agda
  DASHI/Physics/YangMills/BalabanP06A1A2A3InfluenceExact.agda
  DASHI/Physics/YangMills/BalabanP11PrefixTailMinimumExact.agda
  DASHI/Physics/YangMills/BalabanStepVCanonicalAnimalMarginExact.agda
  DASHI/Physics/YangMills/BalabanStepVGeometricInfluenceSummationExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound8SourceAudit.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound8Ledger.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound8Receipt.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound8Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSubmissionRound8Advance.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "round-eight submission tranche contains a postulate or explicit hole" >&2
  exit 1
fi

# Recent 2602.0070/0072 material is deliberately audit-only.  The source audit
# must not silently promote it to an imported theorem.
grep -q 'recent26020070AuditLead' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound8SourceAudit.agda
grep -q 'recent26020072AuditLead' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound8SourceAudit.agda
grep -q 'mayInhabitImportedTheorem = false' \
  DASHI/Physics/YangMills/YangMillsSubmissionRound8SourceAudit.agda

# The numerical Step-V interface must be the canonical animal constant together
# with a strict logarithmic decay margin, rather than a generic smallness flag.
grep -q 'canonicalAnimalConstant' \
  DASHI/Physics/YangMills/BalabanStepVCanonicalAnimalMarginExact.agda
grep -q 'logMarginImpliesWeightedRatioBelowOne' \
  DASHI/Physics/YangMills/BalabanStepVCanonicalAnimalMarginExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanBishopRatioMonotoneTermsExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanBishopAlternatingFirstOmittedExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP06CanonicalAnimalConstantExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP11PrefixTailMinimumExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/YangMillsSubmissionRound8Validation.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSubmissionRound8Advance.agda
