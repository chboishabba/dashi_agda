#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round32.sh

files=(
  DASHI/Physics/YangMills/YangMillsPaperClaimAuditCarrierExact.agda
  DASHI/Physics/YangMills/YangMillsAdversarialClaimAtlasExact.agda
  DASHI/Physics/YangMills/YangMillsClaimFamilyBridgeObligationsExact.agda
  DASHI/Physics/YangMills/YangMillsCompactSimpleGroupPromotionExact.agda
  DASHI/Physics/YangMills/YangMillsFixedSpacingGapScaleCounterexampleExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundVariationalChartBridgeExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound33PaperAuditAllGroupsValidation.agda
)

doc=Docs/support/reference/YangMillsPaperAuditRound33.md
index=Docs/support/reference/YangMillsReferenceIndex.md
workflow=.github/workflows/yang-mills-clay-highest-alpha-round33.yml

for file in "${files[@]}" "$doc" "$index" "$workflow"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty three contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'YangMillsPaperClaimAuditCarrierExact.agda:requiredPromotionBridgeCountExact'
  'YangMillsPaperClaimAuditCarrierExact.agda:numericalEvidenceIsNotFormalProof'
  'YangMillsPaperClaimAuditCarrierExact.agda:latticeAgreementIsNotFormalProof'
  'YangMillsPaperClaimAuditCarrierExact.agda:fixedSpacingTheoryIsNotContinuumTheory'
  'YangMillsAdversarialClaimAtlasExact.agda:claimSourceCountExact'
  'YangMillsAdversarialClaimAtlasExact.agda:noAuditedClaimIsKernelProof'
  'YangMillsAdversarialClaimAtlasExact.agda:noAuditedClaimIsCheckedClayTheorem'
  'YangMillsAdversarialClaimAtlasExact.agda:agawaAddendumRetractionRecorded'
  'YangMillsClaimFamilyBridgeObligationsExact.agda:toupinBridgeCountExact'
  'YangMillsClaimFamilyBridgeObligationsExact.agda:jacobsenBridgeCountExact'
  'YangMillsClaimFamilyBridgeObligationsExact.agda:wattBridgeCountExact'
  'YangMillsCompactSimpleGroupPromotionExact.agda:requiredGroupDatumCountExact'
  'YangMillsCompactSimpleGroupPromotionExact.agda:exceptionalFamilyCountExact'
  'YangMillsCompactSimpleGroupPromotionExact.agda:e8DualCoxeterExact'
  'YangMillsCompactSimpleGroupPromotionExact.agda:sunIsNotAllCompactSimple'
  'YangMillsFixedSpacingGapScaleCounterexampleExact.agda:quadraticGapRescalesToSpacing'
  'YangMillsFixedSpacingGapScaleCounterexampleExact.agda:gapQuarterPositive'
  'YangMillsFixedSpacingGapScaleCounterexampleExact.agda:halfToQuarterPhysicalGapHalves'
  'YangMillsFixedSpacingGapScaleCounterexampleExact.agda:quadraticGapCounterexample'
  'BalabanSelectedBackgroundVariationalChartBridgeExact.agda:selectedBackgroundUniqueInRegularGauge'
  'BalabanSelectedBackgroundVariationalChartBridgeExact.agda:selectedBackgroundBondDefectBelowChart'
  'BalabanSelectedBackgroundVariationalChartBridgeExact.agda:selectedBackgroundBondPrincipalAdmissible'
  'BalabanSelectedBackgroundVariationalChartBridgeExact.agda:selectedBackgroundInverseLogOrientation'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.5281/zenodo.19939019' \
  DASHI/Physics/YangMills/YangMillsAdversarialClaimAtlasExact.agda
grep -q '10.48550/arXiv.2506.00284' \
  DASHI/Physics/YangMills/YangMillsAdversarialClaimAtlasExact.agda
grep -q '10.33774/coe-2025-3jmcf-v2' \
  DASHI/Physics/YangMills/YangMillsAdversarialClaimAtlasExact.agda
grep -q '10.5281/zenodo.19699784' \
  DASHI/Physics/YangMills/YangMillsAdversarialClaimAtlasExact.agda
grep -q '10.1007/BF01229381' \
  DASHI/Physics/YangMills/BalabanSelectedBackgroundVariationalChartBridgeExact.agda
grep -q '10.1007/978-1-4757-2453-0' \
  DASHI/Physics/YangMills/YangMillsCompactSimpleGroupPromotionExact.agda

grep -Fq '[Round 33 — paper-claim audit, all-group rejection guards and scale counterexample](./YangMillsPaperAuditRound33.md)' "$index"
grep -q 'Every paper is admissible as an object of study' "$doc"
grep -q 'Delta_latt(a) = a^2' "$doc"
grep -q 'G2 = 4, F4 = 9, E6 = 12, E7 = 18, E8 = 30' "$doc"
grep -q 'A static audit is not a kernel result' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound33PaperAuditAllGroupsValidation.agda
