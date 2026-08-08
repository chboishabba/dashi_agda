#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_claim_corpus_highest_alpha_round24.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoLiteralGalerkinCarrierRound25Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalFiveClassSupportRound25Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalFiveClassSumRound25Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaClayLemmaLadderRound25Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCarrierSupportRound25Validation.agda
  DASHI/Papers/NavierStokes/PhysicalCarrierSupportRound25.agda
  DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound25.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/physical-carrier-support-round25.md
  docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
)

for file in "${files[@]}" "${docs[@]}"; do
  test -f "$file"
done

audit_targets=("${files[@]}" "${docs[@]}")

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-five contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

carrier=DASHI/Physics/Closure/NSTriadKNLuoLiteralGalerkinCarrierRound25Exact.agda
grep -q '10.1007/BF02547354' "$carrier"
grep -q '10.1090/chel/343' "$carrier"
grep -q '10.1007/978-3-642-16830-7' "$carrier"
grep -q 'filterOutputMemberOriginal' "$carrier"
grep -q 'filterOutputNoDuplicates' "$carrier"
grep -q 'physicalOutputFiberNoDuplicates' "$carrier"
grep -q 'LiteralGalerkinCarrierCertificate' "$carrier"
grep -q 'literalGalerkinCarrierCertificate' "$carrier"
grep -q 'projectedPhysicalCoefficientEqualsGalerkinODE' "$carrier"
grep -q 'true true true true true false false' "$carrier"

support=DASHI/Physics/Closure/NSTriadKNLuoPhysicalFiveClassSupportRound25Exact.agda
grep -q '10.24033/asens.1404' "$support"
grep -q '10.1007/978-3-642-16830-7' "$support"
grep -q '10.1007/s00021-019-0411-z' "$support"
grep -q 'natLessTrueToSuccessorLe' "$support"
grep -q 'noTwoInputsThreeShellsBelowOutput' "$support"
grep -q 'classifyPhysicalTriad' "$support"
grep -q 'triadicClassificationUnique' "$support"
grep -q 'lowHighOutputTracksHighOne' "$support"
grep -q 'highLowOutputTracksHighOne' "$support"
grep -q 'highHighInputsComparableOne' "$support"
grep -q 'classifiedPhysicalOutputFiberErasesExactly' "$support"
grep -q 'fiveSourceClassificationTotal' "$support"
grep -q 'separationCollarIsThree' "$support"
grep -q 'outputTrackingCollarIsTwo' "$support"
grep -q 'inputComparabilityCollarIsTwo' "$support"
grep -q 'true true true true true true false false' "$support"

sums=DASHI/Physics/Closure/NSTriadKNLuoPhysicalFiveClassSumRound25Exact.agda
grep -q 'physicalClassificationPreservesTotal' "$sums"
grep -q 'physicalFourClassPartitionExact' "$sums"
grep -q 'physicalFiveSourcePartitionExact' "$sums"

ladder=DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaClayLemmaLadderRound25Exact.agda
grep -q 'canonicalHighestAlphaClayLemmaLadderRound25' "$ladder"
grep -q 'round25L3AggregateIsStillOpen' "$ladder"
grep -q 'round25L4PhysicalSupportIsCheckedExact' "$ladder"
grep -q 'Round25ExactEvidence' "$ladder"
grep -q 'canonicalRound25ExactEvidence' "$ladder"
grep -q 'classwisePhysicalTaxesRemainOpen' "$ladder"
grep -q 'strictMarginRemainsOpen' "$ladder"
grep -q 'round25ClayPromotionRemainsFalse' "$ladder"
grep -q 'true true true true true false false false false' "$ladder"

paper=DASHI/Papers/NavierStokes/PhysicalCarrierSupportRound25.agda
grep -q 'canonicalPhysicalCarrierSupportRound25Status' "$paper"
grep -q 'l4IsCheckedExact' "$paper"
grep -q 'finiteODEInstanceRemainsOpen' "$paper"
grep -q 'physicalTaxesRemainOpen' "$paper"
grep -q 'strictMarginRemainsOpen' "$paper"
grep -q 'clayPromotionRemainsFalse' "$paper"

current=DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound25.agda
grep -q 'canonicalCurrentNSPaperTheoremInterfaceRound25' "$current"
grep -q 'currentRound25L4Checked' "$current"
grep -q 'currentRound25ClayPromotionFalse' "$current"

grep -q '\[literal physical carrier and five-class support tranche\](physical-carrier-support-round25.md)' docs/ns-clay-contract/README.md
grep -q '\[Round 25 physical carrier and support closure\](physical-carrier-support-round25.md)' docs/ns-clay-contract/README.md
grep -q '\[Back to the Clay-contract overview\](README.md)' docs/ns-clay-contract/physical-carrier-support-round25.md
grep -q 'L4 — Exhaustive physical Bony/commutator support theorem — checked exact in Round 25' docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCarrierSupportRound25Validation.agda
