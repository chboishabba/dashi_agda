#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_clay_contract_round23.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoClaimedSolutionCorpusRound24Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoAbuGhuwalehAdditiveFloorNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCamlinTemporalLiftNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoClaimRouteCrosswalkRound24Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoClaimCorpusHighestAlphaRound24Validation.agda
  DASHI/Papers/NavierStokes/ClaimCorpusHighestAlphaRound24.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/architecture.puml
  docs/ns-clay-contract/paper-corpus/README.md
  docs/ns-clay-contract/paper-corpus/audit-matrix.md
  docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
  docs/ns-clay-contract/paper-corpus/verification.md
)

for file in "${files[@]}" "${docs[@]}"; do
  test -f "$file"
done

audit_targets=("${files[@]}" "${docs[@]}")

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-four contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

corpus=DASHI/Physics/Closure/NSTriadKNLuoClaimedSolutionCorpusRound24Exact.agda
grep -q 'claimedSolutionCorpusRound24' "$corpus"
grep -q '10.5281/zenodo.19559087' "$corpus"
grep -q '10.63968/post-bio-ai-epistemics.v1n2.012' "$corpus"
grep -q '10.5281/zenodo.21194906' "$corpus"
grep -q '10.5281/zenodo.19632058' "$corpus"
grep -q '2606.27560' "$corpus"
grep -q '2605.01875' "$corpus"
grep -q '2605.01873' "$corpus"
grep -q '2601.15685' "$corpus"
grep -q '10.3390/math14091410' "$corpus"
grep -q '10.20944/preprints202603.1591.v1' "$corpus"
grep -q 'NEMGRO' "$corpus"
grep -q 'allCorpusSourcesAreProofAuthorities = false' "$corpus"
grep -q 'corpusSearchIsDeclaredExhaustive = false' "$corpus"

abu=DASHI/Physics/Closure/NSTriadKNLuoAbuGhuwalehAdditiveFloorNoGoExact.agda
grep -q 'counterDissipativeStep' "$abu"
grep -q 'counterUpperComparison' "$abu"
grep -q 'pureStrictDecayConclusionFalse' "$abu"
grep -q 'canonicalAdditiveFloorNoGoWitness' "$abu"

camlin=DASHI/Physics/Closure/NSTriadKNLuoCamlinTemporalLiftNoGoExact.agda
grep -q 'finiteHorizonBoundsExist' "$camlin"
grep -q 'finiteHorizonFamilyDoesNotYieldGlobalUniformBound' "$camlin"
grep -q 'bkmDivergenceCannotBeRemovedByExactTimeChange' "$camlin"
grep -q 'bkmFinitenessCannotBeCreatedByExactTimeChange' "$camlin"
grep -q 'superlinearDriftGapAtCoefficientPlusOne' "$camlin"

crosswalk=DASHI/Physics/Closure/NSTriadKNLuoClaimRouteCrosswalkRound24Exact.agda
grep -q 'firstLoadBearingNode' "$crosswalk"
grep -q 'abuClaimEntersAtStrictMargin' "$crosswalk"
grep -q 'camlinClaimEntersAtNonCircularGronwall' "$crosswalk"
grep -q 'permanaClaimEntersAtPeriodicKernel' "$crosswalk"

ladder=DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact.agda
grep -q 'L0_literalFeffermanPeriodicAlternativeB' "$ladder"
grep -q 'L7_fivePhysicalSourceBoundsUniformInCutoffs' "$ladder"
grep -q 'L15_strictTotalViscosityTaxBelowOne' "$ladder"
grep -q 'L23_literalFeffermanWitnessAndAuditComposition' "$ladder"
grep -q 'highestAlphaPathInputsGiveLiteralClayB' "$ladder"
grep -q 'unconditionalClayTheoremPromoted' "$ladder"

paper=DASHI/Papers/NavierStokes/ClaimCorpusHighestAlphaRound24.agda
grep -q 'canonicalClaimCorpusHighestAlphaRound24Status' "$paper"
grep -q 'claimCorpusIsNotProofAuthority' "$paper"
grep -q 'physicalProducersRemainOpen' "$paper"
grep -q 'clayPromotionRemainsFalse' "$paper"

grep -q '\[Claimed-paper corpus and audits\](paper-corpus/README.md)' docs/ns-clay-contract/README.md
grep -q '\[Audit matrix\](audit-matrix.md)' docs/ns-clay-contract/paper-corpus/README.md
grep -q '\[Highest-alpha lemma ladder\](highest-alpha-lemma-ladder.md)' docs/ns-clay-contract/paper-corpus/README.md
grep -q '\[Verification phase\](verification.md)' docs/ns-clay-contract/paper-corpus/README.md
grep -q '\[Back to the paper-corpus overview\](README.md)' docs/ns-clay-contract/paper-corpus/audit-matrix.md
grep -q '\[Back to the paper-corpus overview\](README.md)' docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
grep -q '\[Back to the paper-corpus overview\](README.md)' docs/ns-clay-contract/paper-corpus/verification.md

grep -q '^@startuml' docs/ns-clay-contract/architecture.puml
grep -q '^@enduml' docs/ns-clay-contract/architecture.puml
grep -q 'Claim corpus and falsification' docs/ns-clay-contract/architecture.puml

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoClaimCorpusHighestAlphaRound24Validation.agda
