#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_projector_operator_core_round27.sh

files=(
  DASHI/Physics/Closure/NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalTriadConjugationOrbitRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNDependentTaxOwnerPartitionRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNSignedConstituentTreeRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNSignedInteractionFibreRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitSignatureRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNDivisionFreePluckerDefectRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerCriticalAbsorptionRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound28Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCarrierPartitionRound28Validation.agda
  DASHI/Papers/NavierStokes/PhysicalCarrierPartitionRound28.agda
  DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound28.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/architecture.puml
  docs/ns-clay-contract/physical-carrier-partition-round28.md
  docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
)

workflow=.github/workflows/ns-luo-physical-carrier-partition-round28.yml

for file in "${files[@]}" "${docs[@]}" "$workflow"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${files[@]}" "${docs[@]}"; then
  echo "round twenty-eight contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

selector=DASHI/Physics/Closure/NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact.agda
grep -q '10.1007/BF02547354' "$selector"
grep -q '10.1090/chel/343' "$selector"
grep -q 'physicalSelectorIdempotent' "$selector"
grep -q 'physicalSelectorFixesCarrier' "$selector"
grep -q 'concreteNavierStokesSelectorsInstantiated = false' "$selector"
grep -q 'fullPhysicalVectorFieldCommutesWithSelector = false' "$selector"

conjugation=DASHI/Physics/Closure/NSTriadKNPhysicalTriadConjugationOrbitRound28Exact.agda
grep -q '10.1512/iumj.1993.42.42034' "$conjugation"
grep -q 'conjugateTriadInCutoff' "$conjugation"
grep -q 'conjugateOutputFiberWitness' "$conjugation"
grep -q 'pluckerConjugatePreservesSquaredArea' "$conjugation"
grep -q 'fullNonlinearCoefficientEquivarianceClosed = false' "$conjugation"

partition=DASHI/Physics/Closure/NSTriadKNDependentTaxOwnerPartitionRound28Exact.agda
grep -q 'OwnedTaxAtom' "$partition"
grep -q 'dependentPartitionListRoundtrip' "$partition"
grep -q 'signedTotalPreservedByDependentPartition' "$partition"
grep -q 'taxableTotalPreservedByDependentPartition' "$partition"

constituents=DASHI/Physics/Closure/NSTriadKNSignedConstituentTreeRound28Exact.agda
grep -q '10.24033/asens.1404' "$constituents"
grep -q '10.48550/arXiv.2606.27560' "$constituents"
grep -q 'CompatibleOwner' "$constituents"
grep -q 'DelayedPositiveGroup' "$constituents"
grep -q 'groupToTaxAtom' "$constituents"
grep -q 'physicalTimeDependentConstituentsInstantiated = false' "$constituents"

interaction=DASHI/Physics/Closure/NSTriadKNSignedInteractionFibreRound28Exact.agda
grep -q '10.1017/CBO9780511626265' "$interaction"
grep -q 'SignedInteractionCell' "$interaction"
grep -q 'interactionFibreSignedIdentity' "$interaction"
grep -q 'cutoffUniformTStarTBoundClosed = false' "$interaction"

orbit=DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitSignatureRound28Exact.agda
grep -q 'TriadOrbitAction' "$orbit"
grep -q 'orientationParity' "$orbit"
grep -q 'orbitSquaredAreaInvariant' "$orbit"
grep -q 'orbitRepresentativeCertificateReductionImplemented = false' "$orbit"

defect=DASHI/Physics/Closure/NSTriadKNDivisionFreePluckerDefectRound28Exact.agda
grep -q 'pluckerNormScale' "$defect"
grep -q 'modeNormScale' "$defect"
grep -q 'parallelScaledModesHaveZeroDefect' "$defect"
grep -q 'CrossMultipliedAngularDefect' "$defect"
grep -q 'continuumDirectionalNearFieldTaxClosed = false' "$defect"

language=DASHI/Physics/Closure/NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact.agda
grep -q 'AdmissibleOwnerEstimate' "$language"
grep -q 'aggregateOwnerEstimates' "$language"
grep -q 'NineOwnerEstimateFamily' "$language"
grep -q 'physicalNineOwnerEstimatesInstantiated = false' "$language"
grep -q 'strictPhysicalEtaMarginClosed = false' "$language"

absorption=DASHI/Physics/Closure/NSTriadKNNineOwnerCriticalAbsorptionRound28Exact.agda
grep -q 'NineOwnerCriticalBalance' "$absorption"
grep -q 'nineOwnerStrictCriticalEstimate' "$absorption"
grep -q 'physicalNineOwnerCriticalBalanceInstantiated = false' "$absorption"
grep -q 'strictPhysicalEtaCertificateInstantiated = false' "$absorption"

integration=DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaRound28Exact.agda
grep -q 'Round28ExactEvidence' "$integration"
grep -q 'conjugateOutputFibre' "$integration"
grep -q 'divisionFreePluckerScaling' "$integration"
grep -q 'strictNineOwnerAbsorption' "$integration"
grep -q 'uniformOperatorTaxStillOpen' "$integration"
grep -q 'strictMarginStillOpen' "$integration"
grep -q 'clayPromotionStillFalse' "$integration"

paper=DASHI/Papers/NavierStokes/PhysicalCarrierPartitionRound28.agda
grep -q 'canonicalPhysicalCarrierPartitionRound28Status' "$paper"
grep -q 'physicalTaxesStillOpen' "$paper"
grep -q 'clayPromotionStillFalse' "$paper"

current=DASHI/Papers/NavierStokes/CurrentTheoremInterfaceRound28.agda
grep -q 'canonicalCurrentNSPaperTheoremInterfaceRound28' "$current"
grep -q 'admissibleNineOwnerAlgebraChecked' "$current"
grep -q 'physicalOwnerTaxesStillOpen' "$current"
grep -q 'currentRound28ClayPromotionFalse' "$current"

grep -q '\[physical-carrier and signed-partition tranche\](physical-carrier-partition-round28.md)' docs/ns-clay-contract/README.md
grep -q '\[Back to the Clay-contract overview\](README.md)' docs/ns-clay-contract/physical-carrier-partition-round28.md
grep -q 'Round 28' docs/ns-clay-contract/paper-corpus/highest-alpha-lemma-ladder.md
grep -q 'Signed constituent tree' docs/ns-clay-contract/architecture.puml

grep -q 'agent/ns-luo-physical-carrier-partition-round28' "$workflow"
grep -q 'check_ns_luo_physical_carrier_partition_round28.sh' "$workflow"
grep -q 'ns-round28-physical-carrier-partition-agda' "$workflow"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalCarrierPartitionRound28Validation.agda
