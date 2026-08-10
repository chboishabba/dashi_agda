#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_strain_gram_cutoff_invariance_round35.sh

files=(
  DASHI/Physics/Closure/NSTriadKNHHBadSchurInverseScaleRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadDissipativeFloorChargingRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNStrainPrincipalAngleCounterexampleRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNComCoarseFineNaturalityRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNShellBudgetProjectiveLedgerRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNTriadSelectionRuleHypergraphRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNFullTriadSelectionRuleRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda
  DASHI/Physics/Closure/NSTriadKNSchurPrincipalAngleProjectiveRound36Validation.agda
)

doc=docs/ns-clay-contract/ns-schur-principal-angle-projective-round36.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|\{\-#[[:space:]]*(TERMINATING|NO_TERMINATION_CHECK)|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext|Properties\.WithK|unique⇒irrelevant' "${files[@]}"; then
  echo "round thirty-six contains a hole, postulate, unsafe/K escape, trust primitive, proof-irrelevance shortcut, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNHHBadSchurInverseScaleRound36Exact.agda:leftDerivativeSchurHasInverseShellScale'
  'NSTriadKNHHBadSchurInverseScaleRound36Exact.agda:rightDerivativeSchurHasInverseShellScale'
  'NSTriadKNHHBadSchurInverseScaleRound36Exact.agda:twoDerivativeSchurIsScaleFree'
  'NSTriadKNHHBadSchurInverseScaleRound36Exact.agda:twoDerivativeSchurCannotHaveInverseShellScale'
  'NSTriadKNHHBadSchurInverseScaleRound36Exact.agda:physicalHHBadSchurBlockRealizationConstructed = false'
  'NSTriadKNHHBadDissipativeFloorChargingRound36Exact.agda:badStratumFloorProducesInverseShellCharging'
  'NSTriadKNHHBadDissipativeFloorChargingRound36Exact.agda:physicalBadStratumDissipativeFloorConstructed = false'
  'NSTriadKNStrainPrincipalAngleCounterexampleRound36Exact.agda:modeDirectionsOrthogonal'
  'NSTriadKNStrainPrincipalAngleCounterexampleRound36Exact.agda:orthogonalModesUnitCrossCoherence'
  'NSTriadKNStrainPrincipalAngleCounterexampleRound36Exact.agda:principalAngleModeSeparationAloneRefuted = true'
  'NSTriadKNComCoarseFineNaturalityRound36Exact.agda:coarseFineNaturalityDefectIsIncrementSum'
  'NSTriadKNComCoarseFineNaturalityRound36Exact.agda:constantVelocityNaturalitySquareCommutes'
  'NSTriadKNComCoarseFineNaturalityRound36Exact.agda:literalComPairProductRealizationConstructed = false'
  'NSTriadKNShellBudgetProjectiveLedgerRound36Exact.agda:inverseDyadicScaleAdd'
  'NSTriadKNShellBudgetProjectiveLedgerRound36Exact.agda:boundaryBudgetAfterSteps'
  'NSTriadKNShellBudgetProjectiveLedgerRound36Exact.agda:canonicalCoherentShellBudgetLedger'
  'NSTriadKNShellBudgetProjectiveLedgerRound36Exact.agda:shellCutoffLimitPreservesOwnerLedgerConstructed = false'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:etaTotalBelowEnvelope'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:robustActualEtaTotalStrict'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:UniformPositiveReserve'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:CriticalReserveWitness'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:ReserveGeometry'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:RobustNineOwnerBudgetPolytope'
  'NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda:physicalRobustNineOwnerBudgetPolytopeConstructed = false'
  'NSTriadKNTriadSelectionRuleHypergraphRound36Exact.agda:retainedEdgeMomentumClosure'
  'NSTriadKNTriadSelectionRuleHypergraphRound36Exact.agda:applyFactoredEdge'
  'NSTriadKNTriadSelectionRuleHypergraphRound36Exact.agda:factoredActionPreservesMomentumClosure'
  'NSTriadKNTriadSelectionRuleHypergraphRound36Exact.agda:physicalCouplingSelectionLawConstructed = false'
  'NSTriadKNFullTriadSelectionRuleRound36Exact.agda:FullPhysicalTriadSelectionLaw'
  'NSTriadKNFullTriadSelectionRuleRound36Exact.agda:fullyAdmissibleMomentumClosure'
  'NSTriadKNFullTriadSelectionRuleRound36Exact.agda:applyFactoredFullyAdmissible'
  'NSTriadKNFullTriadSelectionRuleRound36Exact.agda:physicalFullTriadSelectionLawConstructed = false'
  'NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda:BishopAssignmentsEquivalent'
  'NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda:BishopPhysicalCoordinateEquivalence'
  'NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda:bishopForwardVectorFieldSquare'
  'NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda:bishopReverseVectorFieldSquare'
  'NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda:physicalBishopStateCoordinateEquivalenceConstructed = false'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

# Provenance markers.
grep -q '10.48550/arXiv.math-ph/0505008' DASHI/Physics/Closure/NSTriadKNHHBadSchurInverseScaleRound36Exact.agda
grep -q '10.48550/arXiv.2403.09800' DASHI/Physics/Closure/NSTriadKNHHBadSchurInverseScaleRound36Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadDissipativeFloorChargingRound36Exact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNStrainPrincipalAngleCounterexampleRound36Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNComCoarseFineNaturalityRound36Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNShellBudgetProjectiveLedgerRound36Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNNineOwnerRobustReservePolytopeRound36Exact.agda
grep -q '10.7208/chicago/9780226115498.001.0001' DASHI/Physics/Closure/NSTriadKNTriadSelectionRuleHypergraphRound36Exact.agda
grep -q '10.7208/chicago/9780226115498.001.0001' DASHI/Physics/Closure/NSTriadKNFullTriadSelectionRuleRound36Exact.agda
grep -q '10.1007/978-3-642-61667-9' DASHI/Physics/Closure/NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda
grep -q '10.48550/arXiv.2205.08354' DASHI/Physics/Closure/NSTriadKNBishopSetoidCoordinateGluingRound36Exact.agda

grep -q 'one-derivative Schur' "$doc"
grep -q 'mode principal angles alone are refuted' "$doc"
grep -q 'coarse/fine naturality defect' "$doc"
grep -q 'projective ledger' "$doc"
grep -q 'region, not a point' "$doc"
grep -q 'proof-bearing hypergraph' "$doc"
grep -q 'five-part' "$doc"
grep -q 'Bishop-real setoid' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNSchurPrincipalAngleProjectiveRound36Validation.agda
