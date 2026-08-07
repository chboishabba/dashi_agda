#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_galerkin_defect_diffusion_round22.sh

files=(
  DASHI/Physics/Closure/NSTriadKNFeffermanPeriodicClayStatementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoClayEndToEndCompositionRound23Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoClayPrePostInvariantContractRound23Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoClayContractRound23Validation.agda
)

docs=(
  docs/ns-clay-contract/README.md
  docs/ns-clay-contract/requirements.md
  docs/ns-clay-contract/architecture.puml
  docs/ns-clay-contract/verification.md
  docs/ns-clay-contract/governance.md
)

for file in "${files[@]}" "${docs[@]}"; do
  test -f "$file"
done

audit_targets=("${files[@]}" "${docs[@]}")

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty-three contains a hole, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

clay_file=DASHI/Physics/Closure/NSTriadKNFeffermanPeriodicClayStatementExact.agda
grep -q 'FeffermanPeriodicClayStatementB' "$clay_file"
grep -q 'PositiveViscosity' "$clay_file"
grep -q 'DatumSmoothOnThreeTorus' "$clay_file"
grep -q 'DatumDivergenceFree' "$clay_file"
grep -q 'DatumUnitPeriodicInThreeCoordinates' "$clay_file"
grep -q 'SolvesThreeDimensionalMomentumEquationWithZeroForce' "$clay_file"
grep -q 'VelocityUnitPeriodicInThreeCoordinates' "$clay_file"
grep -q 'PressureUnitPeriodicInThreeCoordinates' "$clay_file"
grep -q 'meanZeroDatumNotRequired' "$clay_file"
grep -q 'uniquenessNotAdded' "$clay_file"
grep -q 'periodicEnergyBoundNotAdded' "$clay_file"
grep -q 'physicalTheoremInhabited' "$clay_file"

galilean_file=DASHI/Physics/Closure/NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact.agda
grep -q 'meanZeroSolverAndGalileanRestorationGiveClayB' "$galilean_file"
grep -q 'centeredDatumHasZeroMean' "$galilean_file"
grep -q 'restoreGalileanSolution' "$galilean_file"
grep -q 'galileanPDEInvarianceProvedAnalytically' "$galilean_file"

adapter_file=DASHI/Physics/Closure/NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact.agda
grep -q 'legacyWitnessGivesLiteralFeffermanWitness' "$adapter_file"
grep -q 'transportPressurePeriodicityErratum' "$adapter_file"
grep -q 'transportMomentumEquation' "$adapter_file"
grep -q 'physicalCarrierAdapterInhabited' "$adapter_file"

end_to_end_file=DASHI/Physics/Closure/NSTriadKNLuoClayEndToEndCompositionRound23Exact.agda
grep -q 'inRepoPathClosesLiteralFeffermanPeriodicB' "$end_to_end_file"
grep -q 'legacyUniformPhysicalConstruction' "$end_to_end_file"
grep -q 'literalMeanZeroToLegacy' "$end_to_end_file"
grep -q 'unconditionalClayTheoremStillFalse' "$end_to_end_file"

contract_file=DASHI/Physics/Closure/NSTriadKNLuoClayPrePostInvariantContractRound23Exact.agda
grep -q 'canonicalClayPreconditions' "$contract_file"
grep -q 'canonicalClayPostconditions' "$contract_file"
grep -q 'canonicalProofRouteInvariants' "$contract_file"
grep -q 'canonicalInRepoPathState' "$contract_file"
grep -q 'physicalProducerOpen' "$contract_file"
grep -q 'clayPhysicalProducersRemainOpen' "$contract_file"

grep -q 'Charles L. Fefferman' "$clay_file"
grep -q '10.1090/chel/343' "$galilean_file"
grep -q '10.1007/BF01174182' "$end_to_end_file"

grep -q '\[requirements.md\](requirements.md)' docs/ns-clay-contract/README.md
grep -q '\[C4/PlantUML source\](architecture.puml)' docs/ns-clay-contract/README.md
grep -q '\[Verification and quality gates\](verification.md)' docs/ns-clay-contract/README.md
grep -q '\[Governance and standards alignment\](governance.md)' docs/ns-clay-contract/README.md
grep -q '\[Back to the contract overview\](README.md)' docs/ns-clay-contract/requirements.md
grep -q '\[Back to the contract overview\](README.md)' docs/ns-clay-contract/verification.md
grep -q '\[Back to the contract overview\](README.md)' docs/ns-clay-contract/governance.md

grep -q '^@startuml' docs/ns-clay-contract/architecture.puml
grep -q '^@enduml' docs/ns-clay-contract/architecture.puml
grep -q 'Fefferman periodic alternative B' docs/ns-clay-contract/architecture.puml

grep -q 'ISO 9001' docs/ns-clay-contract/governance.md
grep -q 'ISO/IEC 42001' docs/ns-clay-contract/governance.md
grep -q 'ISO/IEC 27001' docs/ns-clay-contract/governance.md
grep -q 'ISO/IEC 27701' docs/ns-clay-contract/governance.md
grep -q 'ISO/IEC 23894' docs/ns-clay-contract/governance.md
grep -q 'ISO 9241-110' docs/ns-clay-contract/governance.md
grep -q 'ISO 9241-161' docs/ns-clay-contract/governance.md
grep -q 'ISO 9241-210' docs/ns-clay-contract/governance.md
grep -q 'ISO 24552' docs/ns-clay-contract/governance.md
grep -q 'ISO 16817' docs/ns-clay-contract/governance.md
grep -q 'ISO 9241-306' docs/ns-clay-contract/governance.md
grep -q 'ISO 24505' docs/ns-clay-contract/governance.md
grep -q 'ISO 22727' docs/ns-clay-contract/governance.md
grep -q 'NIST AI RMF' docs/ns-clay-contract/governance.md
grep -q 'Six Sigma' docs/ns-clay-contract/governance.md

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoClayContractRound23Validation.agda
