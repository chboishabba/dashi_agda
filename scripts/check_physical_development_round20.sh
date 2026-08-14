#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_oriented_zero_future_compression_round19.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Biology/Physical/SIBiologyDimensionsExact.agda
  DASHI/Biology/Physical/FiniteReactionDiffusionConservationExact.agda
  DASHI/Biology/Physical/ChemicalAffinityEntropyProductionExact.agda
  DASHI/Biology/Physical/CompartmentMembraneTransportExact.agda
  DASHI/Biology/Physical/ElectrochemicalMembranePowerExact.agda
  DASHI/Biology/Physical/SIBioelectricNetworkAdapterExact.agda
  DASHI/Biology/Physical/MechanochemicalMorphogenesisSIExact.agda
  DASHI/Biology/Physical/DevelopmentalGoalFactorizationExact.agda
  DASHI/Biology/Physical/GenomePhysicalParameterCompilerExact.agda
  DASHI/Biology/Physical/DevelopmentalHiddenStateFutureDefectExact.agda
  DASHI/Biology/Physical/PadicPhysicalParameterProjectionExact.agda
  DASHI/Biology/Physical/Harmonic369HelixLiftExact.agda
  DASHI/Biology/Physical/PhysicalOriginsLadderExact.agda
  DASHI/Biology/Physical/CellBrainTransducerBridgeExact.agda
  DASHI/Biology/Physical/DimensionalPhysicalDevelopmentalStateExact.agda
  DASHI/Biology/Physical/PhysicalDevelopmentalOperatorSystemExact.agda
  DASHI/EverythingPhysicalDevelopmentRound20.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'MolarFlux' DASHI/Biology/Physical/SIBiologyDimensionsExact.agda
grep -q 'ForceDensity' DASHI/Biology/Physical/SIBiologyDimensionsExact.agda
grep -q 'diffusionConservesTotal' DASHI/Biology/Physical/FiniteReactionDiffusionConservationExact.agda
grep -q 'drivenStepBalance' DASHI/Biology/Physical/FiniteReactionDiffusionConservationExact.agda
grep -q 'canonicalAffinityIsFour' DASHI/Biology/Physical/ChemicalAffinityEntropyProductionExact.agda
grep -q 'canonicalDissipatedPowerIsEight' DASHI/Biology/Physical/ChemicalAffinityEntropyProductionExact.agda
grep -q 'permeationConservesSolute' DASHI/Biology/Physical/CompartmentMembraneTransportExact.agda
grep -q 'canonicalPumpFitsMetabolicBudget' DASHI/Biology/Physical/ElectrochemicalMembranePowerExact.agda
grep -q 'canonicalVoltageCarrierIsMillivoltScaled' DASHI/Biology/Physical/SIBioelectricNetworkAdapterExact.agda
grep -q 'fieldGeometryChangesAnchor' DASHI/Biology/Physical/MechanochemicalMorphogenesisSIExact.agda
grep -q 'locationIsNotDeterminedByGenericHand' DASHI/Biology/Physical/DevelopmentalGoalFactorizationExact.agda
grep -q 'ownerIsNotDeterminedByHandHere' DASHI/Biology/Physical/DevelopmentalGoalFactorizationExact.agda
grep -q 'sameGenomeDifferentContextCanChangeOutcome' DASHI/Biology/Physical/DevelopmentalGoalFactorizationExact.agda
grep -q 'contextChangesCompiledChannelParameter' DASHI/Biology/Physical/GenomePhysicalParameterCompilerExact.agda
grep -q 'dnaUVStillExact' DASHI/Biology/Physical/GenomePhysicalParameterCompilerExact.agda
grep -q 'morphologyOnlyDynamicDefect' DASHI/Biology/Physical/DevelopmentalHiddenStateFutureDefectExact.agda
grep -q 'morphologyProjectionCannotBeDynamicallySafe' DASHI/Biology/Physical/DevelopmentalHiddenStateFutureDefectExact.agda
grep -q 'finePhysicalParametersDiffer' DASHI/Biology/Physical/PadicPhysicalParameterProjectionExact.agda
grep -q 'phaseTripleSixRoundTrip' DASHI/Biology/Physical/Harmonic369HelixLiftExact.agda
grep -q 'sameCircularProjectionDifferentHistory' DASHI/Biology/Physical/Harmonic369HelixLiftExact.agda
grep -q 'replicationAppearsBeforeAgency' DASHI/Biology/Physical/PhysicalOriginsLadderExact.agda
grep -q 'damageCorrected' DASHI/Biology/Physical/PhysicalOriginsLadderExact.agda
grep -q 'bioelectricNetworkAsStatefulTransducer' DASHI/Biology/Physical/CellBrainTransducerBridgeExact.agda
grep -q 'zeroStateVoltageIsDimensionChecked' DASHI/Biology/Physical/DimensionalPhysicalDevelopmentalStateExact.agda
grep -q 'physicalDevelopmentalStepFactorises' DASHI/Biology/Physical/PhysicalDevelopmentalOperatorSystemExact.agda
grep -q 'chemicalSourceSurvivesDownstreamOperators' DASHI/Biology/Physical/PhysicalDevelopmentalOperatorSystemExact.agda
grep -q 'morphologyOnlyFutureSafetyFails' DASHI/Biology/Physical/PhysicalDevelopmentalOperatorSystemExact.agda

grep -q '10.1098/rstb.1952.0012' DASHI/Biology/Physical/FiniteReactionDiffusionConservationExact.agda
grep -q '10.1113/jphysiol.1952.sp004764' DASHI/Biology/Physical/ElectrochemicalMembranePowerExact.agda
grep -q '10.1038/191144a0' DASHI/Biology/Physical/CompartmentMembraneTransportExact.agda
grep -q '10.1063/1.4818538' DASHI/Biology/Physical/PhysicalOriginsLadderExact.agda
grep -q '10.1103/PhysRevE.100.022414' DASHI/Biology/Physical/PhysicalOriginsLadderExact.agda
grep -q '10.1016/j.cell.2021.02.034' DASHI/Biology/Physical/DevelopmentalGoalFactorizationExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingPhysicalDevelopmentRound20.agda
else
  echo "agda unavailable: structural/fail-closed round-20 scan completed; no kernel-clean claim"
fi
