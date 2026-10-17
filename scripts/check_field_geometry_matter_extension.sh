#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

files=(
  DASHI/Physics/CondensedMatter/MATBGQTMInstrumentCalibration2026Exact.agda
  DASHI/Physics/CondensedMatter/MATBGQTMInstrumentCalibration2026Validation.agda
  DASHI/Physics/CondensedMatter/MATBGQTMResolutionKernelReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGQTMResolutionKernelValidation.agda
  DASHI/Physics/CondensedMatter/MATBGQTMResolutionAwareForwardObserverReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGQTMResolutionAwareForwardObserverValidation.agda
  DASHI/Physics/Foundations/CasimirIdealSheetScalingCeilingReceiptExact.agda
  DASHI/Physics/Foundations/CasimirIdealSheetScalingCeilingValidation.agda
  DASHI/Physics/Foundations/WarpEnergyConditionSourceAtlasExact.agda
  DASHI/Physics/Foundations/WarpEnergyConditionSourceAtlasValidation.agda
  DASHI/Physics/Foundations/CausalTransport2026SourceAtlasExact.agda
  DASHI/Physics/Foundations/CausalTransport2026SourceAtlasValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file" || { echo "missing required file: $file" >&2; exit 1; }
  if grep -nE '\{!!\}|(^|[[:space:]])postulate([[:space:]]|$)|--unsafe|allow-unsolved-metas|--type-in-type|--no-positivity-check|--no-termination-check' "$file"; then
    echo "forbidden hole, postulate, unsolved-meta or unsafe option in $file" >&2
    exit 1
  fi
done

artifacts=(
  scripts/matbg_qtm_resolution_kernel.py
  Docs/evidence/matbg_qtm_resolution_kernel_2026-10-16.json
  scripts/matbg_qtm_resolution_aware_forward_observer.py
  Docs/evidence/matbg_qtm_resolution_aware_forward_observer_2026-10-16.json
  scripts/casimir_ideal_sheet_scaling_ceiling.py
  Docs/evidence/casimir_ideal_sheet_scaling_ceiling_2026-10-16.json
)

for artifact in "${artifacts[@]}"; do
  test -f "$artifact" || { echo "missing execution artifact: $artifact" >&2; exit 1; }
done

grep -q 'sampleGeometrySourcePaid' DASHI/Physics/CondensedMatter/MATBGQTMInstrumentCalibration2026Exact.agda
grep -q 'normalizedSyntheticKernelExecuted' DASHI/Physics/CondensedMatter/MATBGQTMResolutionKernelReceiptExact.agda
grep -q 'syntheticResolutionAwareSurfaceExecuted' DASHI/Physics/CondensedMatter/MATBGQTMResolutionAwareForwardObserverReceiptExact.agda
grep -q 'fixedGapAreaCeilingNumericallyExecuted' DASHI/Physics/Foundations/CasimirIdealSheetScalingCeilingReceiptExact.agda
grep -q 'genericPhysicallyReasonableWarpEnergyConditionViolationSourcePaid' DASHI/Physics/Foundations/WarpEnergyConditionSourceAtlasExact.agda
grep -q 'constantVelocitySubluminalPositiveEnergyConstructionSourcePaid' DASHI/Physics/Foundations/WarpEnergyConditionSourceAtlasExact.agda
grep -q 'unconditionalRemoteGateTeleportationExperimentPaid' DASHI/Physics/Foundations/CausalTransport2026SourceAtlasExact.agda
grep -q 'lossyChannelTeleportationAdvantageExperimentPaid' DASHI/Physics/Foundations/CausalTransport2026SourceAtlasExact.agda
grep -q 'qetCarrierFreeProtocolTheorySourcePaid' DASHI/Physics/Foundations/CausalTransport2026SourceAtlasExact.agda
grep -q 'qetCountsAsMacroscopicPropellantlessEnergyTransport' DASHI/Physics/Foundations/CausalTransport2026SourceAtlasExact.agda
grep -q 'casimirEGBTraversableWormholeTheorySourcePaid' DASHI/Physics/Foundations/CausalTransport2026SourceAtlasExact.agda
grep -q 'qtmResolutionAwareForwardObserver' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'casimirIdealSheetScalingCeiling' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'genericWarpEnergyConditionObstructionSource' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'remoteQuantumGateTeleportationExperimentSource' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'lossyChannelTeleportationAdvantageExperimentSource' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'quantumEnergyTeleportationProtocolSource' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'qetCountsAsMacroscopicPropellantlessEnergyTransport' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'physicalWormholeRealization' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda

python3 scripts/check_field_geometry_matter_evidence.py

echo "field-geometry-matter extension checks OK"
