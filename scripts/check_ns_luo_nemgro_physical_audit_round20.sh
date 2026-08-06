#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_unconditional_absorption_round19.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoPositiveStrainGradientSignExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLocalizedProjectedKornAffineCounterexampleExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCompactSupportPositiveStrainCoreExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoAmplitudeScalingStaticRigidityNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCouplingParameterSignNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSpectralProjectorGapDependenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGlobalPoincareLowFrequencyNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoWeakNonAlignmentCircularityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHighFrequencyApproximationUniformGradientNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartMultiplierExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDirectionalKernelTripleProductExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDirectionalHHBridgeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoNEMGROPhysicalAuditRound20Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

audit_targets=(
  "${files[@]}"
  docs/ns-luo-nemgro-physical-audit-round20.md
)

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${audit_targets[@]}"; then
  echo "round twenty contains a hole, postulate, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

grep -q 'integratedPointwiseGradientIdentity' DASHI/Physics/Closure/NSTriadKNLuoPositiveStrainGradientSignExact.agda
grep -q 'antisymmetricGradientCubicCancels' DASHI/Physics/Closure/NSTriadKNLuoPositiveStrainGradientSignExact.agda
grep -q 'positiveStrainIsFavourableForGradientEnergy' DASHI/Physics/Closure/NSTriadKNLuoPositiveStrainGradientSignExact.agda

grep -q 'localizedProjectedKornFailsForEveryCoefficient' DASHI/Physics/Closure/NSTriadKNLuoLocalizedProjectedKornAffineCounterexampleExact.agda
grep -q 'positiveStrainContractionIsEight' DASHI/Physics/Closure/NSTriadKNLuoLocalizedProjectedKornAffineCounterexampleExact.agda

grep -q 'localizedCurlIsDivergenceFree' DASHI/Physics/Closure/NSTriadKNLuoCompactSupportPositiveStrainCoreExact.agda
grep -q 'plateauGradientEqualsAffine' DASHI/Physics/Closure/NSTriadKNLuoCompactSupportPositiveStrainCoreExact.agda
grep -q 'plateauPositiveStrainDensityIsEight' DASHI/Physics/Closure/NSTriadKNLuoCompactSupportPositiveStrainCoreExact.agda

grep -q 'scalingGapIdentity' DASHI/Physics/Closure/NSTriadKNLuoAmplitudeScalingStaticRigidityNoGoExact.agda
grep -q 'staticRigidityFailsAtExplicitAmplitude' DASHI/Physics/Closure/NSTriadKNLuoAmplitudeScalingStaticRigidityNoGoExact.agda

grep -q 'youngDefectIdentity' DASHI/Physics/Closure/NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact.agda
grep -q 'quarticYoungInequality' DASHI/Physics/Closure/NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact.agda
grep -q 'threeDimensionalYoungClosure' DASHI/Physics/Closure/NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact.agda

grep -q 'largeCouplingDestroysStrictDissipation' DASHI/Physics/Closure/NSTriadKNLuoCouplingParameterSignNoGoExact.agda
grep -q 'thresholdChoiceHasZeroDissipation' DASHI/Physics/Closure/NSTriadKNLuoCouplingParameterSignNoGoExact.agda

grep -q 'inverseGapIdentity' DASHI/Physics/Closure/NSTriadKNLuoSpectralProjectorGapDependenceExact.agda
grep -q 'crossingMatricesCoincide' DASHI/Physics/Closure/NSTriadKNLuoSpectralProjectorGapDependenceExact.agda
grep -q 'projectorSidesDistinct' DASHI/Physics/Closure/NSTriadKNLuoSpectralProjectorGapDependenceExact.agda

grep -q 'scaleTimesFrequencyIsOne' DASHI/Physics/Closure/NSTriadKNLuoGlobalPoincareLowFrequencyNoGoExact.agda
grep -q 'universalGlobalPoincareCoefficientFails' DASHI/Physics/Closure/NSTriadKNLuoGlobalPoincareLowFrequencyNoGoExact.agda

grep -q 'emptyCycle' DASHI/Physics/Closure/NSTriadKNLuoWeakNonAlignmentCircularityExact.agda
grep -q 'finiteContinuationCanBeTrueWhileCycleEndpointsAreEmpty' DASHI/Physics/Closure/NSTriadKNLuoWeakNonAlignmentCircularityExact.agda

grep -q 'highFrequencyGradientClosedForm' DASHI/Physics/Closure/NSTriadKNLuoHighFrequencyApproximationUniformGradientNoGoExact.agda
grep -q 'highFrequencyGradientExceedsEveryThreshold' DASHI/Physics/Closure/NSTriadKNLuoHighFrequencyApproximationUniformGradientNoGoExact.agda

grep -q 'recoverTransverseVorticity' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartMultiplierExact.agda
grep -q 'strainSymbolTraceFree' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartMultiplierExact.agda
grep -q 'strainSymbol12Symmetric' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartMultiplierExact.agda

grep -q 'physicalDirectionalTripleBound' DASHI/Physics/Closure/NSTriadKNLuoDirectionalKernelTripleProductExact.agda
grep -q 'finiteDirectionalHHSquaredBridge' DASHI/Physics/Closure/NSTriadKNLuoFiniteDirectionalHHBridgeExact.agda
grep -q 'finiteDirectionalHHAbsorption' DASHI/Physics/Closure/NSTriadKNLuoFiniteDirectionalHHBridgeExact.agda

grep -q '10.1007/s00205-019-01419-z' DASHI/Physics/Closure/NSTriadKNLuoPositiveStrainGradientSignExact.agda
grep -q '10.1017/CBO9780511608803' DASHI/Physics/Closure/NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact.agda
grep -q '10.1007/978-3-642-66282-9' DASHI/Physics/Closure/NSTriadKNLuoSpectralProjectorGapDependenceExact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNLuoDirectionalKernelTripleProductExact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoFiniteDirectionalHHBridgeExact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNLuoGlobalPoincareLowFrequencyNoGoExact.agda
grep -q 'PhilArchive record: NEMGRO' DASHI/Physics/Closure/NSTriadKNLuoWeakNonAlignmentCircularityExact.agda

grep -q 'constructiveSmoothBumpImplemented' DASHI/Physics/Closure/NSTriadKNLuoCompactSupportPositiveStrainCoreExact.agda
grep -q 'principalValueKernelConstructed' DASHI/Physics/Closure/NSTriadKNLuoPeriodicBiotSavartMultiplierExact.agda
grep -q 'physicalContinuumKernelProducerProved' DASHI/Physics/Closure/NSTriadKNLuoFiniteDirectionalHHBridgeExact.agda
grep -q 'L2ConvergenceSuppliesUniformInitialH1' DASHI/Physics/Closure/NSTriadKNLuoHighFrequencyApproximationUniformGradientNoGoExact.agda

test -f docs/ns-luo-nemgro-physical-audit-round20.md

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoNEMGROPhysicalAuditRound20Validation.agda
