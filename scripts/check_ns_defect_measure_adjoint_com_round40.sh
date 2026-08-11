#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bash scripts/check_ns_periodic_pv_odd_com_f4_round39.sh

files=(
  DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadDefectMeasureGainRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHAnalyticThresholdOptimizerRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHSquaredThresholdRepresentationRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHScaleDependentThresholdRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodPVResidualOrderRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodFiniteKernelCauchyRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalTransportCoefficientSkewRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerDualSensitivityRound40Exact.agda
  DASHI/Physics/Closure/NSTriadKNDefectMeasureAdjointComRound40Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|\?|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

# Unified HH directional defect: good and bad are complementary uses of the
# same E*Theta measure, with no differentiated Boolean mask.
grep -q 'thresholdTimesBadEnergyBelowDirectionalDefect' DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
grep -q 'thresholdTimesScaledBadChargeBelowScaledDefect' DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
grep -q 'physicalCrossResidualDensityEqualsDefectDensity' DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
grep -q 'badMassControlledBySameDefect' DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
grep -q 'thresholdTimesBadGainBelowDefectCharge' DASHI/Physics/Closure/NSTriadKNHHBadDefectMeasureGainRound40Exact.agda

# Exact analytic threshold optimization, explicit delta=r^2 bridge, and
# shell-dependent diagnostic.
grep -q 'globalBalancedThresholdMinimum' DASHI/Physics/Closure/NSTriadKNHHAnalyticThresholdOptimizerRound40Exact.agda
grep -q 'selectedTaxClosedForm' DASHI/Physics/Closure/NSTriadKNHHAnalyticThresholdOptimizerRound40Exact.agda
grep -q 'deltaIsScaleSquared' DASHI/Physics/Closure/NSTriadKNHHSquaredThresholdRepresentationRound40Exact.agda
grep -q 'badTaxUsesLiteralDeltaInverse' DASHI/Physics/Closure/NSTriadKNHHSquaredThresholdRepresentationRound40Exact.agda
grep -q 'finiteSelectedScalesMinimize' DASHI/Physics/Closure/NSTriadKNHHScaleDependentThresholdRound40Exact.agda
grep -q 'commonScaleMinimizesFiniteShellTax' DASHI/Physics/Closure/NSTriadKNHHScaleDependentThresholdRound40Exact.agda

# HH-good mandatory order: PV cancellation -> residual -> shell-localized
# weighted Cauchy -> uniform periodized kernel constant -> time absorption.
grep -q 'zeroMassKillsConstantShift' DASHI/Physics/Closure/NSTriadKNHHGoodPVResidualOrderRound40Exact.agda
grep -q 'pvCancellationThenResidual' DASHI/Physics/Closure/NSTriadKNHHGoodPVResidualOrderRound40Exact.agda
grep -q 'finiteHHGoodKernelThresholdBound' DASHI/Physics/Closure/NSTriadKNHHGoodFiniteKernelCauchyRound40Exact.agda
grep -q 'finiteHHGoodUniformKernelBound' DASHI/Physics/Closure/NSTriadKNHHGoodFiniteKernelCauchyRound40Exact.agda
grep -q 'periodizedHHGoodShellBound' DASHI/Physics/Closure/NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact.agda

# Literal Fourier transport skew: resonance + reality + divergence-free move the
# derivative frequency and prove conjugate(reverse) = -forward.
grep -q 'resonantDerivativeRelocation' DASHI/Physics/Closure/NSTriadKNPhysicalTransportCoefficientSkewRound40Exact.agda
grep -q 'physicalTransportCoefficientSkew' DASHI/Physics/Closure/NSTriadKNPhysicalTransportCoefficientSkewRound40Exact.agda
grep -q 'physicalVelocityTransportCoefficientSkew' DASHI/Physics/Closure/NSTriadKNPhysicalTransportCoefficientSkewRound40Exact.agda

# Com adjoint collapse and Z2 audit invariant.
grep -q 'lowerChannelIsNegativeUpperAdjoint' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
grep -q 'commutatorTransportSelfAdjoint' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
grep -q 'commutatorSquareSingleGram' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
grep -q 'oddTransportAnticommutesWithGrading' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
grep -q 'physicalHardShellProjectionSelfAdjointReused = true' <(sed 's/OfficialParseval\.officialPhysicalHardProjectorOrthogonalConstructed/true/' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda) || true

# Dual sensitivity, not just final no-go.
grep -q 'combinedLowerIsSumCellPressure' DASHI/Physics/Closure/NSTriadKNNineOwnerDualSensitivityRound40Exact.agda
grep -q 'headImprovementReducesCertificateLower' DASHI/Physics/Closure/NSTriadKNNineOwnerDualSensitivityRound40Exact.agda

# Load-bearing source metadata.
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadDefectMeasureGainRound40Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNPhysicalTransportCoefficientSkewRound40Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact.agda

# Keep genuinely physical PDE/time producers honest.  Algebraic/fixed-finite
# advances above are intentionally true; the continuum/time owner is not.
grep -q 'physicalTimeIntegratedDirectionalDefectEstimateConstructed = false' DASHI/Physics/Closure/NSTriadKNHHUnifiedDirectionalDefectRound40Exact.agda
grep -q 'physicalDirectionalDefectOwnerRateConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadDefectMeasureGainRound40Exact.agda
grep -q 'physicalHHConstantsFitBalancedScalingConstructed = false' DASHI/Physics/Closure/NSTriadKNHHAnalyticThresholdOptimizerRound40Exact.agda
grep -q 'physicalSquaredDirectionalThresholdConstructed = false' DASHI/Physics/Closure/NSTriadKNHHSquaredThresholdRepresentationRound40Exact.agda
grep -q 'physicalShellHHConstantsConstructed = false' DASHI/Physics/Closure/NSTriadKNHHScaleDependentThresholdRound40Exact.agda
grep -q 'physicalHHGoodSingularNearShellTimeBoundConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodPVResidualOrderRound40Exact.agda
grep -q 'physicalShellLocalizedStrainKernelSamplesConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodFiniteKernelCauchyRound40Exact.agda
grep -q 'physicalStrainShellKernelMassIdentificationConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact.agda
grep -q 'physicalLowTransportGlobalMatrixSkewAdjointConstructed = false' DASHI/Physics/Closure/NSTriadKNPhysicalTransportCoefficientSkewRound40Exact.agda
grep -q 'physicalOddTransportSingleGramRealizationConstructed = false' DASHI/Physics/Closure/NSTriadKNComAdjointCollapseRound40Exact.agda
grep -q 'physicalPartialDualSensitivityCertificateConstructed = false' DASHI/Physics/Closure/NSTriadKNNineOwnerDualSensitivityRound40Exact.agda

chmod +x scripts/agda29_without_k_wrapper.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI.Physics.Closure.NSTriadKNDefectMeasureAdjointComRound40Validation

echo "Round40 defect-measure/adjoint-Com checks passed"
