#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bash scripts/check_ns_defect_measure_adjoint_com_round40.sh

files=(
  DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNComSingleChannelSpectralRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNComSixThreeSingleChannelRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNComHilbertSchmidtMultiplicityRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHDirectionalLayerCakeRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHThresholdScaleLawRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerDualPressureBatchRound41Exact.agda
  DASHI/Physics/Closure/NSTriadKNDefectDensityAnnularComRound41Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|\?|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

# HH-bad: exact magnitude, physical same-object gate, and direct promotion into
# the actual Round-39 inverse-shell restricted-gain certificate.
grep -q 'oneDerivativeSchurNormalizesToInverseShell' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q 'oneDerivativeDensityTimesShellIsScaleFree' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q 'twoDerivativeSchurNormalizesToScaleFree' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q 'physicalOneDerivativeFactorizationExposesInverseShell' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q 'densityBelowInverseShellTarget' DASHI/Physics/Closure/NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact.agda
grep -q 'asRound39InverseShellCertificate' DASHI/Physics/Closure/NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact.agda

# Com: full commutator energy is exactly one cross-channel square.  Reuse the
# existing six-three candidate rather than asking for a second Gram estimate.
grep -q 'commutatorNormSquaredSingleChannelExact' DASHI/Physics/Closure/NSTriadKNComSingleChannelSpectralRound41Exact.agda
grep -q 'singleChannelEnvelopeControlsFullCommutatorEnergy' DASHI/Physics/Closure/NSTriadKNComSingleChannelSpectralRound41Exact.agda
grep -q 'singleChannelGramFromSixThreeSameObject' DASHI/Physics/Closure/NSTriadKNComSixThreeSingleChannelRound41Exact.agda
grep -q 'sixThreeFirstPhysicalPairDecay' DASHI/Physics/Closure/NSTriadKNComSixThreeSingleChannelRound41Exact.agda
grep -q 'sixThreeSecondPhysicalPairDecay' DASHI/Physics/Closure/NSTriadKNComSixThreeSingleChannelRound41Exact.agda

# The finite-rank/Hilbert--Schmidt shortcut is explicitly falsifiable by
# multiplicity growth; no fixed-cutoff finiteness is promoted to uniformity.
grep -q 'multiplicityFloorBelowHilbertSchmidtMass' DASHI/Physics/Closure/NSTriadKNComHilbertSchmidtMultiplicityRound41Exact.agda
grep -q 'uniformHSBudgetForcesMultiplicityBudget' DASHI/Physics/Closure/NSTriadKNComHilbertSchmidtMultiplicityRound41Exact.agda
grep -q 'addingPositiveChannelForcesAtLeastWitnessIncrease' DASHI/Physics/Closure/NSTriadKNComHilbertSchmidtMultiplicityRound41Exact.agda

# One directional-defect budget feeds both strata; finite layer cake shows
# E*Theta is aggregate threshold mass rather than two unrelated bookkeepers.
grep -q 'thresholdBadEnergyBelowSharedBudget' DASHI/Physics/Closure/NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact.agda
grep -q 'goodSquareBelowScaledSharedBudget' DASHI/Physics/Closure/NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact.agda
grep -q 'finiteLayerCakeCellExact' DASHI/Physics/Closure/NSTriadKNHHDirectionalLayerCakeRound41Exact.agda
grep -q 'finiteDirectionalLayerCakeExact' DASHI/Physics/Closure/NSTriadKNHHDirectionalLayerCakeRound41Exact.agda

# Exact scale-law consequences of A r^3 = 2 B.
grep -q 'commonFactorRecoversScaleIndependentThreshold' DASHI/Physics/Closure/NSTriadKNHHThresholdScaleLawRound41Exact.agda
grep -q 'eighthBadCoefficientForcesHalfBalancedScale' DASHI/Physics/Closure/NSTriadKNHHThresholdScaleLawRound41Exact.agda
grep -q 'halfBalancedScaleQuartersDelta' DASHI/Physics/Closure/NSTriadKNHHThresholdScaleLawRound41Exact.agda

# HH-good: master-kernel scaling / finite periodization and square-root-free
# Young closure once the physical W <= X D factorization is supplied.
grep -q 'scaledKernelJacobianMassInvariant' DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
grep -q 'finiteScaledKernelMassInvariant' DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
grep -q 'finitePeriodizationL1Contraction' DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
grep -q 'round40KernelTheoremFromMasterPackage' DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
grep -q 'kernelCriticalDissipationBelowYoungSquare' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda
grep -q 'hhGoodSquaredYoungAbsorption' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda
grep -q 'hhGoodOwnerFromSquaredYoung' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda
grep -q 'periodizedHHGoodOwnerFromLocalMassFactorization' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda
grep -q 'physicalHHGoodTimeDissipationAbsorptionNoLongerIndependent = true' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda

# Batch dual sensitivity quantifies exact savings from improving several owner
# constraints without pretending it is derivative calculus on the optimum.
grep -q 'batchPressureConservation' DASHI/Physics/Closure/NSTriadKNNineOwnerDualPressureBatchRound41Exact.agda
grep -q 'batchNewPressureCannotExceedOld' DASHI/Physics/Closure/NSTriadKNNineOwnerDualPressureBatchRound41Exact.agda

# Source metadata on load-bearing new modules.
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q '10.48550/arXiv.math-ph/0505008' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNComSingleChannelSpectralRound41Exact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/Closure/NSTriadKNComHilbertSchmidtMultiplicityRound41Exact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda

# Keep every genuinely physical same-object/PDE producer fail-closed.
grep -q 'physicalHHBadOneDerivativeFactorizationConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadOneDerivativeGainRound41Exact.agda
grep -q 'physicalHHBadGainDensitySchurSameObjectConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact.agda
grep -q 'physicalHHBadScaleFreeCoefficientBoundConstructed = false' DASHI/Physics/Closure/NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact.agda
grep -q 'physicalOddPQBlockSingleChannelEnvelopeConstructed = false' DASHI/Physics/Closure/NSTriadKNComSingleChannelSpectralRound41Exact.agda
grep -q 'physicalOddPQProductEqualsSixThreeGramConstructed = false' DASHI/Physics/Closure/NSTriadKNComSixThreeSingleChannelRound41Exact.agda
grep -q 'physicalComHilbertSchmidtCutoffUniformConstructed = false' DASHI/Physics/Closure/NSTriadKNComHilbertSchmidtMultiplicityRound41Exact.agda
grep -q 'physicalTimeIntegratedDirectionalDefectBudgetConstructed = false' DASHI/Physics/Closure/NSTriadKNHHDirectionalDefectSharedBudgetRound41Exact.agda
grep -q 'physicalThresholdSuperlevelFamilyConstructed = false' DASHI/Physics/Closure/NSTriadKNHHDirectionalLayerCakeRound41Exact.agda
grep -q 'physicalHHCoefficientScaleLawConstructed = false' DASHI/Physics/Closure/NSTriadKNHHThresholdScaleLawRound41Exact.agda
grep -q 'physicalAnnularMasterKernelSameObjectPackageConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodAnnularMasterKernelRound41Exact.agda
grep -q 'physicalHHGoodWeightedLocalMassFactorizationConstructed = false' DASHI/Physics/Closure/NSTriadKNHHGoodSquaredYoungOwnerRound41Exact.agda
grep -q 'physicalDualPressureBatchFromOwnerConstantsConstructed = false' DASHI/Physics/Closure/NSTriadKNNineOwnerDualPressureBatchRound41Exact.agda

chmod +x scripts/agda29_without_k_wrapper.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI.Physics.Closure.NSTriadKNDefectDensityAnnularComRound41Validation

echo "Round41 defect-density/annular-Com checks passed"
