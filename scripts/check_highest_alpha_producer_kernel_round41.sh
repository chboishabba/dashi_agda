#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round40.sh

files=(
  DASHI/Physics/Common/PhysicalProducerMaturityExact.agda
  DASHI/Physics/Common/SameSourceGluedProducerExact.agda
  DASHI/Physics/YangMills/BalabanFiniteLinearFunctionalCoordinatesExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintStencilExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramFiniteRangeExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintGluingExact.agda
  DASHI/Physics/YangMills/BalabanSelectedOwnerBudgetSlackExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCertifiedOwnerEnclosureExact.agda
  DASHI/Physics/YangMills/BalabanSelectedSinglePlaquetteWitnessExact.agda
  DASHI/Physics/YangMills/BalabanMoscoRecoveryGapTransferExact.agda
  DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
  DASHI/Physics/Closure/NSHHBadScaleGainFalsificationExact.agda
  DASHI/Physics/Closure/NSAdmissibleRemainderGrammarExact.agda
  DASHI/Physics/Closure/NSNineOwnerStrictSlackExact.agda
  DASHI/Physics/HighestAlphaProducerKernelRound41Validation.agda
)

doc=Docs/support/reference/HighestAlphaProducerKernelRound41.md
index=Docs/support/reference/YangMillsReferenceIndex.md

for file in "${files[@]}" "$doc" "$index"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round forty one contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'PhysicalProducer' DASHI/Physics/Common/PhysicalProducerMaturityExact.agda
grep -q 'sameCarrierCompositeExact' DASHI/Physics/Common/PhysicalProducerMaturityExact.agda
grep -q 'sourceRepresentsIntermediate' DASHI/Physics/Common/PhysicalProducerMaturityExact.agda
grep -q 'intermediateRepresentsOutput' DASHI/Physics/Common/PhysicalProducerMaturityExact.agda
grep -q 'SameSourceGluedProducer' DASHI/Physics/Common/SameSourceGluedProducerExact.agda
grep -q 'sameSourceCombinedUniquePointwise' DASHI/Physics/Common/SameSourceGluedProducerExact.agda

grep -q 'finiteLinearFunctionalCoordinateExpansion' DASHI/Physics/YangMills/BalabanFiniteLinearFunctionalCoordinatesExact.agda
grep -q 'selectedBackgroundGaugeConstraintMatrix' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda
grep -q 'selectedBackgroundGaugeConstraintMatrixApplyExact' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda
grep -q 'GaugeConstraintSpatialSupport' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintStencilExact.agda
grep -q 'selectedBackgroundGaugeConstraintMatrixOutsideStencilZero' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintStencilExact.agda
grep -q 'selectedBackgroundGaugeGram' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramFiniteRangeExact.agda
grep -q 'selectedBackgroundGaugeGramOutsideRangeZero' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramFiniteRangeExact.agda
grep -q 'selectedBackgroundCombinedConstraintCommutesWithProjections' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintGluingExact.agda
grep -q 'selectedBackgroundCombinedConstraintUnique' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintGluingExact.agda
grep -q 'selectedConstraintOperatorLayerForced' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintGluingExact.agda
grep -q 'ownerBudgetSlack' DASHI/Physics/YangMills/BalabanSelectedOwnerBudgetSlackExact.agda
grep -q 'slackCompletesLegacyOwnerBudget' DASHI/Physics/YangMills/BalabanSelectedOwnerBudgetSlackExact.agda
grep -q 'certifiedEnclosuresToOwnerBounds' DASHI/Physics/YangMills/BalabanSelectedCertifiedOwnerEnclosureExact.agda
grep -q 'LiteralSelectedPlaquetteWitness' DASHI/Physics/YangMills/BalabanSelectedSinglePlaquetteWitnessExact.agda
grep -q 'literalSelectedPlaquetteWitnessToCorrelatedExtractionData' DASHI/Physics/YangMills/BalabanSelectedSinglePlaquetteWitnessExact.agda
grep -q 'recoveryStepTransfersUniformGap' DASHI/Physics/YangMills/BalabanMoscoRecoveryGapTransferExact.agda
grep -q 'liminfOnlyCounterexampleLimitGapWouldBeOneBelowZero' DASHI/Physics/YangMills/BalabanMoscoRecoveryGapTransferExact.agda

grep -q 'physicalStateRepresentsEncoding' DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
grep -q 'encodingRepresentsCoefficientFunction' DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
grep -q 'velocityAtPositiveExact' DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
grep -q 'velocityAtNegativeExact' DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
grep -q 'retainedModesExact' DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
grep -q 'actualTriadCancellationExact' DASHI/Physics/Closure/NSGalerkinSameObjectExact.agda
grep -q 'rawHHBadCostDoubles' DASHI/Physics/Closure/NSHHBadScaleGainFalsificationExact.agda
grep -q 'requiredHHBadGainCalibration' DASHI/Physics/Closure/NSHHBadScaleGainFalsificationExact.agda
grep -q 'physicalHHBadEstimateFromScaleGain' DASHI/Physics/Closure/NSHHBadScaleGainFalsificationExact.agda
grep -q 'RemainderSourceAuthority' DASHI/Physics/Closure/NSAdmissibleRemainderGrammarExact.agda
grep -q 'NoForbiddenDependency' DASHI/Physics/Closure/NSAdmissibleRemainderGrammarExact.agda
grep -q 'nineOwnerAbsorptionWithSlack' DASHI/Physics/Closure/NSNineOwnerStrictSlackExact.agda

grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintStencilExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramFiniteRangeExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanSelectedSinglePlaquetteWitnessExact.agda
grep -q '10.1137/1.9780898717716' DASHI/Physics/YangMills/BalabanSelectedCertifiedOwnerEnclosureExact.agda
grep -q '10.1016/0001-8708(69)90009-7' DASHI/Physics/YangMills/BalabanMoscoRecoveryGapTransferExact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSHHBadScaleGainFalsificationExact.agda
grep -q '10.1007/BF01212349' DASHI/Physics/Closure/NSAdmissibleRemainderGrammarExact.agda

grep -q 'Delta_YM' "$doc"
grep -q 'Delta_NS' "$doc"
grep -q 'Mosco recovery' "$doc"
grep -q 'raw Bernstein' "$doc"
grep -q 'gauge-fixing component' "$doc"
grep -q 'gauge-only Gram' "$doc"
grep -Fq '(./HighestAlphaProducerKernelRound41.md)' "$index"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/HighestAlphaProducerKernelRound41Validation.agda
