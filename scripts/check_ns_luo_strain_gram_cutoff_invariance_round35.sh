#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_fourier_strain_hhbad_round34.sh

files=(
  DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainGramRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainInterferenceRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNFixedCutoffSupportInvariantRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNModeInverseSquareRealityRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNComplex3RealityLawsRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNOrderedInteractionRealityRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalOutputFiberConjugationRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNComGramInterferenceRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNTriadS3RealityActionRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNVectorFieldIndexedGluingRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNDualResourceScaleLedgerRound35Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoStrainGramCutoffInvariantRound35Validation.agda
)

doc=docs/ns-clay-contract/ns-strain-gram-cutoff-invariance-round35.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|\{\-#[[:space:]]*(TERMINATING|NO_TERMINATION_CHECK)|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round thirty-five contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNPeriodicFourierStrainGramRound35Exact.agda:crossMixedLagrange'
  'NSTriadKNPeriodicFourierStrainGramRound35Exact.agda:fourierStrainCrossFibreGramExact'
  'NSTriadKNPeriodicFourierStrainGramRound35Exact.agda:fourierStrainTransversePolarization'
  'NSTriadKNPeriodicFourierStrainGramRound35Exact.agda:fourierStrainHalfIsometry'
  'NSTriadKNPeriodicFourierStrainGramRound35Exact.agda:physicalHHGoodCrossFibreEstimateConstructed = false'
  'NSTriadKNPeriodicFourierStrainInterferenceRound35Exact.agda:frobeniusSquaredAdd'
  'NSTriadKNPeriodicFourierStrainInterferenceRound35Exact.agda:crossWithHeadIsInnerOfTail'
  'NSTriadKNPeriodicFourierStrainInterferenceRound35Exact.agda:finiteStrainInterferenceDecomposition'
  'NSTriadKNPeriodicFourierStrainInterferenceRound35Exact.agda:physicalCrossFibreInterferenceDecayConstructed = false'
  'NSTriadKNFixedCutoffSupportInvariantRound35Exact.agda:positiveLiteralOutputCoefficients'
  'NSTriadKNFixedCutoffSupportInvariantRound35Exact.agda:fixedSupportDerivativeModesExact'
  'NSTriadKNFixedCutoffSupportInvariantRound35Exact.agda:derivativeInSameCutoffSupportFibre'
  'NSTriadKNFixedCutoffSupportInvariantRound35Exact.agda:fixedCutoffSameObjectCompatibilityInvariantConstructed = false'
  'NSTriadKNModeInverseSquareRealityRound35Exact.agda:normSquaredEven'
  'NSTriadKNModeInverseSquareRealityRound35Exact.agda:inverseNormSquaredEven'
  'NSTriadKNModeInverseSquareRealityRound35Exact.agda:rightInverseUnique'
  'NSTriadKNModeInverseSquareRealityRound35Exact.agda:canonicalEvenModeInverseSquare'
  'NSTriadKNComplex3RealityLawsRound35Exact.agda:lerayCorrectionModeEven'
  'NSTriadKNComplex3RealityLawsRound35Exact.agda:lerayProjectModeEven'
  'NSTriadKNComplex3RealityLawsRound35Exact.agda:lerayProjectConjugation'
  'NSTriadKNComplex3RealityLawsRound35Exact.agda:canonicalCorrectComplex3RealityLaws'
  'NSTriadKNOrderedInteractionRealityRound35Exact.agda:orderedVelocityInteractionReality'
  'NSTriadKNOrderedInteractionRealityRound35Exact.agda:projectedOrderedTermConjugateTriad'
  'NSTriadKNOrderedInteractionRealityRound35Exact.agda:orderedInteractionRealityClosed = true'
  'NSTriadKNOrderedInteractionRealityRound35Exact.agda:summedProjectedNonlinearityRealityConstructed = false'
  'NSTriadKNPhysicalOutputFiberConjugationRound35Exact.agda:conjugateFiberRepresentative'
  'NSTriadKNPhysicalOutputFiberConjugationRound35Exact.agda:physicalOutputFiberLabelledConjugationBijection'
  'NSTriadKNPhysicalOutputFiberConjugationRound35Exact.agda:physicalOutputFiberConjugationBijectionClosed = true'
  'NSTriadKNPhysicalOutputFiberConjugationRound35Exact.agda:outputFiberConjugationListPermutationConstructed = false'
  'NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda:canonicalFiniteShellBudgetGluing'
  'NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda:boundaryBudgetHalves'
  'NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda:cutoffAdvanceConservesTotalBudget'
  'NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda:canonicalShellBudgetTransferStep'
  'NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda:physicalHHBadShellBudgetProduced = false'
  'NSTriadKNComGramInterferenceRound35Exact.agda:outerContractionsRemove'
  'NSTriadKNComGramInterferenceRound35Exact.agda:sixThreeGramCandidatePairDecay'
  'NSTriadKNComGramInterferenceRound35Exact.agda:physicalComFirstPairDecayFromGram'
  'NSTriadKNComGramInterferenceRound35Exact.agda:physicalComPairProductGramRealizationConstructed = false'
  'NSTriadKNTriadS3RealityActionRound35Exact.agda:factoredActionExact'
  'NSTriadKNTriadS3RealityActionRound35Exact.agda:canonicalOrbitIffFactoredAction'
  'NSTriadKNTriadS3RealityActionRound35Exact.agda:freeTwelveElementOrbitAssumed = false'
  'NSTriadKNVectorFieldIndexedGluingRound35Exact.agda:coordinateVectorField'
  'NSTriadKNVectorFieldIndexedGluingRound35Exact.agda:reverseSquareFromForward'
  'NSTriadKNVectorFieldIndexedGluingRound35Exact.agda:canonicalVectorFieldIndexedGluing'
  'NSTriadKNVectorFieldIndexedGluingRound35Exact.agda:physicalBishopVectorFieldIndexedGluingConstructed = false'
  'NSTriadKNDualResourceScaleLedgerRound35Exact.agda:criticalInverseScaleBalancesRawHHBad'
  'NSTriadKNDualResourceScaleLedgerRound35Exact.agda:scaleFreeGainCannotBalanceRawHHBad'
  'NSTriadKNDualResourceScaleLedgerRound35Exact.agda:hhBadScaleFreeAbsorptionImpossible'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

# Provenance markers on imported mathematics.
grep -q '10.1512/iumj.1993.42.42034' DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainGramRound35Exact.agda
grep -q '10.1080/03605309608821197' DASHI/Physics/Closure/NSTriadKNPeriodicFourierStrainInterferenceRound35Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNFixedCutoffSupportInvariantRound35Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNModeInverseSquareRealityRound35Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNComplex3RealityLawsRound35Exact.agda
grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNOrderedInteractionRealityRound35Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNPhysicalOutputFiberConjugationRound35Exact.agda
grep -q '10.1007/s00021-019-0411-z' DASHI/Physics/Closure/NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNComGramInterferenceRound35Exact.agda
grep -q '10.7208/chicago/9780226115498.001.0001' DASHI/Physics/Closure/NSTriadKNTriadS3RealityActionRound35Exact.agda
grep -q '10.1007/978-3-642-61667-9' DASHI/Physics/Closure/NSTriadKNVectorFieldIndexedGluingRound35Exact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNDualResourceScaleLedgerRound35Exact.agda

grep -q 'cross-fibre interference' "$doc"
grep -q 'fixed-cutoff support' "$doc"
grep -q 'internal budget plus boundary budget' "$doc"
grep -q 'operator-realisation' "$doc"
grep -q 'Bishop-real' "$doc"
grep -q 'scale-free' "$doc"
grep -q 'inverse-square evenness' "$doc"
grep -q 'ordered nonlinear interaction' "$doc"
grep -q 'labelled output-fibre conjugation' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoStrainGramCutoffInvariantRound35Validation.agda
