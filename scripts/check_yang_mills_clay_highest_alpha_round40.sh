#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round39.sh

files=(
  DASHI/Physics/YangMills/BalabanSelectedVariationSignConventionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedMultiplierPairingRedundancyInvariantExact.agda
  DASHI/Physics/YangMills/BalabanSelectedConstraintCollarPairingExact.agda
  DASHI/Physics/YangMills/BalabanSelectedRawExtractorConstraintDefectAtomsExact.agda
  DASHI/Physics/YangMills/BalabanSelectedMultiplierDefectGreenContractionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCorrelatedResidualOwnershipExact.agda
  DASHI/Physics/YangMills/BalabanSelectedConstraintGramCombesThomasExact.agda
  DASHI/Physics/YangMills/BalabanSelectedKKTMultiplierLocalityExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockCombesThomasConstantsExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockInverseExact.agda
  DASHI/Physics/YangMills/BalabanP33ConstraintGramD4CovarianceExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSingletonBudgetOptimizationExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundCoefficientFieldExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCorrelatedSingletonClosureExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound40MultiplierLocalityValidation.agda
)

doc=Docs/support/reference/YangMillsMultiplierLocalityRound40.md
index=Docs/support/reference/YangMillsReferenceIndex.md
optimizer=scripts/ym_round40_singleton_budget_optimize.py
fixture=scripts/fixtures/ym_round40_singleton_budget_candidates.json

for file in "${files[@]}" "$doc" "$index" "$optimizer" "$fixture"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported|emptyCoordinate|chooseEmpty|chooseCoordinate' "${files[@]}"; then
  echo "round forty contains a hole, postulate, unsafe escape, trust primitive, imported theorem receipt, or invalid generic selector" >&2
  exit 1
fi

if grep -nE '\((data|field)[[:space:]]*:' "${files[@]}"; then
  echo "round forty uses an Agda reserved keyword as a typed binder" >&2
  exit 1
fi

checks=(
  'BalabanSelectedVariationSignConventionExact.agda:singletonResidualSignExact'
  'BalabanSelectedVariationSignConventionExact.agda:wrongDoubleNegativeWouldForcePairCancellation'
  'BalabanSelectedMultiplierPairingRedundancyInvariantExact.agda:multiplierDefectPairingIgnoresRedundancy'
  'BalabanSelectedMultiplierPairingRedundancyInvariantExact.agda:allKKTMultipliersGiveSameDefect'
  'BalabanSelectedConstraintCollarPairingExact.agda:multiplierPairingRestrictsToConstraintCollar'
  'BalabanSelectedConstraintCollarPairingExact.agda:outsideCollarMultiplierAnnihilatesDefect'
  'BalabanSelectedRawExtractorConstraintDefectAtomsExact.agda:rawExtractorConstraintDefectAtomReconstruction'
  'BalabanSelectedMultiplierDefectGreenContractionExact.agda:selectedMultiplierDefectGreenContractionExact'
  'BalabanSelectedCorrelatedResidualOwnershipExact.agda:correlatedResidualReconstructedFromOwners'
  'BalabanSelectedCorrelatedResidualOwnershipExact.agda:exactCorrelatedCancellationRemovedBeforeMajorisation'
  'BalabanSelectedCorrelatedResidualOwnershipExact.agda:correlatedResidualClosesSingletonBudget'
  'BalabanSelectedConstraintGramCombesThomasExact.agda:selectedConstraintGramTiltBelowHalfGap'
  'BalabanSelectedConstraintGramCombesThomasExact.agda:selectedConstraintGramCombesThomasDecay'
  'BalabanSelectedKKTMultiplierLocalityExact.agda:canonicalMultiplierCollarBound'
  'BalabanP33FiniteKKTBlockCombesThomasConstantsExact.agda:threeBlockNeumannParameterBelowHalf'
  'BalabanP33FiniteKKTBlockCombesThomasConstantsExact.agda:selectedKKTCombesThomasDecay'
  'BalabanP33FiniteKKTBlockInverseExact.agda:finiteKKTKernelTrivial'
  'BalabanP33FiniteKKTBlockInverseExact.agda:finiteKKTRightInverseIsLeftInverse'
  'BalabanP33ConstraintGramD4CovarianceExact.agda:constraintGramCovariantUnderD4'
  'BalabanP33ConstraintGramD4CovarianceExact.agda:multiplierGreenPairingOrbitInvariant'
  'BalabanP33PhysicalSingletonBudgetOptimizationExact.agda:generatedCertificateGivesSymbolicSplit'
  'BalabanP33PhysicalSingletonBudgetOptimizationExact.agda:noFitDualContradictsGeneratedCertificate'
  'BalabanSelectedBackgroundCoefficientFieldExact.agda:rationalFrameAvailableOnlyFromLiteralEntries'
  'BalabanSelectedCorrelatedSingletonClosureExact.agda:selectedBackgroundSingletonLowerFromCorrelatedResidual'
  'BalabanSelectedCorrelatedSingletonClosureExact.agda:selectedBackgroundCorrelatedWilsonLower'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanSelectedVariationSignConventionExact.agda
grep -q '10.1017/S0305004100030401' DASHI/Physics/YangMills/BalabanSelectedMultiplierPairingRedundancyInvariantExact.agda
grep -q '10.1007/BF01211042' DASHI/Physics/YangMills/BalabanSelectedConstraintCollarPairingExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedConstraintGramCombesThomasExact.agda
grep -q '10.1007/BF00531932' DASHI/Physics/YangMills/BalabanSelectedCorrelatedResidualOwnershipExact.agda

grep -q 'RawLocalization - <lambda,Lw>' "$doc"
grep -q '55 / 18874368' "$doc"
grep -q 'genuine two-sided finite KKT inverse' "$index"
grep -Fq '[Round 40 — multiplier locality and correlated singleton residual](./YangMillsMultiplierLocalityRound40.md)' "$index"

certificate="$(mktemp)"
trap 'rm -f "$certificate"' EXIT
python "$optimizer" --input "$fixture" --output "$certificate" --expect fit
grep -q '"status": "fit"' "$certificate"
grep -q '"physicalParameterAssignment": "correlated_owner_bound"' "$certificate"
grep -q '"singletonTotalCostExact": "9/3145728"' "$certificate"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound40MultiplierLocalityValidation.agda
