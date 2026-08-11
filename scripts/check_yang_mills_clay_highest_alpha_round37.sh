#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round36.sh

sources_repair=(
  DASHI/Physics/YangMills/BalabanSelectedPlaquetteLinearRepairModelExact.agda
  DASHI/Physics/YangMills/BalabanSelectedPlaquetteResidualBudgetRound37Exact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonGateSignatureRound37Exact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound37RepairSelectorValidation.agda
)

for source in "${sources_repair[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'selectedPlaquetteVariation'
  'selectedPlaquetteVariationGaugeAdmissible'
  'selectedPlaquetteVariationConstraintTangent'
  'selectedPlaquetteVariationExtractsSingleton'
  'selectedPlaquetteVariationChargeExact'
  'selectLinearPlaquetteVariation'
  'residualCoefficientLedgerExact'
  'selectedVariationSpilloverUpper'
  'covariantTransportAtom'
  'physicalCovariantPrefixTransportConstructedIsFalse'
  'GateISignature'
  'singletonIsLowerDegreeButOpen'
  'pairIsHigherDegreeButFiniteClosed'
  'oppositePairOrbitIsDistinguished'
  'physicalPrefixActionProvesTheseOrbitClassesIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources_repair[@]}" >/dev/null
done

files_projector=(
  DASHI/Physics/YangMills/BalabanP33PhysicalCoordinateProjectorExact.agda
  DASHI/Physics/YangMills/BalabanP33PlaquetteBoundaryProjectorExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalProjectorCompositionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedVariationProjectionSpilloverExact.agda
  DASHI/Physics/YangMills/BalabanSelectedVariationProjectedNoetherResidualExact.agda
  DASHI/Physics/YangMills/BalabanSelectedVariationProjectedSelectorAssemblyExact.agda
  DASHI/Physics/YangMills/BalabanP33PlaquetteOrientationReversalExact.agda
  DASHI/Physics/YangMills/BalabanWilsonSixteenAtomCentredProbeExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralHessianSpectralCertificateExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalStateDualTiltExact.agda
  DASHI/Physics/YangMills/BalabanP33StrictOwnedMarginExact.agda
  DASHI/Physics/YangMills/BalabanE8QuantitativeRootDataExact.agda
  DASHI/Physics/YangMills/BalabanCommon196608AtlasExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound37ProjectorResidualValidation.agda
)

doc=Docs/support/reference/YangMillsProjectorResidualRound37.md
index=Docs/support/reference/YangMillsReferenceIndex.md

for file in "${files_projector[@]}" "$doc" "$index"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files_projector[@]}"; then
  echo "round thirty seven contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanP33PhysicalCoordinateProjectorExact.agda:physicalConstraintProjectorIdempotent'
  'BalabanP33PhysicalCoordinateProjectorExact.agda:physicalConstraintProjectorSelfAdjoint'
  'BalabanP33PhysicalCoordinateProjectorExact.agda:physicalConstrainedResolutionOfIdentity'
  'BalabanP33PhysicalCoordinateProjectorExact.agda:projectedLiteralHessianMatrixRepresentsForm'
  'BalabanP33PlaquetteBoundaryProjectorExact.agda:plaquetteBoundaryMask'
  'BalabanP33PlaquetteBoundaryProjectorExact.agda:rawPlaquetteSingletonExtractor'
  'BalabanP33PlaquetteBoundaryProjectorExact.agda:rawPlaquetteSingletonExtractorLocal'
  'BalabanP33PhysicalProjectorCompositionExact.agda:physicalCoordinateProjectorsCommute'
  'BalabanP33PhysicalProjectorCompositionExact.agda:triplePhysicalConstraintProjectorIdempotent'
  'BalabanSelectedVariationProjectionSpilloverExact.agda:firstVariationRawSplitsProjectedDiscarded'
  'BalabanSelectedVariationProjectionSpilloverExact.agda:projectedFirstVariationIsRawMinusDiscarded'
  'BalabanSelectedVariationProjectionSpilloverExact.agda:projectedExtractionSpilloverUpper'
  'BalabanSelectedVariationProjectedNoetherResidualExact.agda:selectedVariationResidualStationary'
  'BalabanSelectedVariationProjectedNoetherResidualExact.agda:projectedConstructionToSingletonWitness'
  'BalabanSelectedVariationProjectedNoetherResidualExact.agda:projectedFamilyToSelectedBackgroundVariationSelector'
  'BalabanSelectedVariationProjectedSelectorAssemblyExact.agda:analyticDataToProjectedSingletonConstruction'
  'BalabanSelectedVariationProjectedSelectorAssemblyExact.agda:analyticDataToSingletonExtractionWitness'
  'BalabanSelectedVariationProjectedSelectorAssemblyExact.agda:analyticFamilyToSelectedBackgroundVariationSelector'
  'BalabanP33PlaquetteOrientationReversalExact.agda:reverseQuaternionMultiply'
  'BalabanP33PlaquetteOrientationReversalExact.agda:reverseSubsetAtomExact'
  'BalabanP33PlaquetteOrientationReversalExact.agda:reverseWilsonScalarInvariant'
  'BalabanWilsonSixteenAtomCentredProbeExact.agda:sixteenAtomCentredProbeExact'
  'BalabanWilsonSixteenAtomCentredProbeExact.agda:uniformWeightsSeeOnlyAugmentation'
  'BalabanP33LiteralHessianSpectralCertificateExact.agda:eigenpairQuadraticExact'
  'BalabanP33LiteralHessianSpectralCertificateExact.agda:p33NoNormalizedZeroEigenvector'
  'BalabanP33PhysicalStateDualTiltExact.agda:tiltedHessianDifferenceEntryExact'
  'BalabanP33StrictOwnedMarginExact.agda:maximalUniformCoerciveCore'
  'BalabanP33StrictOwnedMarginExact.agda:strictMarginAfterErasingOwners'
  'BalabanE8QuantitativeRootDataExact.agda:e8RankPlusExpectedRootsIsAdjointDimension'
  'BalabanCommon196608AtlasExact.agda:yangMillsChartIs196608'
  'BalabanCommon196608AtlasExact.agda:phaseChartIs196608'
  'BalabanCommon196608AtlasExact.agda:leechChartIs196608'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1017/S096249290100006X' DASHI/Physics/YangMills/BalabanSelectedVariationProjectionSpilloverExact.agda
grep -q '10.1016/S0022-1236(03)00057-0' DASHI/Physics/YangMills/BalabanP33PhysicalProjectorCompositionExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanP33PhysicalStateDualTiltExact.agda
grep -q '10.1007/978-3-642-66282-9' DASHI/Physics/YangMills/BalabanP33LiteralHessianSpectralCertificateExact.agda
grep -q '10.1007/978-1-4757-6568-7' DASHI/Physics/YangMills/BalabanE8QuantitativeRootDataExact.agda
grep -q '10.1112/blms/11.3.308' DASHI/Physics/YangMills/BalabanCommon196608AtlasExact.agda

grep -q 'projector-defect pairing' "$doc"
grep -q '55/18874368' "$doc"
grep -q 'expected-count' "$doc"
grep -q '24 \* 8192' "$doc"
grep -Fq '[Round 37 — physical projectors, Noether residuals and spillover decomposition](./YangMillsProjectorResidualRound37.md)' "$index"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound37RepairSelectorValidation.agda \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound37ProjectorResidualValidation.agda
