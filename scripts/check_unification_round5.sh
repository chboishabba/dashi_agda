#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# This physics/constants tranche is stacked directly on PR #399.  Validate the
# complete biology/Yijing/natural-system Round Five before checking the added
# foundations, attached-formalism, collider, junction, renderer, and p-adic
# continuation paths.
if [[ "${UNIFICATION_ROUND5_SKIP_BIOLOGY:-0}" != "1" ]]; then
  bash scripts/check_conscious_access_round5.sh
fi

FILES=(
  DASHI/Physics/Foundations/ParameterScaleTaxonomyExact.agda
  DASHI/Physics/Foundations/ParameterInformationGeometryExact.agda
  DASHI/Physics/Foundations/ScaleInvariantTheorySelectionExact.agda
  DASHI/Physics/Foundations/PadicCausalChartLosslessExact.agda
  DASHI/Physics/Foundations/ModularProjectionQuantisationExact.agda
  DASHI/Physics/Foundations/RGMDLExhaustionChambersExact.agda
  DASHI/Physics/Foundations/DimensionPowerCountingBoundaryExact.agda
  DASHI/Physics/Foundations/DiscreteLorentzEmergenceBoundaryExact.agda
  DASHI/Physics/Foundations/AtomicFermionShellExact.agda
  DASHI/Physics/Foundations/AtomicValenceFermionBridgeExact.agda
  DASHI/Physics/Foundations/AtomicGenerationPipelineExact.agda
  DASHI/Physics/Foundations/NuclearShellPairingExact.agda
  DASHI/Physics/Foundations/NuclearShapeInstabilityExact.agda
  DASHI/Physics/Foundations/NuclearResponseComplexityExact.agda
  DASHI/Physics/Foundations/CausalCodingCosmologyBoundaryExact.agda
  DASHI/Physics/Foundations/CMBInformationChannelExact.agda
  DASHI/Physics/Foundations/KernelGeometryEmergenceObligations.agda
  DASHI/Physics/Foundations/FiniteStressConservationGeodesicExact.agda
  DASHI/Physics/Foundations/FiniteGraphGaugeScalarExact.agda
  DASHI/Physics/Foundations/FiniteFockExcitationExact.agda
  DASHI/Physics/Foundations/KernelQFTEmergenceObligations.agda
  DASHI/Physics/Foundations/KernelEmergenceHypothesesExact.agda
  DASHI/Physics/Foundations/PR399FoundationsCrossPollinationExact.agda
  DASHI/Physics/Foundations/UnifiedEffectiveActionBoundary.agda
  DASHI/Physics/Foundations/FiniteHistoryOrientationExact.agda
  DASHI/Physics/Foundations/HistoryWeightFiltrationExact.agda
  DASHI/Physics/Foundations/FiniteHistoryFunctionalExact.agda
  DASHI/Physics/Foundations/FormalReceiptBoundaryExact.agda
  DASHI/Physics/Foundations/FiniteResidueCycleReachabilityExact.agda
  DASHI/Physics/Foundations/FiniteWeightedTernaryKernelExact.agda
  DASHI/Physics/Foundations/TernaryKernelQuotientLyapunovExact.agda
  DASHI/Physics/Foundations/FiniteMultiscaleKernelCompatibilityExact.agda
  DASHI/Physics/Foundations/FiniteStatisticalFiltrationExact.agda
  DASHI/Physics/Foundations/ProbabilityDecoratedReebExact.agda
  DASHI/Physics/Foundations/FiniteUltrametricReebFlowExact.agda
  DASHI/Physics/Foundations/TriToBiSingularJunctionExact.agda
  DASHI/Physics/Foundations/TriToBiTransportExact.agda
  DASHI/Physics/Foundations/TriToBiPhaseDialecticExact.agda
  DASHI/Physics/Foundations/AttachedFormalismSourceAtlas.agda
  DASHI/Physics/Foundations/Round5AttachedFormalismBoundary.agda
  DASHI/Physics/Foundations/Round5AttachedFormalismRegression.agda
  DASHI/Physics/Foundations/Round5AttachedCompletionBoundary.agda
  DASHI/Physics/Foundations/Round5AttachedCompletionRegression.agda
  DASHI/Physics/DarkSector/SectorCarrier.agda
  DASHI/Physics/DarkSector/GaugeSingletPortal.agda
  DASHI/Physics/DarkSector/HiggsPortalDecay.agda
  DASHI/Physics/DarkSector/MetastableLifetime.agda
  DASHI/Physics/DarkSector/BoostedDecayGeometry.agda
  DASHI/Physics/DarkSector/DisplacedVertex.agda
  DASHI/Physics/DarkSector/TriggerCensoring.agda
  DASHI/Physics/DarkSector/LinkedColliderChainExact.agda
  DASHI/Physics/DarkSector/DarkSectorColliderSourceAtlas.agda
  DASHI/Physics/DarkSector/DarkSectorColliderBoundary.agda
  DASHI/Physics/DarkSector/DarkSectorColliderRegression.agda
  DASHI/Physics/DarkSector/Everything.agda
  DASHI/Biology/TernaryCyclicDialecticExact.agda
  DASHI/Biology/TernarySoftCarryLogicExact.agda
  DASHI/Biology/TernaryLogicRelaxationSourceAtlas.agda
  DASHI/Biology/RenderablePadicReasoningFieldExact.agda
  DASHI/Biology/PadicLODConsistencyExact.agda
  DASHI/Biology/PadicRenderModeCorrectionExact.agda
  DASHI/Visualisation/AffinePlaneSliceExact.agda
  DASHI/Visualisation/FiveClassSimplexColourExact.agda
  DASHI/Visualisation/SliceObjectiveExact.agda
  DASHI/Visualisation/ColourProjectionDiagnosticsExact.agda
  DASHI/Visualisation/CoarseSliceSearchExact.agda
  DASHI/Visualisation/QuantisedSearchBoundsExact.agda
  DASHI/Visualisation/RendererParityExact.agda
  DASHI/Visualisation/RendererReceiptExact.agda
  DASHI/Visualisation/GraphSeriesSemanticExact.agda
  DASHI/Visualisation/MeasureFieldAdapterExact.agda
  DASHI/Visualisation/AdapterCommutationExact.agda
  DASHI/Visualisation/AttachedVisualisationSourceAtlas.agda
  DASHI/Visualisation/AttachedVisualisationBoundary.agda
  DASHI/Visualisation/AttachedVisualisationRegression.agda
  DASHI/Visualisation/EventFilamentFieldExact.agda
  DASHI/Visualisation/EventSeparationQuantisationExact.agda
  DASHI/Visualisation/EventSeparationQuantisationRegression.agda
  DASHI/Visualisation/EventLabelGeometryExact.agda
  DASHI/Visualisation/FiniteAnisotropicKernelExact.agda
  DASHI/Visualisation/EventFilamentPersistenceExact.agda
  DASHI/Visualisation/SelfConsistentEventRendererExact.agda
  DASHI/Visualisation/RendererStabilityExact.agda
  DASHI/Visualisation/EventPadicSourceAtlas.agda
  DASHI/Visualisation/EventPadicContinuationBoundary.agda
  DASHI/Visualisation/EventPadicContinuationRegression.agda
  DASHI/Visualisation/Everything.agda
  DASHI/Physics/Foundations/Round5SourceAtlas.agda
  DASHI/Physics/Foundations/Round5CombinedSourceBoundary.agda
  DASHI/Physics/Foundations/Round5CompletionRegression.agda
  DASHI/Physics/Foundations/Round5FullBoundary.agda
  DASHI/Physics/Foundations/Round5CompleteBoundary.agda
  DASHI/Physics/Foundations/Round5Regression.agda
  DASHI/Physics/Foundations/Everything.agda
  DASHI/Biology/Everything.agda
  DASHI/Unified/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required unification round-five source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/Round5AttachedFormalismRegression.agda \
  DASHI/Physics/Foundations/Round5AttachedCompletionRegression.agda \
  DASHI/Visualisation/AttachedVisualisationRegression.agda \
  DASHI/Visualisation/EventSeparationQuantisationRegression.agda \
  DASHI/Visualisation/EventPadicContinuationRegression.agda \
  DASHI/Visualisation/Everything.agda \
  DASHI/Physics/Foundations/Round5CompleteBoundary.agda \
  DASHI/Physics/DarkSector/DarkSectorColliderRegression.agda \
  DASHI/Physics/DarkSector/Everything.agda \
  DASHI/Physics/Foundations/Round5Regression.agda \
  DASHI/Physics/Foundations/Everything.agda \
  DASHI/Biology/Everything.agda \
  DASHI/Unified/Everything.agda
