#!/usr/bin/env bash
set -euo pipefail

repo_root="${DASHI_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
cd "$repo_root"

files=(
  DASHI/Core/ProvenanceBearingQuotient.agda
  DASHI/Core/AdmissibleReachability.agda
  DASHI/Core/DynamicalQuotientSafety.agda
  DASHI/Core/ProvenanceQuotientDynamics.agda
  DASHI/Core/PossibilityAccessibilitySupport.agda
  DASHI/Core/ConsumerIndexedRelevanceMeasure.agda
  DASHI/Core/ConsumerProjectionSufficiency.agda
  DASHI/Core/FinePhaseObservation.agda
  DASHI/Core/RelationalHorizon369.agda
  DASHI/Core/StructuralSupportEdge.agda
  DASHI/Core/ClassificationEdge.agda
  DASHI/Foundations/DepthWheelGradedDynamics.agda
  DASHI/Foundations/CantorConsumerRelevanceReference.agda
  DASHI/Cognition/PNF/BoundedExecutionCarrier.agda
  DASHI/Cognition/PNF/BoundedExecutionAdapters.agda
  DASHI/Cognition/PNF/ReopenableEvidenceFibre.agda
  DASHI/Cognition/PNF/ParserArgumentSupportGluing.agda
  DASHI/Cognition/PNF/SupportClassificationIdentitySpine.agda
  DASHI/Cognition/PNF/ContextualRepresentationOrbit.agda
  DASHI/Cognition/PNF/EvidenceClassificationEdge.agda
  DASHI/Cognition/PNF/TypePressure.agda
  DASHI/Cognition/PNF/EvidencePhaseObservationAdapter.agda
  DASHI/Cognition/PNF/EvidenceHorizon369.agda
  DASHI/Cognition/PNF/EvidenceDepthWheelOrthogonality.agda
  DASHI/Cognition/PNF/LexicalRetrievalProjection.agda
  DASHI/Cognition/PNF/NumericTokenStorageReference.agda
  DASHI/Cognition/PNF/SemanticSamplingLookupGeometry.agda
  DASHI/Cognition/PNF/SemanticSamplingDynamicSafety.agda
  DASHI/Cognition/PNF/TerminalisationDefectRegression.agda
  DASHI/Cognition/PNF/PNFResidualTerminalisationRegression.agda
  DASHI/Cognition/PNF/RelevanceMassDynamicSafetyRegression.agda
  DASHI/Cognition/PNF/TemporalRoleWorldAlignment.agda
  DASHI/Cognition/PNF/WikidataRepairProposal.agda
  DASHI/Cognition/PNF/IdentityProofUtility.agda
  DASHI/Cognition/PNF/InductiveDemandPreference.agda
  DASHI/Cognition/PNF/NumericOccurrenceFibre.agda
  DASHI/Cognition/PNF/EvidenceCoverageAudit.agda
  DASHI/Cognition/PNF/PNFEvidenceHyperformalism.agda
  DASHI/Cognition/PNF/DirectDemandLookup.agda
  DASHI/Cognition/PNF/RuntimeThroughputConstitution.agda
  DASHI/Cognition/PNF/NumericHotPathConstitution.agda
  DASHI/Cognition/PNF/CorpusLearningEconomy.agda
  DASHI/Cognition/PNF/ContextualWorldCache.agda
  DASHI/Cognition/PNF/RelativeOctantAddressReference.agda
  DASHI/Cognition/PNF/LazyHorizonIncrementalExecution.agda
  DASHI/Cognition/PNF/FrequencyAdaptiveSymbolCode.agda
  DASHI/Cognition/PNF/HotColdExecutionProjection.agda
  DASHI/Cognition/PNF/WorkloadGranularityReference.agda
  DASHI/Cognition/PNF/StructuralSupportSelectivity.agda
  DASHI/Cognition/PNF/NumericPNFHyperfabricEverything.agda
  DASHI/Cognition/PNF/DepthWheelMemoryHyperfabric.agda
  DASHI/Cognition/PNF/DepthWheelMemoryPhaseGeometry.agda
  DASHI/Cognition/PNF/DepthWheelMemoryGradedAdapter.agda
  DASHI/Physics/Closure/SSPPrimeLane369DepthWheelCantorBridge.agda
  DASHI/Physics/Closure/SSPPrimeLane369DepthAddressWheel.agda
  DASHI/Physics/Closure/SSP369PolarResidualQuotient.agda
  DASHI/Geometry/SSP369DepthWheelUltrametric.agda
)

for file in "${files[@]}"; do
  test -f "$file" || { echo "missing required file: $file" >&2; exit 1; }
done

if grep -nE '(postulate|\{!|!\}|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|--allow-unsolved-metas|--type-in-type|--with-K)' "${files[@]}"; then
  echo "unsafe or unfinished Agda construct found in ITIR reopenable-evidence tranche" >&2
  exit 1
fi

required_markers=(
  'ProvenanceBearingQuotient'
  'TerminalisationDefect'
  'ConsumerIndexedRelevanceMeasure'
  'WorldCoverageWitness'
  'ConsumerSafeCompression'
  'StructuralSupportEdge'
  'ClassificationEdge'
  'ReopenableExecutionPartition'
  'ConsumerMeasuredReopenableExecutionPartition'
  'supportAloneCannotCreateIdentity'
  'pressureAloneCannotAssertType'
  'horizonExpansionCommutesWithDepthAdvance'
  'regexHasNoSemanticAuthority'
  'decodeEncode'
  'ResolvedRoleTimeDemand'
  'repairProposalCannotAssertOntologyTruth'
  'inductivePreferenceCannotProjectScalarIdentity'
  'ParserDominatedOptimisationReceipt'
  'ArchiveScaleReceipt'
  'regexCannotEnterSemanticHotPath'
  'NumericAutomatonReceipt'
  'workWithinLinearPlusMatches'
  'learningCannotIncreaseDeclaredWorkBound'
  'cacheSizeAloneDoesNotProveRuntimeImprovement'
  'cachedLabelCannotPromoteOneWorldEntity'
  'missingContextDoesNotRefuteCandidate'
  'decodeEncodeOctant'
  'oneOctantDigitDoesNotProveOneByteWholeCell'
  'h6ConsumesExactlyH3Residual'
  'h9ConsumesExactlyH6Residual'
  'recomputedExactlyAffected'
  'absenceOfEvidenceCannotRefute'
  'frequencyRankCannotChangeSemanticIdentity'
  'maintainedEqualsRebuilt'
  'tokensArePrimaryCrossDocumentScaleIsTrue'
  'StructuralSupportFanoutReceipt'
  'supportMayBeBuiltAsUnboundedTokenObjectCrossProductIsFalse'
)

for marker in "${required_markers[@]}"; do
  if ! grep -Rqs --include='*.agda' "$marker" DASHI; then
    echo "missing required theorem/boundary marker: $marker" >&2
    exit 1
  fi
done

export AGDA_FLAKE="${AGDA_FLAKE:-github:agda/agda/86a1179c1f886da773dc53be920bcca5d876884e#debug.bin}"
export AGDA_JOBS="${AGDA_JOBS:-2}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/NumericPNFHyperfabricEverything.agda
