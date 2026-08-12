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
  DASHI/Core/FinePhaseObservation.agda
  DASHI/Core/RelationalHorizon369.agda
  DASHI/Core/StructuralSupportEdge.agda
  DASHI/Core/ClassificationEdge.agda
  DASHI/Foundations/DepthWheelGradedDynamics.agda
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
  DASHI/Cognition/PNF/TemporalRoleWorldAlignment.agda
  DASHI/Cognition/PNF/WikidataRepairProposal.agda
  DASHI/Cognition/PNF/IdentityProofUtility.agda
  DASHI/Cognition/PNF/InductiveDemandPreference.agda
  DASHI/Cognition/PNF/NumericOccurrenceFibre.agda
  DASHI/Cognition/PNF/EvidenceCoverageAudit.agda
  DASHI/Cognition/PNF/PNFEvidenceHyperformalism.agda
  DASHI/Cognition/PNF/DirectDemandLookup.agda
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

# Fail closed on explicit trust escapes / hole blocks. Bare question marks are
# left to Agda itself because '?' is ordinary prose in comments.
if grep -nE '(postulate|\{!|!\}|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|--allow-unsolved-metas|--type-in-type|--with-K)' "${files[@]}"; then
  echo "unsafe or unfinished Agda construct found in ITIR reopenable-evidence tranche" >&2
  exit 1
fi

required_markers=(
  'ProvenanceBearingQuotient'
  'reopenExact'
  'projectionReceiptCannotEraseSemantics'
  'reopenPolarProjectExact'
  'polarResidualQuotient'
  'DynamicConsumerSafety'
  'TerminalisationDefect'
  'terminalisationDefectContradictsSafety'
  'ReopenableButDynamicallyUnsafe'
  'CorrectiveReachability'
  'PossibilityAccessibilitySupport'
  'PhaseObservationSystem'
  'coarsePhaseDoesNotReconstructFineEvidence'
  'evidenceCoordinatePhaseObservation'
  'RelationalHorizon369Boundary'
  'genericRelationalHorizonCoreReusedIsTrue'
  'StructuralSupportEdge'
  'canonicalStructuralSupportCoreReusedIsTrue'
  'ClassificationEdge'
  'canonicalClassificationCoreReusedIsTrue'
  'classificationEdgeFromTypePressure'
  'executionOverflowHasNoSemanticPermission'
  'ReopenableExecutionPartition'
  'residualExecutionStateCannotRejectSemantics'
  'properNameCarrierAsGeneric'
  'compositionCarrierAsGeneric'
  'semanticRefutationRequiresIndexedEvidenceIsTrue'
  'canonicalReachabilityCoreReusedIsTrue'
  'supportAloneCannotCreateIdentity'
  'supportCommutesWithCoarsening'
  'candidateClassificationCannotPromoteIdentity'
  'classificationRevision'
  'pressureAloneCannotAssertType'
  'envelopeClassification'
  'orbitRelationAloneCannotPromoteIdentity'
  'freeActionAssumedIsFalse'
  'coarsePhaseAssignedWithoutFineSignedWitnessIsFalse'
  'coarsenThenProject6to3EqualsProjectThenCoarsen'
  'coarsenThenProject9to6EqualsProjectThenCoarsen'
  'horizonExpansionCommutesWithDepthAdvance'
  'constantGradedWheel'
  'gradedMemoryLearningSystem'
  'phase0OneWheelUnderlyingState'
  'gradeMayBeForgottenWithoutSafetyProofIsFalse'
  'h9PresenceAloneCannotPromoteWorldIdentity'
  'regexHasNoSemanticAuthority'
  'outputDoesNotExceedInput'
  'decodeEncode'
  'multiscaleStorageJoinSplitExact'
  'numberTheoryAloneDoesNotSelectPhysicalLayout'
  'queryCommutationIsClassicalNyquistTheoremIsFalse'
  'neighbourhoodProposalCannotAdmitIdentity'
  'staticQuerySufficiencyDoesNotSupplyDynamicSafety'
  'depthPhaseTerminalisationDefect'
  'extinctionActionTerminalisationDefect'
  'residualProjectionTerminalisationDefect'
  'ResolvedRoleTimeDemand'
  'localRoleResolutionDoesNotRequireWorldAuthority'
  'externalCandidateAloneCannotPromoteWorldIdentity'
  'repairProposalCannotAssertOntologyTruth'
  'identityProofDoesNotImplyFactorApplicability'
  'inductivePreferenceCannotProjectScalarIdentity'
  'sharedSurfaceDoesNotIdentifyOccurrences'
  'distinctPropositionsWithinWitnessRows'
  'factorStageWithinAdmittedStage'
  'lowCoverageInvalidatesAnOtherwiseValidIdentityProofIsFalse'
  'finiteReferenceDoesNotPromoteUniversalPQJ'
  'ComplementaryReadingReference'
  'expectedConstantEqualityClaimRequiresContract'
  'prefixPartitionClaimRequiresContract'
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
