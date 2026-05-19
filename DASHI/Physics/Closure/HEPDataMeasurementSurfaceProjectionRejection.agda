module DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataEmpiricalSourceCandidateDiagnostic as HEP

------------------------------------------------------------------------
-- HEP-D: MeasurementSurface -> DashiState typed rejection.
--
-- This module does not implement projection and does not promote empirical
-- evidence.  It records the current contract state: local HEPData source
-- candidates exist, but the semantic, metric, transform, failure, and
-- authority receipts required for theorem-side projection are still absent.

data ProjectionEndpoint : Set where
  measurementSurfaceEndpoint :
    ProjectionEndpoint
  dashiStateSchemaEndpoint :
    ProjectionEndpoint
  theoremSideDeltaStateEndpoint :
    ProjectionEndpoint

data CurrentProjectionContractStatus : Set where
  rejectedMissingProjectionContract :
    CurrentProjectionContractStatus

data DeclaredTransform : Set where
  raw :
    DeclaredTransform
  gradient :
    DeclaredTransform
  whitened :
    DeclaredTransform
  other-declared :
    DeclaredTransform

data MetricGeometryEffect : Set where
  preservesMetricGeometry :
    MetricGeometryEffect
  changesMetricFrame :
    MetricGeometryEffect
  noDefaultMetricGeometryClaim :
    MetricGeometryEffect

data RegularizationRequirement : Set where
  noRegularizationRequired :
    RegularizationRequirement
  regularizationRequiredWhenCovarianceNotInvertible :
    RegularizationRequirement
  noDefaultRegularizationClaim :
    RegularizationRequirement

data ComparableGroup : Set where
  nativeGroup :
    ComparableGroup
  derivedGroup :
    ComparableGroup
  normalizedGroup :
    ComparableGroup
  declaredOtherGroup :
    ComparableGroup

data DownstreamUsePermission : Set where
  exploratoryOnlyUntilPromoted :
    DownstreamUsePermission
  requiresDerivativeCovariancePropagationLaw :
    DownstreamUsePermission
  comparisonOnlyWithinWhitenedFrame :
    DownstreamUsePermission
  noDownstreamUseByDefault :
    DownstreamUsePermission

record TransformVocabularyEntry : Set where
  field
    transform :
      DeclaredTransform

    metricGeometryEffect :
      MetricGeometryEffect

    regularizationRequirement :
      RegularizationRequirement

    comparableGroup :
      ComparableGroup

    downstreamUsePermission :
      DownstreamUsePermission

    meaning :
      String

rawTransformEntry :
  TransformVocabularyEntry
rawTransformEntry =
  record
    { transform =
        raw
    ; metricGeometryEffect =
        preservesMetricGeometry
    ; regularizationRequirement =
        noRegularizationRequired
    ; comparableGroup =
        nativeGroup
    ; downstreamUsePermission =
        exploratoryOnlyUntilPromoted
    ; meaning =
        "use observed y as the candidate signal without reparameterizing the carrier"
    }

gradientTransformEntry :
  TransformVocabularyEntry
gradientTransformEntry =
  record
    { transform =
        gradient
    ; metricGeometryEffect =
        noDefaultMetricGeometryClaim
    ; regularizationRequirement =
        noRegularizationRequired
    ; comparableGroup =
        derivedGroup
    ; downstreamUsePermission =
        requiresDerivativeCovariancePropagationLaw
    ; meaning =
        "use local variation of y over ordered x as the candidate signal"
    }

whitenedTransformEntry :
  TransformVocabularyEntry
whitenedTransformEntry =
  record
    { transform =
        whitened
    ; metricGeometryEffect =
        changesMetricFrame
    ; regularizationRequirement =
        regularizationRequiredWhenCovarianceNotInvertible
    ; comparableGroup =
        normalizedGroup
    ; downstreamUsePermission =
        comparisonOnlyWithinWhitenedFrame
    ; meaning =
        "use covariance-normalized coordinates with an explicit whitening operator"
    }

otherDeclaredTransformEntry :
  TransformVocabularyEntry
otherDeclaredTransformEntry =
  record
    { transform =
        other-declared
    ; metricGeometryEffect =
        noDefaultMetricGeometryClaim
    ; regularizationRequirement =
        noDefaultRegularizationClaim
    ; comparableGroup =
        declaredOtherGroup
    ; downstreamUsePermission =
        noDownstreamUseByDefault
    ; meaning =
        "use a lane-specific transform only after explicit declaration"
    }

canonicalDeclaredTransformVocabulary :
  List TransformVocabularyEntry
canonicalDeclaredTransformVocabulary =
  rawTransformEntry
  ∷ gradientTransformEntry
  ∷ whitenedTransformEntry
  ∷ otherDeclaredTransformEntry
  ∷ []

data ProjectionResultState : Set where
  projectionOk :
    ProjectionResultState
  projectionDegraded :
    ProjectionResultState
  projectionRejected :
    ProjectionResultState
  projectionAbstained :
    ProjectionResultState

canonicalProjectionResultStates :
  List ProjectionResultState
canonicalProjectionResultStates =
  projectionOk
  ∷ projectionDegraded
  ∷ projectionRejected
  ∷ projectionAbstained
  ∷ []

data ProjectionFailureOrAbstentionState : Set where
  shapeInvalidFailure :
    ProjectionFailureOrAbstentionState
  covarianceUnavailableFailure :
    ProjectionFailureOrAbstentionState
  covarianceRankDeficientFailure :
    ProjectionFailureOrAbstentionState
  illConditionedMetricFailure :
    ProjectionFailureOrAbstentionState
  undeclaredTransformFailure :
    ProjectionFailureOrAbstentionState
  silentWhiteningFailure :
    ProjectionFailureOrAbstentionState
  silentCovarianceDropFailure :
    ProjectionFailureOrAbstentionState
  abstainMissingDeltaMeaning :
    ProjectionFailureOrAbstentionState
  abstainMissingCoarseHeadMeaning :
    ProjectionFailureOrAbstentionState
  abstainMissingMetricPropagationLaw :
    ProjectionFailureOrAbstentionState
  abstainMissingAuthorityReceipt :
    ProjectionFailureOrAbstentionState

canonicalFailureAndAbstentionStates :
  List ProjectionFailureOrAbstentionState
canonicalFailureAndAbstentionStates =
  shapeInvalidFailure
  ∷ covarianceUnavailableFailure
  ∷ covarianceRankDeficientFailure
  ∷ illConditionedMetricFailure
  ∷ undeclaredTransformFailure
  ∷ silentWhiteningFailure
  ∷ silentCovarianceDropFailure
  ∷ abstainMissingDeltaMeaning
  ∷ abstainMissingCoarseHeadMeaning
  ∷ abstainMissingMetricPropagationLaw
  ∷ abstainMissingAuthorityReceipt
  ∷ []

data ProjectionContractRequirementGap : Set where
  missingSemanticDeltaMeaning :
    ProjectionContractRequirementGap
  missingSemanticCoarseHeadMeaning :
    ProjectionContractRequirementGap
  missingCovarianceMetricPropagationLaw :
    ProjectionContractRequirementGap
  missingSelectedTransformVocabularyCommitment :
    ProjectionContractRequirementGap
  missingPerTransformDiagnostics :
    ProjectionContractRequirementGap
  missingFailureAndAbstentionSemantics :
    ProjectionContractRequirementGap
  missingProjectionToTheoremSideCarrier :
    ProjectionContractRequirementGap
  missingTheoremSidePromotionAuthority :
    ProjectionContractRequirementGap

canonicalProjectionContractRequirementGaps :
  List ProjectionContractRequirementGap
canonicalProjectionContractRequirementGaps =
  missingSemanticDeltaMeaning
  ∷ missingSemanticCoarseHeadMeaning
  ∷ missingCovarianceMetricPropagationLaw
  ∷ missingSelectedTransformVocabularyCommitment
  ∷ missingPerTransformDiagnostics
  ∷ missingFailureAndAbstentionSemantics
  ∷ missingProjectionToTheoremSideCarrier
  ∷ missingTheoremSidePromotionAuthority
  ∷ []

data TheoremSideMeasurementSurfaceProjectionReceipt : Set where

theoremSideProjectionReceiptImpossibleHere :
  TheoremSideMeasurementSurfaceProjectionReceipt →
  ⊥
theoremSideProjectionReceiptImpossibleHere ()

record HEPDataMeasurementSurfaceProjectionRejection : Setω where
  field
    sourceEndpoint :
      ProjectionEndpoint

    targetEndpoint :
      ProjectionEndpoint

    currentStatus :
      CurrentProjectionContractStatus

    currentResultState :
      ProjectionResultState

    sourceCandidateDiagnostic :
      HEP.HEPDataEmpiricalSourceCandidateDiagnostic

    sourceCandidatesStillNonPromoting :
      HEP.HEPDataEmpiricalSourceCandidateDiagnostic.candidateStatus
        sourceCandidateDiagnostic
      ≡
      HEP.sourceCandidatesPresentButNonPromoting

    sourceMissingSurfaces :
      List HEP.HEPDataBridgeMissingSurface

    sourceMissingSurfacesStillCanonical :
      sourceMissingSurfaces
      ≡
      HEP.canonicalHEPDataBridgeMissingSurfaces

    measurementToDashiProjectionKnownMissing :
      Bool

    metricPropagationKnownMissing :
      Bool

    declaredTransformVocabulary :
      List TransformVocabularyEntry

    declaredTransformVocabularyIsCanonical :
      declaredTransformVocabulary
      ≡
      canonicalDeclaredTransformVocabulary

    allowedResultStates :
      List ProjectionResultState

    allowedResultStatesAreCanonical :
      allowedResultStates
      ≡
      canonicalProjectionResultStates

    failureAndAbstentionStates :
      List ProjectionFailureOrAbstentionState

    failureAndAbstentionStatesAreCanonical :
      failureAndAbstentionStates
      ≡
      canonicalFailureAndAbstentionStates

    requirementGaps :
      List ProjectionContractRequirementGap

    requirementGapsAreCanonical :
      requirementGaps
      ≡
      canonicalProjectionContractRequirementGaps

    deltaMeaningStatus :
      String

    coarseHeadMeaningStatus :
      String

    covarianceMetricPropagationStatus :
      String

    transformVocabularyStatus :
      String

    failureAbstentionStatus :
      String

    sourceCandidateNonProjectionReasons :
      List String

    nonPromotionBoundary :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

    noTheoremSideProjectionReceiptHere :
      TheoremSideMeasurementSurfaceProjectionReceipt →
      ⊥

canonicalHEPDataMeasurementSurfaceProjectionRejection :
  HEPDataMeasurementSurfaceProjectionRejection
canonicalHEPDataMeasurementSurfaceProjectionRejection =
  record
    { sourceEndpoint =
        measurementSurfaceEndpoint
    ; targetEndpoint =
        dashiStateSchemaEndpoint
    ; currentStatus =
        rejectedMissingProjectionContract
    ; currentResultState =
        projectionRejected
    ; sourceCandidateDiagnostic =
        HEP.canonicalHEPDataEmpiricalSourceCandidateDiagnostic
    ; sourceCandidatesStillNonPromoting =
        refl
    ; sourceMissingSurfaces =
        HEP.canonicalHEPDataBridgeMissingSurfaces
    ; sourceMissingSurfacesStillCanonical =
        refl
    ; measurementToDashiProjectionKnownMissing =
        true
    ; metricPropagationKnownMissing =
        true
    ; declaredTransformVocabulary =
        canonicalDeclaredTransformVocabulary
    ; declaredTransformVocabularyIsCanonical =
        refl
    ; allowedResultStates =
        canonicalProjectionResultStates
    ; allowedResultStatesAreCanonical =
        refl
    ; failureAndAbstentionStates =
        canonicalFailureAndAbstentionStates
    ; failureAndAbstentionStatesAreCanonical =
        refl
    ; requirementGaps =
        canonicalProjectionContractRequirementGaps
    ; requirementGapsAreCanonical =
        refl
    ; deltaMeaningStatus =
        "semantic meaning of delta is undeclared for MeasurementSurface-derived HEPData payloads"
    ; coarseHeadMeaningStatus =
        "semantic meaning of coarse_head is only a DashiStateSchema field and is not derived from MeasurementSurface"
    ; covarianceMetricPropagationStatus =
        "covariance exists on MeasurementSurface, but no metric propagation law to DashiState or theorem-side delta is declared"
    ; transformVocabularyStatus =
        "raw, gradient, whitened, and other-declared are vocabulary entries only; no selected transform may imply projection"
    ; failureAbstentionStatus =
        "ok/degraded/rejected/abstained are contract states; the current theorem-side result is rejected"
    ; sourceCandidateNonProjectionReasons =
        "HEPData source candidates terminate at MeasurementSurface packaging"
        ∷ "candidate diagnostics still list missing MeasurementSurface -> DashiState projection"
        ∷ "candidate diagnostics still list missing projection metric propagation law"
        ∷ "candidate diagnostics still list missing unit/dimension, comparison law, checksum, conformance tests, authority adapter, accepted authority token, W3 receipt, and W8 receipt"
        ∷ "the current HEPData bridge is source availability, not theorem-side empirical compatibility"
        ∷ []
    ; nonPromotionBoundary =
        "This module constructs no MeasurementSurface -> DashiState function"
        ∷ "This module constructs no delta_state, no DashiStateSchema, and no theorem-side delta carrier"
        ∷ "This module constructs no W3 accepted-authority receipt and no W8 origin-promotion receipt"
        ∷ "This module performs no empirical promotion and no projection implementation"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-D\\nprojection rejection\\nMeasurementSurface -> DashiState\\ntyped diagnostic\\nno theorem promotion\" as HEPDATA_HEPD #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_W0 --> HEPDATA_HEPD : projection contract typed rejection\nHEPDATA_HEPD --> Plateau : semantic delta/coarse_head + metric law + authority still required\nHEPDATA_HEPD --> W3 : no empirical adequacy promotion"
    ; noTheoremSideProjectionReceiptHere =
        theoremSideProjectionReceiptImpossibleHere
    }
