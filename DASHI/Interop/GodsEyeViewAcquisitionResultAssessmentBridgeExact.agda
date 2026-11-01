module DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact as ABI
import DASHI.Interop.GodsEyeViewExecutableWorldResearchLoopExact as Loop

------------------------------------------------------------------------
-- RUNTIME ACQUISITION RESULT -> SEMANTIC ASSESSMENT
--
-- Transport success is only admission to assessment.  Semantic payment still
-- requires source/content inspection, same-object, temporal, coverage,
-- contradiction, authority and applicability work on the returned carrier.
------------------------------------------------------------------------

executionAllowsSemanticAssessment : ABI.AcquisitionExecutionStatus → Bool
executionAllowsSemanticAssessment ABI.executedWithOutput = true
executionAllowsSemanticAssessment ABI.executedNoMatch = false
executionAllowsSemanticAssessment ABI.blockedBeforeExecution = false
executionAllowsSemanticAssessment ABI.providerUnavailable = false
executionAllowsSemanticAssessment ABI.executionFailed = false

executedOutputAllowsAssessment :
  executionAllowsSemanticAssessment ABI.executedWithOutput ≡ true
executedOutputAllowsAssessment = refl

noMatchDoesNotPretendToBeEvidence :
  executionAllowsSemanticAssessment ABI.executedNoMatch ≡ false
noMatchDoesNotPretendToBeEvidence = refl

record AcquisitionSemanticAssessment
    (request : ABI.RuntimeNeutralAcquisitionRequest) : Set₁ where
  constructor acquisition-semantic-assessment
  field
    result : ABI.RuntimeNeutralAcquisitionResult request
    executionAdmitted :
      executionAllowsSemanticAssessment (ABI.executionStatus result) ≡ true
    sourceDiligence : Diligence.SourceDiligence
    contentInspectionReference : String
    exactRequestResultSameObjectReference : String
    semanticSameObjectReference : String
    temporalAssessmentReference : String
    coverageAssessmentReference : String
    contradictionAssessmentReference : String
    authorityAssessmentReference : String
    applicabilityAssessmentReference : String
    paymentAssessmentReference : String
    assessmentShape : Loop.ObservationAssessmentShape
    assessmentReference : String

open AcquisitionSemanticAssessment public

toAssessedObservationResult :
  (request : ABI.RuntimeNeutralAcquisitionRequest) →
  AcquisitionSemanticAssessment request →
  Loop.AssessedObservationResult
toAssessedObservationResult request assessment =
  Loop.assessed-observation-result
    (ABI.selectedCandidate request)
    (ABI.resultIdentityReference (result assessment))
    (ABI.rawEvidenceReference (result assessment))
    (contentInspectionReference assessment)
    (sourceDiligence assessment)
    (semanticSameObjectReference assessment)
    (temporalAssessmentReference assessment)
    (coverageAssessmentReference assessment)
    (contradictionAssessmentReference assessment)
    (authorityAssessmentReference assessment)
    (applicabilityAssessmentReference assessment)
    (assessmentShape assessment)
    (assessmentReference assessment)

assessedDisposition :
  (request : ABI.RuntimeNeutralAcquisitionRequest) →
  AcquisitionSemanticAssessment request →
  Loop.ObservationReturnDisposition
assessedDisposition request assessment =
  Loop.disposition (toAssessedObservationResult request assessment)

assessmentClassifierPreserved :
  (request : ABI.RuntimeNeutralAcquisitionRequest) →
  (assessment : AcquisitionSemanticAssessment request) →
  assessedDisposition request assessment
  ≡ Loop.classifyObservationReturn (assessmentShape assessment)
assessmentClassifierPreserved request assessment = refl

------------------------------------------------------------------------
-- Provider-specific outputs all enter the SAME assessment compiler.
-- Their carriers remain distinct; the semantic return algebra does not depend
-- on provider identity.
------------------------------------------------------------------------

record ProviderNeutralAssessmentCompatibility : Set where
  constructor provider-neutral-assessment-compatibility
  field
    documentResultUsesSameAssessmentCompiler : Bool
    documentResultUsesSameAssessmentCompilerIsTrue :
      documentResultUsesSameAssessmentCompiler ≡ true
    sensorResultUsesSameAssessmentCompiler : Bool
    sensorResultUsesSameAssessmentCompilerIsTrue :
      sensorResultUsesSameAssessmentCompiler ≡ true
    marketResultUsesSameAssessmentCompiler : Bool
    marketResultUsesSameAssessmentCompilerIsTrue :
      marketResultUsesSameAssessmentCompiler ≡ true
    wikimediaResultUsesSameAssessmentCompiler : Bool
    wikimediaResultUsesSameAssessmentCompilerIsTrue :
      wikimediaResultUsesSameAssessmentCompiler ≡ true
    communityResultUsesSameAssessmentCompiler : Bool
    communityResultUsesSameAssessmentCompilerIsTrue :
      communityResultUsesSameAssessmentCompiler ≡ true

canonicalProviderNeutralAssessmentCompatibility :
  ProviderNeutralAssessmentCompatibility
canonicalProviderNeutralAssessmentCompatibility =
  provider-neutral-assessment-compatibility
    true refl true refl true refl true refl true refl

------------------------------------------------------------------------
-- Fail-closed bridge boundaries.
------------------------------------------------------------------------

data TransportSuccessIsSemanticAssessment : Set where
data NoMatchIsNegativeWorldFact : Set where
data SemanticPaymentCreatesActionAuthority : Set where
data SameProviderImpliesSameEpistemicCarrier : Set where

typeTransportSuccessDoesNotReplaceAssessment :
  TransportSuccessIsSemanticAssessment → ⊥
typeTransportSuccessDoesNotReplaceAssessment ()

noMatchDoesNotBecomeNegativeFact : NoMatchIsNegativeWorldFact → ⊥
noMatchDoesNotBecomeNegativeFact ()

semanticPaymentDoesNotCreateActionAuthority :
  SemanticPaymentCreatesActionAuthority → ⊥
semanticPaymentDoesNotCreateActionAuthority ()

providerIdentityDoesNotCollapseCarrierSemantics :
  SameProviderImpliesSameEpistemicCarrier → ⊥
providerIdentityDoesNotCollapseCarrierSemantics ()

record AcquisitionResultAssessmentBoundary : Set where
  constructor acquisition-result-assessment-boundary
  field
    onlyExecutedOutputEntersSemanticAssessment : Bool
    onlyExecutedOutputEntersSemanticAssessmentIsTrue :
      onlyExecutedOutputEntersSemanticAssessment ≡ true
    assessmentRetainsSourceDiligence : Bool
    assessmentRetainsSourceDiligenceIsTrue : assessmentRetainsSourceDiligence ≡ true
    sameObjectAndApplicabilityRemainExplicit : Bool
    sameObjectAndApplicabilityRemainExplicitIsTrue :
      sameObjectAndApplicabilityRemainExplicit ≡ true
    providerIdentityDoesNotChooseDisposition : Bool
    providerIdentityDoesNotChooseDispositionIsTrue :
      providerIdentityDoesNotChooseDisposition ≡ true

canonicalAcquisitionResultAssessmentBoundary : AcquisitionResultAssessmentBoundary
canonicalAcquisitionResultAssessmentBoundary =
  acquisition-result-assessment-boundary true refl true refl true refl true refl
