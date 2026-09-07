module DASHI.Core.PluralEpistemicOperationalClosureExact where

------------------------------------------------------------------------
-- PLURAL EPISTEMIC OPERATIONAL CLOSURE
--
-- Generic compiler combining four already-owned repository distinctions:
--
--   declared purpose != realised operation/effect;
--   one knowledge strand != exhaustive access to another strand's provenance;
--   consultation/reporting != authority-bearing community outcome;
--   correction response is itself part of system operation.
--
-- Source-specific Two-Eyed Seeing, POSIWID, Indigenous knowledge, legal and
-- remedy applications remain attributed in their own owners.  The records and
-- finite theorem shapes here are DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed

------------------------------------------------------------------------
-- A plural operational system preserves distinct evidence/authority strands.
------------------------------------------------------------------------

record PluralOperationalSystem
    (State Declared Behaviour Effect Correction StateObservation
     CommunityObservation CommunityOutcome : Set) : Set₁ where
  constructor plural-operational-system
  field
    declaredPurpose : State → Declared
    behaviour : State → Behaviour
    realisedEffect : State → Effect
    correctionResponse : State → Correction
    stateObservation : State → StateObservation
    communityObservation : State → CommunityObservation
    communityOutcome : State → CommunityOutcome

open PluralOperationalSystem public

------------------------------------------------------------------------
-- Closure coordinates are typed separately.  No single report pays all of them.
------------------------------------------------------------------------

data OperationalClosureCoordinate : Set where
  declaredCommitmentCoordinate
  realisedEffectCoordinate
  communityDefinedOutcomeCoordinate
  communityAuthorityCoordinate
  independentMonitoringCoordinate
  correctionResponseCoordinate
  preventionOfRecurrenceCoordinate
  : OperationalClosureCoordinate

data OperationalClosureState : Set where
  coordinatePaid
  coordinatePartial
  coordinateOpen
  coordinateSourceUnresolved
  : OperationalClosureState

record OperationalClosureSnapshot : Set where
  constructor operational-closure-snapshot
  field
    stateFor : OperationalClosureCoordinate → OperationalClosureState
    snapshotReference : String

open OperationalClosureSnapshot public

record FullOperationalClosure (snapshot : OperationalClosureSnapshot) : Set where
  constructor full-operational-closure
  field
    realisedEffectPaid : stateFor snapshot realisedEffectCoordinate ≡ coordinatePaid
    communityOutcomePaid : stateFor snapshot communityDefinedOutcomeCoordinate ≡ coordinatePaid
    communityAuthorityPaid : stateFor snapshot communityAuthorityCoordinate ≡ coordinatePaid
    monitoringPaid : stateFor snapshot independentMonitoringCoordinate ≡ coordinatePaid
    correctionPaid : stateFor snapshot correctionResponseCoordinate ≡ coordinatePaid
    recurrencePreventionPaid : stateFor snapshot preventionOfRecurrenceCoordinate ≡ coordinatePaid

------------------------------------------------------------------------
-- Two-Eyed / plural-knowledge closure does not fuse evidence histories.
------------------------------------------------------------------------

data EvidenceStrand : Set where
  institutionalSelfReportStrand
  affectedCommunityStrand
  independentMonitoringStrand
  externalReviewStrand
  : EvidenceStrand

record PluralEvidenceAssessment : Set where
  constructor plural-evidence-assessment
  field
    institutionalStrand : EvidenceStrand
    communityStrand : EvidenceStrand
    monitoringStrand : EvidenceStrand
    sharedObservationRequiresEpistemicFusion : Bool
    sharedObservationRequiresEpistemicFusionIsFalse :
      sharedObservationRequiresEpistemicFusion ≡ false
    institutionalObservationExhaustsCommunityOutcome : Bool
    institutionalObservationExhaustsCommunityOutcomeIsFalse :
      institutionalObservationExhaustsCommunityOutcome ≡ false
    communityOutcomeMayReopenInstitutionalAssessment : Bool
    communityOutcomeMayReopenInstitutionalAssessmentIsTrue :
      communityOutcomeMayReopenInstitutionalAssessment ≡ true
    correctionRequiresAuthorityBearingFeedback : Bool
    correctionRequiresAuthorityBearingFeedbackIsTrue :
      correctionRequiresAuthorityBearingFeedback ≡ true

open PluralEvidenceAssessment public

canonicalPluralEvidenceAssessment : PluralEvidenceAssessment
canonicalPluralEvidenceAssessment = plural-evidence-assessment
  institutionalSelfReportStrand
  affectedCommunityStrand
  independentMonitoringStrand
  false refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- Operational description: what the system repeatedly does is not recoverable
-- from its declaration alone.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

declaredPurposeDoesNotOverrideRepeatedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRepeatedEffect = refl

correctionHandlingIsPartOfOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
correctionHandlingIsPartOfOperation = refl

operationalDescriptionDoesNotProvePrivateIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationalDescriptionDoesNotProvePrivateIntent = refl

operationalDescriptionDoesNotProveLegitimacy :
  POSIWID.operationalDescriptionProvesLegitimacy posiwidBoundary ≡ false
operationalDescriptionDoesNotProveLegitimacy = refl

------------------------------------------------------------------------
-- Two-Eyed Seeing boundary: coordination does not fuse provenance/history.
------------------------------------------------------------------------

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

sharedObservationDoesNotMeanSameEpistemicHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory twoEyedBoundary ≡ false
sharedObservationDoesNotMeanSameEpistemicHistory = refl

coordinatedUseDoesNotRequireFusion :
  TwoEyed.coordinatedUseRequiresEpistemicFusion twoEyedBoundary ≡ false
coordinatedUseDoesNotRequireFusion = refl

------------------------------------------------------------------------
-- Finite witness: the same declaration/report can coexist with different
-- realised community outcomes and different correction responses.
------------------------------------------------------------------------

data DemoState : Set where
  reportSameOutcomeUnrepaired
  reportSameOutcomeRepaired
  : DemoState

data DemoDeclaration : Set where
  sameBenevolentDeclaration : DemoDeclaration

data DemoBehaviour : Set where
  activityWithoutAuthorityShift
  authorityBearingCorrectionBehaviour
  : DemoBehaviour

data DemoEffect : Set where
  materialResidualPersists
  materialResidualReduced
  : DemoEffect

data DemoCorrection : Set where
  feedbackRecordedOnly
  feedbackChangesOperation
  : DemoCorrection

data DemoStateObservation : Set where
  sameImplementationReport : DemoStateObservation

data DemoCommunityObservation : Set where
  sameCommunityIssueReported : DemoCommunityObservation

data DemoCommunityOutcome : Set where
  communityOutcomeUnchanged
  communityOutcomeImproved
  : DemoCommunityOutcome

demoDeclared : DemoState → DemoDeclaration
demoDeclared _ = sameBenevolentDeclaration

demoBehaviour : DemoState → DemoBehaviour
demoBehaviour reportSameOutcomeUnrepaired = activityWithoutAuthorityShift
demoBehaviour reportSameOutcomeRepaired = authorityBearingCorrectionBehaviour

demoEffect : DemoState → DemoEffect
demoEffect reportSameOutcomeUnrepaired = materialResidualPersists
demoEffect reportSameOutcomeRepaired = materialResidualReduced

demoCorrection : DemoState → DemoCorrection
demoCorrection reportSameOutcomeUnrepaired = feedbackRecordedOnly
demoCorrection reportSameOutcomeRepaired = feedbackChangesOperation

demoStateObservation : DemoState → DemoStateObservation
demoStateObservation _ = sameImplementationReport

demoCommunityObservation : DemoState → DemoCommunityObservation
demoCommunityObservation _ = sameCommunityIssueReported

demoCommunityOutcome : DemoState → DemoCommunityOutcome
demoCommunityOutcome reportSameOutcomeUnrepaired = communityOutcomeUnchanged
demoCommunityOutcome reportSameOutcomeRepaired = communityOutcomeImproved

demoSystem : PluralOperationalSystem
  DemoState DemoDeclaration DemoBehaviour DemoEffect DemoCorrection
  DemoStateObservation DemoCommunityObservation DemoCommunityOutcome
demoSystem = plural-operational-system
  demoDeclared demoBehaviour demoEffect demoCorrection
  demoStateObservation demoCommunityObservation demoCommunityOutcome

stateReportsCollide :
  demoStateObservation reportSameOutcomeUnrepaired
  ≡ demoStateObservation reportSameOutcomeRepaired
stateReportsCollide = refl

communityOutcomesDiffer :
  demoCommunityOutcome reportSameOutcomeUnrepaired
  ≡ demoCommunityOutcome reportSameOutcomeRepaired → ⊥
communityOutcomesDiffer ()

stateReportCannotRecoverCommunityOutcome :
  INF.FactorsThrough demoStateObservation demoCommunityOutcome → ⊥
stateReportCannotRecoverCommunityOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      reportSameOutcomeUnrepaired reportSameOutcomeRepaired
      stateReportsCollide communityOutcomesDiffer)

sameDeclarationsCollide :
  demoDeclared reportSameOutcomeUnrepaired
  ≡ demoDeclared reportSameOutcomeRepaired
sameDeclarationsCollide = refl

realisedEffectsDiffer :
  demoEffect reportSameOutcomeUnrepaired
  ≡ demoEffect reportSameOutcomeRepaired → ⊥
realisedEffectsDiffer ()

declarationCannotRecoverRealisedEffect :
  INF.FactorsThrough demoDeclared demoEffect → ⊥
declarationCannotRecoverRealisedEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      reportSameOutcomeUnrepaired reportSameOutcomeRepaired
      sameDeclarationsCollide realisedEffectsDiffer)

correctionResponsesDiffer :
  demoCorrection reportSameOutcomeUnrepaired
  ≡ demoCorrection reportSameOutcomeRepaired → ⊥
correctionResponsesDiffer ()

declarationCannotRecoverCorrectionResponse :
  INF.FactorsThrough demoDeclared demoCorrection → ⊥
declarationCannotRecoverCorrectionResponse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      reportSameOutcomeUnrepaired reportSameOutcomeRepaired
      sameDeclarationsCollide correctionResponsesDiffer)

------------------------------------------------------------------------
-- Classification of operational relation, not private motive.
------------------------------------------------------------------------

data OperationalRelationClass : Set where
  declaredOnly
  activityWithoutRealisedClosure
  partialOperationalCorrection
  authorityBearingMaterialTransformation
  correctionClosureRisk
  : OperationalRelationClass

record OperationalRelationReceipt : Set where
  constructor operational-relation-receipt
  field
    declarationPresent : Bool
    activityPresent : Bool
    realisedOutcomeImproved : Bool
    communityAuthorityCarried : Bool
    correctionCanChangeOperation : Bool
    independentMonitoringAvailable : Bool
    classification : OperationalRelationClass
    privateIntentProved : Bool
    privateIntentProvedIsFalse : privateIntentProved ≡ false
    receiptReference : String

open OperationalRelationReceipt public

------------------------------------------------------------------------
-- BIDI: first open operational coordinate routes to a producer.
------------------------------------------------------------------------

data OperationalProducer : Set where
  realisedOutcomeProducer
  communityAuthorityProducer
  independentMonitoringProducer
  correctionLoopProducer
  recurrencePreventionProducer
  : OperationalProducer

producerFor : OperationalClosureCoordinate → OperationalProducer
producerFor declaredCommitmentCoordinate = realisedOutcomeProducer
producerFor realisedEffectCoordinate = realisedOutcomeProducer
producerFor communityDefinedOutcomeCoordinate = realisedOutcomeProducer
producerFor communityAuthorityCoordinate = communityAuthorityProducer
producerFor independentMonitoringCoordinate = independentMonitoringProducer
producerFor correctionResponseCoordinate = correctionLoopProducer
producerFor preventionOfRecurrenceCoordinate = recurrencePreventionProducer

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DeclarationEqualsRealisedJustice : Set where
data InstitutionalReportEqualsCommunityOutcome : Set where
data ConsultationEqualsCommunityAuthority : Set where
data SharedObservationTransfersEpistemicAuthority : Set where
data MonitoringWithoutCorrectionClosesSystem : Set where
data DoctrinalCorrectionEqualsMaterialTransformation : Set where
\data OperationalClassificationProvesPrivateIntent : Set where

declarationDoesNotEqualRealisedJustice : DeclarationEqualsRealisedJustice → ⊥
declarationDoesNotEqualRealisedJustice ()

institutionalReportDoesNotEqualCommunityOutcome : InstitutionalReportEqualsCommunityOutcome → ⊥
institutionalReportDoesNotEqualCommunityOutcome ()

consultationDoesNotEqualCommunityAuthority : ConsultationEqualsCommunityAuthority → ⊥
consultationDoesNotEqualCommunityAuthority ()

sharedObservationDoesNotTransferAuthority : SharedObservationTransfersEpistemicAuthority → ⊥
sharedObservationDoesNotTransferAuthority ()

monitoringWithoutCorrectionDoesNotCloseSystem : MonitoringWithoutCorrectionClosesSystem → ⊥
monitoringWithoutCorrectionDoesNotCloseSystem ()

doctrinalCorrectionDoesNotEqualMaterialTransformation :
  DoctrinalCorrectionEqualsMaterialTransformation → ⊥
doctrinalCorrectionDoesNotEqualMaterialTransformation ()

operationalClassificationDoesNotProvePrivateIntent :
  OperationalClassificationProvesPrivateIntent → ⊥
operationalClassificationDoesNotProvePrivateIntent ()

record PluralEpistemicOperationalBoundary : Set where
  constructor plural-epistemic-operational-boundary
  field
    realisedOutcomeRequiredForClosure : Bool
    realisedOutcomeRequiredForClosureIsTrue : realisedOutcomeRequiredForClosure ≡ true
    affectedCommunityOutcomeIsIndependentStrand : Bool
    affectedCommunityOutcomeIsIndependentStrandIsTrue :
      affectedCommunityOutcomeIsIndependentStrand ≡ true
    stateSelfAssessmentIsSufficientForClosure : Bool
    stateSelfAssessmentIsSufficientForClosureIsFalse :
      stateSelfAssessmentIsSufficientForClosure ≡ false
    correctionHandlingCountsAsSystemBehaviour : Bool
    correctionHandlingCountsAsSystemBehaviourIsTrue :
      correctionHandlingCountsAsSystemBehaviour ≡ true
    epistemicCoordinationRequiresFusion : Bool
    epistemicCoordinationRequiresFusionIsFalse :
      epistemicCoordinationRequiresFusion ≡ false
    repeatedOperationMayReopenDeclaredSuccess : Bool
    repeatedOperationMayReopenDeclaredSuccessIsTrue :
      repeatedOperationMayReopenDeclaredSuccess ≡ true

canonicalPluralEpistemicOperationalBoundary : PluralEpistemicOperationalBoundary
canonicalPluralEpistemicOperationalBoundary = plural-epistemic-operational-boundary
  true refl
  true refl
  false refl
  true refl
  false refl
  true refl
