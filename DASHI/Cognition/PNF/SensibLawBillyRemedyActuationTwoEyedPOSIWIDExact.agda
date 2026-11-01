module DASHI.Cognition.PNF.SensibLawBillyRemedyActuationTwoEyedPOSIWIDExact where

------------------------------------------------------------------------
-- BILLY REMEDY ACTUATION / TWO-EYED SEEING / POSIWID BIDI
--
-- No new external proposition is manufactured here.
-- Human Rights Committee findings/remedies, Australian responses, public
-- implementation states and Two-Eyed Seeing/Kimmerer propositions remain
-- source-owned upstream.  This file is a DASHI/SensibLaw actuation synthesis.
--
-- Core separation:
--   remedy finding
--   != enforcement channel
--   != use of that channel
--   != community-defined realised repair.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Operational
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- Actuation topology.
------------------------------------------------------------------------

data RemedyActuator : Set where
  stateExecutiveActuator : RemedyActuator
  parliamentaryActuator : RemedyActuator
  communityNegotiatedActuator : RemedyActuator
  treatyBodyFollowUpActuator : RemedyActuator
  periodicReportingActuator : RemedyActuator
  publicAccountabilityActuator : RemedyActuator
  separateDomesticCauseActuator : RemedyActuator
  noDirectDomesticExecutionActuator : RemedyActuator


data ActuationDependency : Set where
  stateCanActDirectly : ActuationDependency
  appropriationOrLegislationDependent : ActuationDependency
  communityAgreementDependent : ActuationDependency
  indirectExternalFollowUp : ActuationDependency
  separateLegalRouteRequired : ActuationDependency
  noSelfExecutingDomesticCompulsion : ActuationDependency


data ActuationProspect : Set where
  comparativelyDirectButOutcomeOpen : ActuationProspect
  politicallyDependent : ActuationProspect
  communityAuthorityDependent : ActuationProspect
  indirectFollowUpOnly : ActuationProspect
  separateRouteOnly : ActuationProspect
  noDirectExecutionRoute : ActuationProspect


record RemedyActuationReceipt : Set where
  constructor remedy-actuation-receipt
  field
    coordinate : Billy.RemedyCoordinate
    actuator : RemedyActuator
    dependency : ActuationDependency
    prospect : ActuationProspect
    publicImplementation : Billy.PublicImplementationState
    sourceOrSynthesisReference : String
    actuationChannelExists : Bool
    findingAloneExecutesChannel : Bool
    findingAloneExecutesChannelIsFalse : findingAloneExecutesChannel ≡ false
    stateReportAloneClosesOutcome : Bool
    stateReportAloneClosesOutcomeIsFalse : stateReportAloneClosesOutcome ≡ false
    communityDefinedOutcomeRequired : Bool
    communityDefinedOutcomeRequiredIsTrue : communityDefinedOutcomeRequired ≡ true

open RemedyActuationReceipt public

compensationActuation : RemedyActuationReceipt
compensationActuation = remedy-actuation-receipt
  Billy.adequateCompensation
  parliamentaryActuator
  appropriationOrLegislationDependent
  politicallyDependent
  (Billy.publicImplementationState Billy.adequateCompensation)
  "DASHI/SensibLaw synthesis over HRC full-reparation requirement + Australian implementation topology; public compensation receipt remains unrecovered upstream"
  true
  false refl
  false refl
  true refl

consultationActuation : RemedyActuationReceipt
consultationActuation = remedy-actuation-receipt
  Billy.meaningfulConsultation
  communityNegotiatedActuator
  communityAgreementDependent
  communityAuthorityDependent
  (Billy.publicImplementationState Billy.meaningfulConsultation)
  "DASHI/SensibLaw synthesis: consultation activity is publicly evidenced upstream, but adequacy remains community-authority/outcome indexed"
  true
  false refl
  false refl
  true refl

safeExistenceActuation : RemedyActuationReceipt
safeExistenceActuation = remedy-actuation-receipt
  Billy.continuedSafeExistenceMeasures
  stateExecutiveActuator
  stateCanActDirectly
  comparativelyDirectButOutcomeOpen
  (Billy.publicImplementationState Billy.continuedSafeExistenceMeasures)
  "DASHI/SensibLaw synthesis: executive/funding/adaptation action can occur directly, while realised safe existence remains an outcome consumer"
  true
  false refl
  false refl
  true refl

monitoringActuation : RemedyActuationReceipt
monitoringActuation = remedy-actuation-receipt
  Billy.monitoringAndReview
  treatyBodyFollowUpActuator
  indirectExternalFollowUp
  indirectFollowUpOnly
  (Billy.publicImplementationState Billy.monitoringAndReview)
  "DASHI/SensibLaw synthesis: monitoring/follow-up can scrutinise implementation but does not itself execute compensation or Country repair"
  true
  false refl
  false refl
  true refl

correctionActuation : RemedyActuationReceipt
correctionActuation = remedy-actuation-receipt
  Billy.correctionOfDeficiencies
  stateExecutiveActuator
  stateCanActDirectly
  politicallyDependent
  (Billy.publicImplementationState Billy.correctionOfDeficiencies)
  "DASHI/SensibLaw synthesis: correction requires the state implementation system actually to revise deficient action after feedback"
  true
  false refl
  false refl
  true refl

preventionActuation : RemedyActuationReceipt
preventionActuation = remedy-actuation-receipt
  Billy.preventionOfSimilarViolations
  parliamentaryActuator
  appropriationOrLegislationDependent
  politicallyDependent
  (Billy.publicImplementationState Billy.preventionOfSimilarViolations)
  "DASHI/SensibLaw synthesis: recurrence prevention may require policy, funding, legislation and institutional redesign; no single announcement pays the terminal outcome"
  true
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Why there is no honest single probability without a model and data.
------------------------------------------------------------------------

data ProspectCoordinate : Set where
  normSpecified : ProspectCoordinate
  directDomesticWritAvailable : ProspectCoordinate
  domesticActorCanAct : ProspectCoordinate
  budgetOrLegislationRequired : ProspectCoordinate
  communityAgreementRequired : ProspectCoordinate
  externalFollowUpAvailable : ProspectCoordinate
  realisedOutcomeObserved : ProspectCoordinate
  correctionActuallyOccurs : ProspectCoordinate


data ProspectState : Set where
  present : ProspectState
  absent : ProspectState
  conditional : ProspectState
  unresolved : ProspectState


compensationProspectState : ProspectCoordinate → ProspectState
compensationProspectState normSpecified = present
compensationProspectState directDomesticWritAvailable = absent
compensationProspectState domesticActorCanAct = present
compensationProspectState budgetOrLegislationRequired = conditional
compensationProspectState communityAgreementRequired = conditional
compensationProspectState externalFollowUpAvailable = present
compensationProspectState realisedOutcomeObserved = unresolved
compensationProspectState correctionActuallyOccurs = unresolved

record NoFakeScalarOddsBoundary : Set where
  constructor no-fake-scalar-odds-boundary
  field
    qualitativeDependencyProfileIsAvailable : Bool
    qualitativeDependencyProfileIsAvailableIsTrue :
      qualitativeDependencyProfileIsAvailable ≡ true
    sourceBackedNumericProbabilityAvailable : Bool
    sourceBackedNumericProbabilityAvailableIsFalse :
      sourceBackedNumericProbabilityAvailable ≡ false
    missingProbabilityMayBeInventedFromLegalStrength : Bool
    missingProbabilityMayBeInventedFromLegalStrengthIsFalse :
      missingProbabilityMayBeInventedFromLegalStrength ≡ false
    implementationProspectDependsOnActuatorAndPolitics : Bool
    implementationProspectDependsOnActuatorAndPoliticsIsTrue :
      implementationProspectDependsOnActuatorAndPolitics ≡ true

open NoFakeScalarOddsBoundary public

canonicalNoFakeScalarOddsBoundary : NoFakeScalarOddsBoundary
canonicalNoFakeScalarOddsBoundary = no-fake-scalar-odds-boundary
  true refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Two-Eyed Seeing: implementation adequacy is braided, not state-monocular.
------------------------------------------------------------------------

record BraidedActuationAssessment : Set where
  constructor braided-actuation-assessment
  field
    stateImplementationStrandPresent : Bool
    communityOutcomeStrandPresent : Bool
    independentMonitoringStrandPresent : Bool
    treatyBodyAssessmentStrandPresent : Bool
    stateStrandCanSubstituteForCommunityOutcome : Bool
    stateStrandCanSubstituteForCommunityOutcomeIsFalse :
      stateStrandCanSubstituteForCommunityOutcome ≡ false
    communityOutcomeMayReopenImplementation : Bool
    communityOutcomeMayReopenImplementationIsTrue :
      communityOutcomeMayReopenImplementation ≡ true
    correctionLoopPartOfAdequacy : Bool
    correctionLoopPartOfAdequacyIsTrue : correctionLoopPartOfAdequacy ≡ true

open BraidedActuationAssessment public

canonicalBraidedActuationAssessment : BraidedActuationAssessment
canonicalBraidedActuationAssessment = braided-actuation-assessment
  true true true true
  false refl
  true refl
  true refl

sharedObservationStillDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationStillDoesNotFuseKnowledgeHistory = refl

extractedPropositionStillDoesNotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionStillDoesNotRecoverCommunityAuthority =
  IK.propositionCannotRecoverAuthority

stateObservationStillDoesNotExhaustCommunityOutcome :
  Country.stateObservationExhaustsCommunityOutcome
    Country.canonicalBraidedRemedyAssessment ≡ false
stateObservationStillDoesNotExhaustCommunityOutcome = refl

------------------------------------------------------------------------
-- POSIWID terminal consumer.
------------------------------------------------------------------------

record RemedySystemOperationReceipt : Set where
  constructor remedy-system-operation-receipt
  field
    declarationObserved : Bool
    channelAvailable : Bool
    channelUsed : Bool
    communityOutcomeSatisfied : Bool
    independentCorrectionWorks : Bool
    realisedRepair : Bool

open RemedySystemOperationReceipt public

classifyRealisedRepair : RemedySystemOperationReceipt → Bool
classifyRealisedRepair
  (remedy-system-operation-receipt _ _ _ true true true) = true
classifyRealisedRepair _ = false

syntheticDeclarationWithoutOutcome : RemedySystemOperationReceipt
syntheticDeclarationWithoutOutcome = remedy-system-operation-receipt
  true true true false false false

syntheticDeclarationWithoutOutcomeDoesNotCloseRepair :
  classifyRealisedRepair syntheticDeclarationWithoutOutcome ≡ false
syntheticDeclarationWithoutOutcomeDoesNotCloseRepair = refl

syntheticBraidedRealisation : RemedySystemOperationReceipt
syntheticBraidedRealisation = remedy-system-operation-receipt
  true true true true true true

syntheticBraidedRealisationClosesTerminalConsumer :
  classifyRealisedRepair syntheticBraidedRealisation ≡ true
syntheticBraidedRealisationClosesTerminalConsumer = refl

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

correctionResponseIsPartOfWhatSystemDoes :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
correctionResponseIsPartOfWhatSystemDoes = refl

declaredPurposeCannotOverrideRepeatedOutcome :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeCannotOverrideRepeatedOutcome = refl

observedOperationStillDoesNotProvePrivateIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
observedOperationStillDoesNotProvePrivateIntent = refl

------------------------------------------------------------------------
-- Reverse route from live remedy residual to the first missing actuator/outcome.
------------------------------------------------------------------------

data RemedyReverseNeed : Set where
  acquireCompensationExecutionReceipt : RemedyReverseNeed
  acquireCommunityDefinedNeedsReceipt : RemedyReverseNeed
  acquireRealisedSafetyOutcome : RemedyReverseNeed
  acquireCorrectionResponseReceipt : RemedyReverseNeed
  acquireRecurrencePreventionOutcome : RemedyReverseNeed


reverseNeed : Billy.RemedyCoordinate → RemedyReverseNeed
reverseNeed Billy.adequateCompensation = acquireCompensationExecutionReceipt
reverseNeed Billy.meaningfulConsultation = acquireCommunityDefinedNeedsReceipt
reverseNeed Billy.communityNeedsAssessment = acquireCommunityDefinedNeedsReceipt
reverseNeed Billy.continuedSafeExistenceMeasures = acquireRealisedSafetyOutcome
reverseNeed Billy.monitoringAndReview = acquireCorrectionResponseReceipt
reverseNeed Billy.correctionOfDeficiencies = acquireCorrectionResponseReceipt
reverseNeed Billy.preventionOfSimilarViolations = acquireRecurrencePreventionOutcome
reverseNeed Billy.publicationAndDissemination = acquireCorrectionResponseReceipt

compensationRoutesToExecutionNotAnotherDeclaration :
  reverseNeed Billy.adequateCompensation ≡ acquireCompensationExecutionReceipt
compensationRoutesToExecutionNotAnotherDeclaration = refl

monitoringRoutesToCorrectionBehaviour :
  reverseNeed Billy.monitoringAndReview ≡ acquireCorrectionResponseReceipt
monitoringRoutesToCorrectionBehaviour = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data HRCFindingEqualsDomesticExecution : Set where
data AvailableActuatorEqualsActuatorUsed : Set where
data ActuatorUsedEqualsAdequateOutcome : Set where
data StateReportEqualsCommunityRealisation : Set where
data ConsultationMeetingEqualsAuthorityBearingCoDesign : Set where
data MonitoringWithoutCorrectionEqualsEffectiveRemedy : Set where
data PoliticalContingencyNegatesLegalMerits : Set where

findingDoesNotExecuteItself : HRCFindingEqualsDomesticExecution → ⊥
findingDoesNotExecuteItself ()

availableActuatorDoesNotProveUse : AvailableActuatorEqualsActuatorUsed → ⊥
availableActuatorDoesNotProveUse ()

useDoesNotProveAdequacy : ActuatorUsedEqualsAdequateOutcome → ⊥
useDoesNotProveAdequacy ()

stateReportDoesNotEqualCommunityRealisation : StateReportEqualsCommunityRealisation → ⊥
stateReportDoesNotEqualCommunityRealisation ()

consultationMeetingDoesNotEqualCoDesign : ConsultationMeetingEqualsAuthorityBearingCoDesign → ⊥
consultationMeetingDoesNotEqualCoDesign ()

monitoringWithoutCorrectionDoesNotEqualEffectiveRemedy :
  MonitoringWithoutCorrectionEqualsEffectiveRemedy → ⊥
monitoringWithoutCorrectionDoesNotEqualEffectiveRemedy ()

politicalDependencyDoesNotNegateMerits : PoliticalContingencyNegatesLegalMerits → ⊥
politicalDependencyDoesNotNegateMerits ()
