module DASHI.Cognition.PNF.SensibLawCountrySystemFunctionTwoEyedRemedyRealisationExact where

------------------------------------------------------------------------
-- COUNTRY / SYSTEM FUNCTION / TWO-EYED REMEDY REALISATION
--
-- This owner makes the operational consumer explicit:
--
--   system declaration / state report / consultation count
--   !=
--   realised justice in Country/community life.
--
-- Historical/legal source propositions remain in their existing owners.
-- Two-Eyed Seeing remains source-bounded and is used here only to preserve
-- distinct knowledge/authority strands without epistemic fusion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusJuridicalHumanityOperationalEquivalenceExact as Humanity
import DASHI.Cognition.PNF.SensibLawTerraNulliusBillyTwoEyedOperationalJusticeExact as Operational
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawBillySituatedKnowledgeRemedyAdequacyExact as Situated
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as CountrySystem
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed

------------------------------------------------------------------------
-- 1. Terra nullius: legal-functional equivalence at the foundational relation.
------------------------------------------------------------------------

terraNulliusFoundationalClassification :
  Humanity.classify Humanity.terraNulliusCriterion
  ≡ Humanity.juridicallyNonHumanNonconstitutive
terraNulliusFoundationalClassification = refl

terraNulliusLegallyConstitutiveHumanityDenied :
  Humanity.legallyConstitutiveHumanityDenied
    Humanity.terraNulliusJuridicalNonHumanityReading ≡ true
terraNulliusLegallyConstitutiveHumanityDenied = refl

terraNulliusClassificationIsNotOnlyMetaphor :
  Humanity.OperationalClassificationIsOnlyMetaphor → ⊥
terraNulliusClassificationIsNotOnlyMetaphor =
  Humanity.juridicalClassificationIsNotMerelyMetaphor

------------------------------------------------------------------------
-- 2. System-function coordinates: declarations are not the realised target.
------------------------------------------------------------------------

data SystemFunctionCoordinate : Set where
  juridicalConstitutiveStanding
  indigenousLawAuthority
  equalSovereignRelation
  landCountryControl
  materialSafety
  culturalContinuity
  compensationReparation
  communityDefinedNeedSatisfaction
  reciprocalCorrection
  preventionOfRecurrence
  : SystemFunctionCoordinate

data SystemFunctionState : Set where
  realisedFunction
  partialFunction
  residualFunctionOpen
  sourceOutcomeUnresolved
  : SystemFunctionState

systemFunctionState : SystemFunctionCoordinate → SystemFunctionState
systemFunctionState juridicalConstitutiveStanding = partialFunction
systemFunctionState indigenousLawAuthority = partialFunction
systemFunctionState equalSovereignRelation = residualFunctionOpen
systemFunctionState landCountryControl = residualFunctionOpen
systemFunctionState materialSafety = sourceOutcomeUnresolved
systemFunctionState culturalContinuity = sourceOutcomeUnresolved
systemFunctionState compensationReparation = residualFunctionOpen
systemFunctionState communityDefinedNeedSatisfaction = residualFunctionOpen
systemFunctionState reciprocalCorrection = sourceOutcomeUnresolved
systemFunctionState preventionOfRecurrence = sourceOutcomeUnresolved

landCountryControlStillOpen :
  systemFunctionState landCountryControl ≡ residualFunctionOpen
landCountryControlStillOpen = refl

compensationStillOpen :
  systemFunctionState compensationReparation ≡ residualFunctionOpen
compensationStillOpen = refl

materialSafetyStillNeedsOutcomeEvidence :
  systemFunctionState materialSafety ≡ sourceOutcomeUnresolved
materialSafetyStillNeedsOutcomeEvidence = refl

------------------------------------------------------------------------
-- 3. Means of compliance != odds of realised compliance.
------------------------------------------------------------------------

record RemedyRealisationTopology : Set where
  constructor remedy-realisation-topology
  field
    executiveImplementationAvailable : Bool
    executiveImplementationAvailableIsTrue : executiveImplementationAvailable ≡ true
    parliamentaryImplementationAvailable : Bool
    parliamentaryImplementationAvailableIsTrue : parliamentaryImplementationAvailable ≡ true
    treatyBodyFollowUpAvailable : Bool
    treatyBodyFollowUpAvailableIsTrue : treatyBodyFollowUpAvailable ≡ true
    committeeViewSelfExecutesDomestically : Bool
    committeeViewSelfExecutesDomesticallyIsFalse :
      committeeViewSelfExecutesDomestically ≡ false
    implementationDependsOnDomesticPoliticalAdministrativeAction : Bool
    implementationDependsOnDomesticPoliticalAdministrativeActionIsTrue :
      implementationDependsOnDomesticPoliticalAdministrativeAction ≡ true
    publicEvidenceIdentifiesNumericProbabilityOfFullReparation : Bool
    publicEvidenceIdentifiesNumericProbabilityOfFullReparationIsFalse :
      publicEvidenceIdentifiesNumericProbabilityOfFullReparation ≡ false
    currentPublicState : Operational.PublicBillyOperationalState
    currentPublicStateExact :
      currentPublicState ≡ Operational.partialImplementationMapped
    fullReparationClosed : Bool
    fullReparationClosedIsFalse : fullReparationClosed ≡ false
    reading : String

open RemedyRealisationTopology public

canonicalRemedyRealisationTopology : RemedyRealisationTopology
canonicalRemedyRealisationTopology = remedy-realisation-topology
  true refl
  true refl
  true refl
  false refl
  true refl
  false refl
  Operational.currentPublicBillyOperationalState refl
  false refl
  "Australia has direct domestic means to implement the Committee's remedy requirements, while treaty-body follow-up is indirect and the View is not a self-executing Australian writ. Current public receipts therefore support a topology of political/administrative contingency and partial implementation, not a numeric probability of full reparation."

publicBillyStateRemainsPartial :
  currentPublicState canonicalRemedyRealisationTopology
  ≡ Operational.partialImplementationMapped
publicBillyStateRemainsPartial = refl

fullReparationRemainsUnclosed :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
fullReparationRemainsUnclosed = refl

noNumericOddsFromMechanismTopology :
  publicEvidenceIdentifiesNumericProbabilityOfFullReparation
    canonicalRemedyRealisationTopology ≡ false
noNumericOddsFromMechanismTopology = refl

------------------------------------------------------------------------
-- 4. Two-Eyed Seeing: implementation evidence is a braid, not one sovereign
-- observer. State, community, monitoring and treaty-body strands stay distinct.
------------------------------------------------------------------------

data RealisationEvidenceStrand : Set where
  stateImplementationEvidence
  affectedCommunityOutcomeEvidence
  independentMonitoringEvidence
  treatyBodyFollowUpEvidence
  : RealisationEvidenceStrand

record TwoEyedRealisationAssessment : Set where
  constructor two-eyed-realisation-assessment
  field
    stateStrand : RealisationEvidenceStrand
    communityStrand : RealisationEvidenceStrand
    monitoringStrand : RealisationEvidenceStrand
    treatyBodyStrand : RealisationEvidenceStrand
    stateReportExhaustsCommunityOutcome : Bool
    stateReportExhaustsCommunityOutcomeIsFalse :
      stateReportExhaustsCommunityOutcome ≡ false
    sharedObservationFusesEpistemicHistory : Bool
    sharedObservationFusesEpistemicHistoryIsFalse :
      sharedObservationFusesEpistemicHistory ≡ false
    hearingCommunityContentTransfersCommunityAuthority : Bool
    hearingCommunityContentTransfersCommunityAuthorityIsFalse :
      hearingCommunityContentTransfersCommunityAuthority ≡ false
    communityOutcomeMayReopenImplementationAssessment : Bool
    communityOutcomeMayReopenImplementationAssessmentIsTrue :
      communityOutcomeMayReopenImplementationAssessment ≡ true
    realisedCorrectionLoopRequiredForClosure : Bool
    realisedCorrectionLoopRequiredForClosureIsTrue :
      realisedCorrectionLoopRequiredForClosure ≡ true

open TwoEyedRealisationAssessment public

canonicalTwoEyedRealisationAssessment : TwoEyedRealisationAssessment
canonicalTwoEyedRealisationAssessment = two-eyed-realisation-assessment
  stateImplementationEvidence
  affectedCommunityOutcomeEvidence
  independentMonitoringEvidence
  treatyBodyFollowUpEvidence
  false refl
  false refl
  false refl
  true refl
  true refl

sharedObservationStillDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationStillDoesNotFuseKnowledgeHistory = refl

extractedPropositionStillCannotRecoverAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionStillCannotRecoverAuthority = IK.propositionCannotRecoverAuthority

consultationStillCannotRecoverAuthorityParticipation :
  INF.FactorsThrough Situated.consultationSurface Situated.authorityParticipation → ⊥
consultationStillCannotRecoverAuthorityParticipation =
  Situated.consultationRecordCannotRecoverAuthorityParticipation

consultationStillCannotRecoverReciprocity :
  INF.FactorsThrough Situated.consultationSurface Situated.reciprocalImplementation → ⊥
consultationStillCannotRecoverReciprocity =
  Situated.consultationRecordCannotRecoverReciprocalImplementation

------------------------------------------------------------------------
-- 5. POSIWID / system-is-what-it-does: correction handling is observable too.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

realisedEffectMayClassifySystemOperation :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
realisedEffectMayClassifySystemOperation = refl

declaredPurposeDoesNotOverrideRepeatedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRepeatedEffect = refl

correctionResponseIsPartOfSystemOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
correctionResponseIsPartOfSystemOperation = refl

realisedOperationDoesNotProvePrivateIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
realisedOperationDoesNotProvePrivateIntent = refl

------------------------------------------------------------------------
-- 6. Operational adequacy: a declared remedy can fail its realised consumer.
------------------------------------------------------------------------

data DeclaredRemedySurface : Set where
  stateReportsMeaningfulConsultationAndAdaptation : DeclaredRemedySurface

data RealisedRemedyOutcome : Set where
  communityAuthorityNotCarried
  communityAuthorityCarried
  : RealisedRemedyOutcome

data RemedyProcessState : Set where
  reportedActivityWithoutAuthorityRealisation
  reportedActivityWithAuthorityRealisation
  : RemedyProcessState

declaredRemedySurface : RemedyProcessState → DeclaredRemedySurface
declaredRemedySurface _ = stateReportsMeaningfulConsultationAndAdaptation

realisedRemedyOutcome : RemedyProcessState → RealisedRemedyOutcome
realisedRemedyOutcome reportedActivityWithoutAuthorityRealisation = communityAuthorityNotCarried
realisedRemedyOutcome reportedActivityWithAuthorityRealisation = communityAuthorityCarried

sameDeclaredRemedySurface :
  declaredRemedySurface reportedActivityWithoutAuthorityRealisation
  ≡ declaredRemedySurface reportedActivityWithAuthorityRealisation
sameDeclaredRemedySurface = refl

realisedRemedyOutcomeDiffers :
  realisedRemedyOutcome reportedActivityWithoutAuthorityRealisation
  ≡ realisedRemedyOutcome reportedActivityWithAuthorityRealisation → ⊥
realisedRemedyOutcomeDiffers ()

declaredRemedyCannotRecoverRealisedAuthority :
  INF.FactorsThrough declaredRemedySurface realisedRemedyOutcome → ⊥
declaredRemedyCannotRecoverRealisedAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      reportedActivityWithoutAuthorityRealisation
      reportedActivityWithAuthorityRealisation
      refl
      realisedRemedyOutcomeDiffers)

------------------------------------------------------------------------
-- 7. Historical continuity test: rejecting the old doctrine does not by itself
-- prove that every later authority-erasing operation has disappeared.
------------------------------------------------------------------------

record AuthorityErasureContinuityTest : Set where
  constructor authority-erasure-continuity-test
  field
    foundationalTerraNulliusRejected : Bool
    foundationalTerraNulliusRejectedIsTrue : foundationalTerraNulliusRejected ≡ true
    laterProcessMayStillEraseCommunityAuthority : Bool
    laterProcessMayStillEraseCommunityAuthorityIsTrue :
      laterProcessMayStillEraseCommunityAuthority ≡ true
    historicalIdentityAutomaticallyClaimed : Bool
    historicalIdentityAutomaticallyClaimedIsFalse :
      historicalIdentityAutomaticallyClaimed ≡ false
    repeatedAuthorityErasureRequiresRealisedEvidence : Bool
    repeatedAuthorityErasureRequiresRealisedEvidenceIsTrue :
      repeatedAuthorityErasureRequiresRealisedEvidence ≡ true
    doctrinalCorrectionAloneProvesMaterialTransformation : Bool
    doctrinalCorrectionAloneProvesMaterialTransformationIsFalse :
      doctrinalCorrectionAloneProvesMaterialTransformation ≡ false

open AuthorityErasureContinuityTest public

canonicalAuthorityErasureContinuityTest : AuthorityErasureContinuityTest
canonicalAuthorityErasureContinuityTest = authority-erasure-continuity-test
  true refl
  true refl
  false refl
  true refl
  false refl

------------------------------------------------------------------------
-- 8. Reuse current-master operational justice routing.
------------------------------------------------------------------------

landControlRoutesToMaterialProducer :
  CountrySystem.producerFor CountrySystem.landAndCountryControl
  ≡ CountrySystem.landReturnOrControlProducer
landControlRoutesToMaterialProducer = refl

compensationRoutesToExecutionProducer :
  CountrySystem.producerFor CountrySystem.compensationAndReparation
  ≡ CountrySystem.compensationExecutionProducer
compensationRoutesToExecutionProducer = refl

communityNeedsRouteToCommunityDefinedProducer :
  CountrySystem.producerFor CountrySystem.communityDefinedNeedSatisfaction
  ≡ CountrySystem.communityDefinedNeedsProducer
communityNeedsRouteToCommunityDefinedProducer = refl

------------------------------------------------------------------------
-- 9. No-collapse laws.
------------------------------------------------------------------------

data StateReportEqualsCommunityOutcome : Set where
data ConsultationCountEqualsAuthorityBearingParticipation : Set where
data TreatyBodyFindingEqualsDomesticExecution : Set where
data MeansOfImplementationDetermineNumericOdds : Set where
data MaboDoctrinalCorrectionEqualsMaterialDecolonisation : Set where
data TerraNulliusRejectionProvesNoLaterAuthorityErasure : Set where
data TwoEyedSeeingMeansStateAndCommunityEvidenceMustAgree : Set where

stateReportDoesNotEqualCommunityOutcome : StateReportEqualsCommunityOutcome → ⊥
stateReportDoesNotEqualCommunityOutcome ()

consultationCountDoesNotEqualAuthorityBearingParticipation :
  ConsultationCountEqualsAuthorityBearingParticipation → ⊥
consultationCountDoesNotEqualAuthorityBearingParticipation ()

treatyBodyFindingDoesNotSelfExecuteDomestically : TreatyBodyFindingEqualsDomesticExecution → ⊥
treatyBodyFindingDoesNotSelfExecuteDomestically ()

meansDoNotDetermineNumericOdds : MeansOfImplementationDetermineNumericOdds → ⊥
meansDoNotDetermineNumericOdds ()

maboCorrectionDoesNotEqualMaterialDecolonisation :
  MaboDoctrinalCorrectionEqualsMaterialDecolonisation → ⊥
maboCorrectionDoesNotEqualMaterialDecolonisation ()

terraNulliusRejectionDoesNotProveNoLaterAuthorityErasure :
  TerraNulliusRejectionProvesNoLaterAuthorityErasure → ⊥
terraNulliusRejectionDoesNotProveNoLaterAuthorityErasure ()

twoEyedSeeingDoesNotRequireEvidenceFusion :
  TwoEyedSeeingMeansStateAndCommunityEvidenceMustAgree → ⊥
twoEyedSeeingDoesNotRequireEvidenceFusion ()
