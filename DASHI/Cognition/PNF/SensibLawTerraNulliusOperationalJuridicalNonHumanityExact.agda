module DASHI.Cognition.PNF.SensibLawTerraNulliusOperationalJuridicalNonHumanityExact where

------------------------------------------------------------------------
-- TERRA NULLIUS / OPERATIONAL JURIDICAL NON-HUMANITY
--
-- This owner does not soften the existing current-master classification.
-- It imports the already-owned relation-indexed juridical non-humanity result
-- and places it inside the plural operational / Two-Eyed justice architecture.
--
-- No phrase is back-attributed to Brennan J.  The source propositions remain
-- upstream; the operational classification is SensibLaw/DASHI synthesis.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Terra
import DASHI.Cognition.PNF.SensibLawCountryPluralEpistemicOperationalAuditExact as Audit
import DASHI.Cognition.PNF.SensibLawCountryCommunityAuthorityFirstCorrectionExact as Correction
import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.PluralOperationalRealisationDiscrepancyExact as Discrepancy
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Existing strong classification is inherited exactly.
------------------------------------------------------------------------

foundationalPersonhoodReceipt : Terra.RelationIndexedJuridicalPersonhood
foundationalPersonhoodReceipt = Terra.terraNulliusFoundationalJuridicalPersonhood

foundationalNonHumanityReceipt : Terra.RelationIndexedJuridicalNonHumanity
foundationalNonHumanityReceipt = Terra.terraNulliusRelationIndexedJuridicalNonHumanity

peoplePhysicallyPresent :
  Terra.physicallyPresent foundationalPersonhoodReceipt ≡ true
peoplePhysicallyPresent = refl

lawActuallyPresent :
  Terra.lawActuallyPresent foundationalPersonhoodReceipt ≡ true
lawActuallyPresent = refl

polityActuallyPresent :
  Terra.polityActuallyPresent foundationalPersonhoodReceipt ≡ true
polityActuallyPresent = refl

occupancyActuallyPresent :
  Terra.occupancyActuallyPresent foundationalPersonhoodReceipt ≡ true
occupancyActuallyPresent = refl

lawDeniedConstitutiveForce :
  Terra.humanLawPolityRelationDeniedConstitutiveForce foundationalNonHumanityReceipt ≡ true
lawDeniedConstitutiveForce = refl

treatedAsIfNoConstitutivePeopleWerePresent :
  Terra.treatedAsIfNoJuridicallyConstitutivePeopleWerePresent foundationalNonHumanityReceipt ≡ true
treatedAsIfNoConstitutivePeopleWerePresent = refl

classificationIsJuridicalNotBiological :
  Terra.classificationIsBiologicalTaxonomy foundationalNonHumanityReceipt ≡ false
classificationIsJuridicalNotBiological = refl

------------------------------------------------------------------------
-- System operation: this classification does not depend on benevolent or
-- malicious subjective intent.  The operation itself is the relevant carrier.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

operationMayClassifySystemFunction :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
operationMayClassifySystemFunction = refl

declaredPurposeDoesNotOverrideRepeatedOperation :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRepeatedOperation = refl

operationDoesNotNeedPrivateIntentProof :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationDoesNotNeedPrivateIntentProof = refl

------------------------------------------------------------------------
-- Historical operational sequence: juridical erasure -> doctrinal correction
-- -> still-open material/community operational closure.
------------------------------------------------------------------------

data OperationalHistoricalStage : Set where
  foundationalJuridicalErasureStage
  nativeTitleDoctrinalCorrectionStage
  partialOperationalCorrectionStage
  materialCommunityClosureStage
  : OperationalHistoricalStage

record TerraNulliusOperationalHistory : Set where
  constructor terra-nullius-operational-history
  field
    priorJuridicalErasureOccurred : Bool
    priorJuridicalErasureOccurredIsTrue : priorJuridicalErasureOccurred ≡ true
    laterDoctrinalCorrectionOccurred : Bool
    laterDoctrinalCorrectionOccurredIsTrue : laterDoctrinalCorrectionOccurred ≡ true
    laterCorrectionRetroactivelyDeletesPriorOperation : Bool
    laterCorrectionRetroactivelyDeletesPriorOperationIsFalse :
      laterCorrectionRetroactivelyDeletesPriorOperation ≡ false
    currentCommunityOutcomeClosed : Bool
    currentCommunityOutcomeClosedIsFalse : currentCommunityOutcomeClosed ≡ false
    currentCommunityAuthorityClosed : Bool
    currentCommunityAuthorityClosedIsFalse : currentCommunityAuthorityClosed ≡ false
    currentCorrectionResponseClosed : Bool
    currentCorrectionResponseClosedIsFalse : currentCorrectionResponseClosed ≡ false
    historyReference : String

open TerraNulliusOperationalHistory public

currentTerraNulliusOperationalHistory : TerraNulliusOperationalHistory
currentTerraNulliusOperationalHistory = terra-nullius-operational-history
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  "Current-master synthesis: terra nullius operated as relation-indexed juridical erasure/non-humanity in the foundational Crown-acquisition relation; Mabo was a real doctrinal correction; current Country/community operational closure remains incomplete on source-bounded residual coordinates."

currentCommunityOutcomeStillOpen :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.communityDefinedOutcomeCoordinate
  ≡ Operational.coordinateOpen
currentCommunityOutcomeStillOpen = refl

currentCommunityAuthorityStillOpen :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.communityAuthorityCoordinate
  ≡ Operational.coordinateOpen
currentCommunityAuthorityStillOpen = refl

currentCorrectionStillOpen :
  Operational.stateFor Audit.currentCountryOperationalSnapshot
    Operational.correctionResponseCoordinate
  ≡ Operational.coordinateOpen
currentCorrectionStillOpen = refl

------------------------------------------------------------------------
-- Two-Eyed / Indigenous-knowledge cross-pollination.
------------------------------------------------------------------------

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

sharedObservationDoesNotMeanSharedEpistemicHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory twoEyedBoundary ≡ false
sharedObservationDoesNotMeanSharedEpistemicHistory = refl

coordinationDoesNotRequireEpistemicFusion :
  TwoEyed.coordinatedUseRequiresEpistemicFusion twoEyedBoundary ≡ false
coordinationDoesNotRequireEpistemicFusion = refl

extractedStatePropositionCannotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedStatePropositionCannotRecoverCommunityAuthority = IK.propositionCannotRecoverAuthority

------------------------------------------------------------------------
-- Operational discrepancy consequence: an institution can report legal reform
-- while the material/community consumer remains open.  The State report is not
-- the privileged meta-observer of whether repair is realised.
------------------------------------------------------------------------

discrepancyBoundary : Discrepancy.OperationalDiscrepancyBoundary
discrepancyBoundary = Discrepancy.canonicalOperationalDiscrepancyBoundary

stateReportHasNoDefaultMetaObserverPriority :
  Discrepancy.stateReportGetsMetaObserverPriorityByDefault discrepancyBoundary ≡ false
stateReportHasNoDefaultMetaObserverPriority = refl

communityOutcomeCanReopenDeclaredSuccess :
  Discrepancy.repeatedOperationMayReopenDeclaredSuccess discrepancyBoundary ≡ true
communityOutcomeCanReopenDeclaredSuccess = refl

communityOutcomeRequiresIndependentCoordinate :
  Discrepancy.affectedCommunityOutcomeCanBeIndependentClosureCoordinate
    discrepancyBoundary ≡ true
communityOutcomeRequiresIndependentCoordinate = refl

currentCorrectionPlanBeginsWithCommunityOutcome :
  Correction.firstStage Correction.canonicalCommunityAuthorityFirstPlan
  ≡ Correction.obtainCommunityDefinedOutcomeStage
currentCorrectionPlanBeginsWithCommunityOutcome = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data MaboErasesTerraNulliusPriorOperation : Set where
data LegalRecognitionRepairsJuridicalErasureMateriallyByItself : Set where
data StateAcknowledgementCreatesCommunityAuthority : Set where
data JuridicalNonHumanityMeansBiologicalNonHumanityQuotation : Set where
data TwoEyedSeeingMeansStateCanAbsorbIndigenousEpistemicAuthority : Set where

aMaboDoesNotErasePriorOperation : MaboErasesTerraNulliusPriorOperation → ⊥
aMaboDoesNotErasePriorOperation ()

recognitionAloneDoesNotCompleteMaterialRepair :
  LegalRecognitionRepairsJuridicalErasureMateriallyByItself → ⊥
recognitionAloneDoesNotCompleteMaterialRepair ()

stateAcknowledgementDoesNotCreateCommunityAuthority :
  StateAcknowledgementCreatesCommunityAuthority → ⊥
stateAcknowledgementDoesNotCreateCommunityAuthority ()

juridicalNonHumanityNeedNotBeBiologicalQuotation :
  JuridicalNonHumanityMeansBiologicalNonHumanityQuotation → ⊥
juridicalNonHumanityNeedNotBeBiologicalQuotation ()

twoEyedSeeingDoesNotTransferIndigenousAuthorityToState :
  TwoEyedSeeingMeansStateCanAbsorbIndigenousEpistemicAuthority → ⊥
twoEyedSeeingDoesNotTransferIndigenousAuthorityToState ()
