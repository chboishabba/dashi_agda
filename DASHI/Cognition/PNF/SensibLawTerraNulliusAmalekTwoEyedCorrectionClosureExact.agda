module DASHI.Cognition.PNF.SensibLawTerraNulliusAmalekTwoEyedCorrectionClosureExact where

------------------------------------------------------------------------
-- TERRA NULLIUS / AMALEK / TWO-EYED CORRECTION-CLOSURE CROSS-POLLINATION
--
-- Terra nullius already supplies a relation-indexed juridical non-humanity
-- classification.  Amalek supplies a separately bounded operator-pattern for
-- closed authority loops.  Two-Eyed Seeing / Indigenous-knowledge owners keep
-- state/community/knowledge histories distinct without epistemic fusion.
-- POSIWID supplies the operational rule that realised correction behaviour is
-- itself part of what a system does.
--
-- This file does NOT assert historical identity between terra nullius and
-- Amalek.  It defines the stronger terminalisation criterion and records which
-- coordinates are already paid versus which require separate evidence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusJuridicalHumanityOperationalEquivalenceExact as Humanity
import DASHI.Cognition.PNF.SensibLawCountrySystemFunctionTwoEyedRemedyRealisationExact as SystemFunction
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- 1. Strong terra-nullius input: juridical humanity is constitutionally erased
--    in the relevant foundational legal relation.
------------------------------------------------------------------------

terraNulliusIsJuridicallyNonHumanNonconstitutive :
  Humanity.classify Humanity.terraNulliusCriterion
  ≡ Humanity.juridicallyNonHumanNonconstitutive
terraNulliusIsJuridicallyNonHumanNonconstitutive = refl

terraNulliusDeniedLegallyConstitutiveHumanity :
  Humanity.legallyConstitutiveHumanityDenied
    Humanity.terraNulliusJuridicalNonHumanityReading ≡ true
terraNulliusDeniedLegallyConstitutiveHumanity = refl

------------------------------------------------------------------------
-- 2. Amalek closed-loop coordinates remain separate from juridical humanity.
------------------------------------------------------------------------

data TerminalisationCoordinate : Set where
  constitutiveHumanityErasure
  authoritySelfValidation
  externalCorrectionDelegitimation
  doubtPenalty
  dissentReclassifiedAsFault
  independentCorrectionClosure
  : TerminalisationCoordinate

data CoordinateEvidenceState : Set where
  sourceOrOwnerPaid
  criticalStructuralInference
  separateEvidenceRequired
  : CoordinateEvidenceState

terraNulliusTerminalisationEvidenceState :
  TerminalisationCoordinate → CoordinateEvidenceState
terraNulliusTerminalisationEvidenceState constitutiveHumanityErasure = sourceOrOwnerPaid
terraNulliusTerminalisationEvidenceState authoritySelfValidation = criticalStructuralInference
terraNulliusTerminalisationEvidenceState externalCorrectionDelegitimation = separateEvidenceRequired
terraNulliusTerminalisationEvidenceState doubtPenalty = separateEvidenceRequired
terraNulliusTerminalisationEvidenceState dissentReclassifiedAsFault = separateEvidenceRequired
terraNulliusTerminalisationEvidenceState independentCorrectionClosure = separateEvidenceRequired

constitutiveErasureAlreadyPaid :
  terraNulliusTerminalisationEvidenceState constitutiveHumanityErasure
  ≡ sourceOrOwnerPaid
constitutiveErasureAlreadyPaid = refl

closedLoopRequiresMoreThanJuridicalErasure :
  terraNulliusTerminalisationEvidenceState independentCorrectionClosure
  ≡ separateEvidenceRequired
closedLoopRequiresMoreThanJuridicalErasure = refl

------------------------------------------------------------------------
-- 3. Generic stronger criterion: juridical non-humanity + closed correction
--    loop gives terminalising juridical erasure.
------------------------------------------------------------------------

data TerminalisingJuridicalErasure : Set where
  terminalisingJuridicalErasure : TerminalisingJuridicalErasure

record TerminalisingJuridicalErasureWitness : Set where
  constructor terminalising-juridical-erasure-witness
  field
    juridicalState : Humanity.JuridicalHumanityOperationalState
    juridicalStateExact : juridicalState ≡ Humanity.juridicallyNonHumanNonconstitutive
    closedLoop : Amalek.ClosedAuthorityLoop
    authoritySelfValidatesExact : Amalek.authoritySelfValidates closedLoop ≡ true
    externalEvidenceDelegitimisedExact : Amalek.externalEvidenceDelegitimised closedLoop ≡ true
    doubtPenalisedExact : Amalek.doubtPenalised closedLoop ≡ true
    dissentReclassifiedAsFaultExact : Amalek.dissentReclassifiedAsFault closedLoop ≡ true
    correctionChannelIndependentExact : Amalek.correctionChannelIndependent closedLoop ≡ false
    classification : TerminalisingJuridicalErasure

open TerminalisingJuridicalErasureWitness public

canonicalAbstractTerminalisationWitness : TerminalisingJuridicalErasureWitness
canonicalAbstractTerminalisationWitness = terminalising-juridical-erasure-witness
  Humanity.juridicallyNonHumanNonconstitutive refl
  Amalek.canonicalClosedAuthorityRisk
  refl refl refl refl refl
  terminalisingJuridicalErasure

------------------------------------------------------------------------
-- 4. Historical-identity firewall.
------------------------------------------------------------------------

data TerraNulliusIsLiterallyAmalekHistoricalDoctrine : Set where
data JuridicalNonHumanityAloneProvesEveryClosedLoopCoordinate : Set where
data AmalekMayNameAnIndigenousPeopleOrHumanGroup : Set where

doesNotClaimHistoricalDoctrineIdentity :
  TerraNulliusIsLiterallyAmalekHistoricalDoctrine → ⊥
doesNotClaimHistoricalDoctrineIdentity ()

juridicalNonHumanityAloneDoesNotPayWholeClosedLoop :
  JuridicalNonHumanityAloneProvesEveryClosedLoopCoordinate → ⊥
juridicalNonHumanityAloneDoesNotPayWholeClosedLoop ()

humanGroupPromotionRemainsForbidden : AmalekMayNameAnIndigenousPeopleOrHumanGroup → ⊥
humanGroupPromotionRemainsForbidden ()

------------------------------------------------------------------------
-- 5. Two-Eyed Seeing: correction cannot be assessed from one sovereign report.
------------------------------------------------------------------------

sharedObservationDoesNotFuseEpistemicHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseEpistemicHistory = refl

extractedPropositionDoesNotRecoverKnowledgeAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionDoesNotRecoverKnowledgeAuthority = IK.propositionCannotRecoverAuthority

stateReportDoesNotExhaustCommunityOutcome :
  SystemFunction.stateReportExhaustsCommunityOutcome
    SystemFunction.canonicalTwoEyedRealisationAssessment ≡ false
stateReportDoesNotExhaustCommunityOutcome = refl

communityOutcomeMayReopenStateImplementationAssessment :
  SystemFunction.communityOutcomeMayReopenImplementationAssessment
    SystemFunction.canonicalTwoEyedRealisationAssessment ≡ true
communityOutcomeMayReopenStateImplementationAssessment = refl

------------------------------------------------------------------------
-- 6. POSIWID: correction handling is part of the observable system operation.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

correctionResponseCountsAsSystemOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
correctionResponseCountsAsSystemOperation = refl

declaredPurposeCannotOverrideRepeatedRealisedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeCannotOverrideRepeatedRealisedEffect = refl

operationalClassificationDoesNotRequirePrivateIntentProof :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationalClassificationDoesNotRequirePrivateIntentProof = refl

------------------------------------------------------------------------
-- 7. Correction adequacy for a decolonial remedy consumer.
------------------------------------------------------------------------

data CorrectionAdequacyCoordinate : Set where
  affectedCommunityAuthorityBearing
  independentReviewAvailable
  externalEvidenceAdmissible
  dissentDoesNotSelfInvalidate
  correctionCanChangeDecision
  realisedCountryOutcomeObserved
  recurrencePreventionObserved
  : CorrectionAdequacyCoordinate

data CorrectionAdequacyState : Set where
  paid
  open
  outcomeEvidenceRequired
  : CorrectionAdequacyState

currentCorrectionAdequacyState :
  CorrectionAdequacyCoordinate → CorrectionAdequacyState
currentCorrectionAdequacyState affectedCommunityAuthorityBearing = open
currentCorrectionAdequacyState independentReviewAvailable = open
currentCorrectionAdequacyState externalEvidenceAdmissible = open
currentCorrectionAdequacyState dissentDoesNotSelfInvalidate = open
currentCorrectionAdequacyState correctionCanChangeDecision = open
currentCorrectionAdequacyState realisedCountryOutcomeObserved = outcomeEvidenceRequired
currentCorrectionAdequacyState recurrencePreventionObserved = outcomeEvidenceRequired

------------------------------------------------------------------------
-- 8. Operational closure is stronger than declared consultation/remedy activity.
------------------------------------------------------------------------

record DecolonialCorrectionClosure : Set where
  constructor decolonial-correction-closure
  field
    communityAuthorityBearing : Bool
    independentCorrection : Bool
    externalEvidenceCanCorrectState : Bool
    dissentCanRemainEvidenceRatherThanFault : Bool
    correctionCanAlterInstitutionalDecision : Bool
    realisedCountryOutcomeImproved : Bool
    recurrencePreventionObserved : Bool

open DecolonialCorrectionClosure public

record ClosureReceipt (closure : DecolonialCorrectionClosure) : Set where
  constructor closure-receipt
  field
    communityAuthorityBearingPaid : communityAuthorityBearing closure ≡ true
    independentCorrectionPaid : independentCorrection closure ≡ true
    externalEvidenceCorrectionPaid : externalEvidenceCanCorrectState closure ≡ true
    dissentNotFaultPaid : dissentCanRemainEvidenceRatherThanFault closure ≡ true
    correctionAltersDecisionPaid : correctionCanAlterInstitutionalDecision closure ≡ true
    countryOutcomePaid : realisedCountryOutcomeImproved closure ≡ true
    recurrencePreventionPaid : recurrencePreventionObserved closure ≡ true

open ClosureReceipt public

------------------------------------------------------------------------
-- 9. A declared state remedy surface cannot factor the stronger closure state.
------------------------------------------------------------------------

data RemedyProcessState : Set where
  declarationWithoutIndependentCorrection
  declarationWithIndependentCorrection
  : RemedyProcessState

data StateRemedyDeclaration : Set where
  sameDeclaredRemedy : StateRemedyDeclaration

data CorrectionChannelState : Set where
  correctionClosed correctionOpen : CorrectionChannelState

stateRemedyDeclaration : RemedyProcessState → StateRemedyDeclaration
stateRemedyDeclaration _ = sameDeclaredRemedy

correctionChannelState : RemedyProcessState → CorrectionChannelState
correctionChannelState declarationWithoutIndependentCorrection = correctionClosed
correctionChannelState declarationWithIndependentCorrection = correctionOpen

declaredRemedyCannotRecoverCorrectionChannel :
  INF.FactorsThrough stateRemedyDeclaration correctionChannelState → ⊥
declaredRemedyCannotRecoverCorrectionChannel =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      declarationWithoutIndependentCorrection
      declarationWithIndependentCorrection
      refl
      (λ ()))

------------------------------------------------------------------------
-- 10. System-function reading.
------------------------------------------------------------------------

record SystemFunctionCorrectionBoundary : Set where
  constructor system-function-correction-boundary
  field
    doctrinalRejectionAloneClosesAuthorityErasure : Bool
    doctrinalRejectionAloneClosesAuthorityErasureIsFalse :
      doctrinalRejectionAloneClosesAuthorityErasure ≡ false
    stateConsultationLabelAloneProvesIndependentCorrection : Bool
    stateConsultationLabelAloneProvesIndependentCorrectionIsFalse :
      stateConsultationLabelAloneProvesIndependentCorrection ≡ false
    repeatedCorrectionClosureMayClassifySystemOperation : Bool
    repeatedCorrectionClosureMayClassifySystemOperationIsTrue :
      repeatedCorrectionClosureMayClassifySystemOperation ≡ true
    repeatedAuthorityErasureMayClassifySystemOperation : Bool
    repeatedAuthorityErasureMayClassifySystemOperationIsTrue :
      repeatedAuthorityErasureMayClassifySystemOperation ≡ true
    operationalClassificationEqualsPrivateIntentFinding : Bool
    operationalClassificationEqualsPrivateIntentFindingIsFalse :
      operationalClassificationEqualsPrivateIntentFinding ≡ false
    affectedCommunityOutcomeIsIndependentRequiredStrand : Bool
    affectedCommunityOutcomeIsIndependentRequiredStrandIsTrue :
      affectedCommunityOutcomeIsIndependentRequiredStrand ≡ true

open SystemFunctionCorrectionBoundary public

canonicalSystemFunctionCorrectionBoundary : SystemFunctionCorrectionBoundary
canonicalSystemFunctionCorrectionBoundary = system-function-correction-boundary
  false refl
  false refl
  true refl
  true refl
  false refl
  true refl
