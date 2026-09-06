module DASHI.Cognition.PNF.SensibLawDeclaredReasonRealizedEffectOperationalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as Operation
import DASHI.Cognition.PNF.SensibLawDoctrinalGateInterventionDistributionExact as Gate
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawJuridicalPersonhoodRemedyOperationalCrossPollinationExact as Cross

------------------------------------------------------------------------
-- Generic legal-system operational witness.
--
-- These finite states are synthetic DASHI fixtures. They are not claims that a
-- cited court or state used the exact labels below. Their purpose is to prove
-- that a declared legal/remedial surface cannot, by itself, carry realised
-- distribution or realised remedy.
------------------------------------------------------------------------

data LegalSystemState : Set where
  declaredNeutralEffectClaimant
  declaredNeutralEffectController
  : LegalSystemState

data DeclaredLegalRationale : Set where
  sameInstitutionalNeutralityRationale : DeclaredLegalRationale

data RealizedDistribution : Set where
  lossRemainsWithClaimant
  lossTransferredToController
  : RealizedDistribution

data LegalBehaviour : Set where
  closesRemedyRoute opensRemedyRoute : LegalBehaviour

data LegalCorrectionResponse : Set where
  reopensOnEvidence preservesGateAgainstChallenge : LegalCorrectionResponse

declaredLegalRationale : LegalSystemState → DeclaredLegalRationale
declaredLegalRationale _ = sameInstitutionalNeutralityRationale

realizedDistribution : LegalSystemState → RealizedDistribution
realizedDistribution declaredNeutralEffectClaimant = lossRemainsWithClaimant
realizedDistribution declaredNeutralEffectController = lossTransferredToController

legalBehaviour : LegalSystemState → LegalBehaviour
legalBehaviour declaredNeutralEffectClaimant = closesRemedyRoute
legalBehaviour declaredNeutralEffectController = opensRemedyRoute

legalCorrectionResponse : LegalSystemState → LegalCorrectionResponse
legalCorrectionResponse declaredNeutralEffectClaimant = preservesGateAgainstChallenge
legalCorrectionResponse declaredNeutralEffectController = reopensOnEvidence

legalOperationalSystem :
  Operation.OperationalSystem
    LegalSystemState DeclaredLegalRationale LegalBehaviour RealizedDistribution LegalCorrectionResponse
legalOperationalSystem = Operation.operational-system
  declaredLegalRationale legalBehaviour realizedDistribution legalCorrectionResponse

sameDeclaredRationale :
  declaredLegalRationale declaredNeutralEffectClaimant
  ≡ declaredLegalRationale declaredNeutralEffectController
sameDeclaredRationale = refl

differentDistribution :
  realizedDistribution declaredNeutralEffectClaimant
  ≡ realizedDistribution declaredNeutralEffectController → ⊥
differentDistribution ()

declaredRationaleDistributionWitness :
  INF.NonFactorabilityWitness declaredLegalRationale realizedDistribution
declaredRationaleDistributionWitness = INF.nonFactorabilityWitness
  declaredNeutralEffectClaimant
  declaredNeutralEffectController
  sameDeclaredRationale
  differentDistribution

declaredRationaleCannotRecoverDistribution :
  INF.FactorsThrough declaredLegalRationale realizedDistribution → ⊥
declaredRationaleCannotRecoverDistribution =
  INF.witnessRulesOutEveryFlatFactorisation declaredRationaleDistributionWitness

------------------------------------------------------------------------
-- Billy remedy fixture: same declared commitment, different realised remedy.
------------------------------------------------------------------------

data RemedySystemState : Set where
  declaredCommitmentPartialRepair
  declaredCommitmentFullRepair
  : RemedySystemState

data DeclaredRemedySurface : Set where
  sameCollaborationFundingCommitment : DeclaredRemedySurface

data RealizedRemedyState : Set where
  partialRepair fullRepair : RealizedRemedyState

data RemedyBehaviour : Set where
  activityWithoutFullClosure activityWithFullClosure : RemedyBehaviour

data RemedyCorrection : Set where
  correctionResidualOpen correctionResidualClosed : RemedyCorrection

declaredRemedySurface : RemedySystemState → DeclaredRemedySurface
declaredRemedySurface _ = sameCollaborationFundingCommitment

realizedRemedy : RemedySystemState → RealizedRemedyState
realizedRemedy declaredCommitmentPartialRepair = partialRepair
realizedRemedy declaredCommitmentFullRepair = fullRepair

remedyBehaviour : RemedySystemState → RemedyBehaviour
remedyBehaviour declaredCommitmentPartialRepair = activityWithoutFullClosure
remedyBehaviour declaredCommitmentFullRepair = activityWithFullClosure

remedyCorrection : RemedySystemState → RemedyCorrection
remedyCorrection declaredCommitmentPartialRepair = correctionResidualOpen
remedyCorrection declaredCommitmentFullRepair = correctionResidualClosed

remedyOperationalSystem :
  Operation.OperationalSystem
    RemedySystemState DeclaredRemedySurface RemedyBehaviour RealizedRemedyState RemedyCorrection
remedyOperationalSystem = Operation.operational-system
  declaredRemedySurface remedyBehaviour realizedRemedy remedyCorrection

sameDeclaredRemedy :
  declaredRemedySurface declaredCommitmentPartialRepair
  ≡ declaredRemedySurface declaredCommitmentFullRepair
sameDeclaredRemedy = refl

differentRealizedRemedy :
  realizedRemedy declaredCommitmentPartialRepair
  ≡ realizedRemedy declaredCommitmentFullRepair → ⊥
differentRealizedRemedy ()

declaredRemedyRealizationWitness :
  INF.NonFactorabilityWitness declaredRemedySurface realizedRemedy
declaredRemedyRealizationWitness = INF.nonFactorabilityWitness
  declaredCommitmentPartialRepair
  declaredCommitmentFullRepair
  sameDeclaredRemedy
  differentRealizedRemedy

declaredRemedyCannotRecoverRealizedRepair :
  INF.FactorsThrough declaredRemedySurface realizedRemedy → ⊥
declaredRemedyCannotRecoverRealizedRepair =
  INF.witnessRulesOutEveryFlatFactorisation declaredRemedyRealizationWitness

------------------------------------------------------------------------
-- Source-bounded bridges to the real legal/remedy owners.
------------------------------------------------------------------------

pabaiEffectIsDashReconstruction :
  Gate.effectIsDashReconstruction Gate.pabaiNoDutyAllocationAudit ≡ true
pabaiEffectIsDashReconstruction = refl

pabaiEffectDoesNotInferActorIntent :
  Gate.actorIntentInferred Gate.pabaiNoDutyAllocationAudit ≡ false
pabaiEffectDoesNotInferActorIntent = refl

billyCurrentFullReparationStillLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
billyCurrentFullReparationStillLive = refl

billyDeclaredActivityDoesNotCloseFullReparation :
  Cross.ConsultationAndFundingMeanFullReparationCompleted → ⊥
billyDeclaredActivityDoesNotCloseFullReparation = Cross.activityDoesNotEqualFullReparation

------------------------------------------------------------------------
-- Two-Eyed / community-defined operational closure.
------------------------------------------------------------------------

record CommunityDefinedOutcomeBoundary : Set where
  constructor community-defined-outcome-boundary
  field
    stateDefinedMetricAloneDeterminesCommunityRemedyAdequacy : Bool
    stateDefinedMetricAloneDeterminesCommunityRemedyAdequacyIsFalse :
      stateDefinedMetricAloneDeterminesCommunityRemedyAdequacy ≡ false
    communityDefinedNeedsAreIndependentCoordinate : Bool
    communityDefinedNeedsAreIndependentCoordinateIsTrue :
      communityDefinedNeedsAreIndependentCoordinate ≡ true
    knowledgeProvenanceIsIndependentCoordinate : Bool
    knowledgeProvenanceIsIndependentCoordinateIsTrue :
      knowledgeProvenanceIsIndependentCoordinate ≡ true
    correctionFeedbackIsPartOfSystemOperation : Bool
    correctionFeedbackIsPartOfSystemOperationIsTrue :
      correctionFeedbackIsPartOfSystemOperation ≡ true
    consultationCountIsNotSufficientStatisticForRemedy : Bool
    consultationCountIsNotSufficientStatisticForRemedyIsTrue :
      consultationCountIsNotSufficientStatisticForRemedy ≡ true

open CommunityDefinedOutcomeBoundary public

canonicalCommunityDefinedOutcomeBoundary : CommunityDefinedOutcomeBoundary
canonicalCommunityDefinedOutcomeBoundary = community-defined-outcome-boundary
  false refl
  true refl
  true refl
  true refl
  true refl

------------------------------------------------------------------------
-- Cross-domain theorem shape.
------------------------------------------------------------------------

record DeclaredRealizedLegalSystemBoundary : Set where
  constructor declared-realized-legal-system-boundary
  field
    statedRationaleDeterminesDistribution : Bool
    statedRationaleDeterminesDistributionIsFalse : statedRationaleDeterminesDistribution ≡ false
    statedRemedyCommitmentDeterminesRealization : Bool
    statedRemedyCommitmentDeterminesRealizationIsFalse : statedRemedyCommitmentDeterminesRealization ≡ false
    observedDistributionProvesSubjectiveIntent : Bool
    observedDistributionProvesSubjectiveIntentIsFalse : observedDistributionProvesSubjectiveIntent ≡ false
    observedRemedyFailureProvesNoGoodFaithEffort : Bool
    observedRemedyFailureProvesNoGoodFaithEffortIsFalse : observedRemedyFailureProvesNoGoodFaithEffort ≡ false
    repeatedRealizedEffectIsSystemRelevant : Bool
    repeatedRealizedEffectIsSystemRelevantIsTrue : repeatedRealizedEffectIsSystemRelevant ≡ true
    correctionResponseIsSystemRelevant : Bool
    correctionResponseIsSystemRelevantIsTrue : correctionResponseIsSystemRelevant ≡ true

open DeclaredRealizedLegalSystemBoundary public

canonicalDeclaredRealizedLegalSystemBoundary : DeclaredRealizedLegalSystemBoundary
canonicalDeclaredRealizedLegalSystemBoundary = declared-realized-legal-system-boundary
  false refl
  false refl
  false refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data NeutralRationaleProvesNeutralDistribution : Set where
data FundingAnnouncementProvesEffectiveRemedy : Set where
data RepeatedEffectProvesPrivateIntent : Set where
data CommunityConsultationMeansStateOwnsCommunityKnowledge : Set where

neutralWordsDoNotProveNeutralDistribution : NeutralRationaleProvesNeutralDistribution → ⊥
neutralWordsDoNotProveNeutralDistribution ()

fundingAnnouncementDoesNotProveEffectiveRemedy : FundingAnnouncementProvesEffectiveRemedy → ⊥
fundingAnnouncementDoesNotProveEffectiveRemedy ()

repeatedEffectDoesNotMindRead : RepeatedEffectProvesPrivateIntent → ⊥
repeatedEffectDoesNotMindRead ()

consultationDoesNotTransferKnowledgeAuthority : CommunityConsultationMeansStateOwnsCommunityKnowledge → ⊥
consultationDoesNotTransferKnowledgeAuthority ()
