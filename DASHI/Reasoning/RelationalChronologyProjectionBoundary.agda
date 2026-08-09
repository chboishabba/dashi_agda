module DASHI.Reasoning.RelationalChronologyProjectionBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalStateCore as Core
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared
import DASHI.Reasoning.DefensiveReversalRepair as Defensive
import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic

------------------------------------------------------------------------
-- Relational triangle and assigned roles.
------------------------------------------------------------------------

data TrianglePosition : Set where
  dependentSubjectPosition witnessPosition messengerPosition : TrianglePosition
  potentialAllyPosition symbolicExtensionPosition independentParticipantPosition : TrianglePosition

record RelationalTriangle : Set where
  constructor relationalTriangle
  field
    firstAdult secondAdult triangleDependent : Core.Participant
    assignedPositions : List TrianglePosition
    roleAssignmentContested : Bool
    triangleReceipt : String

open RelationalTriangle public

firstCaregiver : Core.Participant
firstCaregiver = Core.participant "first caregiver" Core.caregiverRole

secondCaregiver : Core.Participant
secondCaregiver = Core.participant "second caregiver" Core.caregiverRole

dependentSubject : Core.Participant
dependentSubject = Core.participant "dependent participant" Core.dependentRole

canonicalRelationalTriangle : RelationalTriangle
canonicalRelationalTriangle =
  relationalTriangle firstCaregiver secondCaregiver dependentSubject
    (dependentSubjectPosition ∷ witnessPosition ∷ messengerPosition ∷ symbolicExtensionPosition ∷ [])
    true
    "A dependent participant may be positioned as witness, messenger, ally, or symbolic extension; the assigned position is not the participant's identity."

------------------------------------------------------------------------
-- Identity-prior contamination: hold the act fixed and change only the prior.
------------------------------------------------------------------------

data PriorLoad : Set where noInheritedPrior inheritedNegativePrior : PriorLoad

data CurrentAct : Set where requestParticularsAct boundaryWithdrawalAct ordinaryAssistanceAct : CurrentAct

data ActAppraisal : Set where
  clarificationAppraisal selfProtectionAppraisal facilitationAppraisal : ActAppraisal
  confirmingFaultAppraisal controllingAppraisal : ActAppraisal

appraise : PriorLoad → CurrentAct → ActAppraisal
appraise noInheritedPrior requestParticularsAct = clarificationAppraisal
appraise noInheritedPrior boundaryWithdrawalAct = selfProtectionAppraisal
appraise noInheritedPrior ordinaryAssistanceAct = facilitationAppraisal
appraise inheritedNegativePrior requestParticularsAct = confirmingFaultAppraisal
appraise inheritedNegativePrior boundaryWithdrawalAct = controllingAppraisal
appraise inheritedNegativePrior ordinaryAssistanceAct = controllingAppraisal

sameActDifferentPriorChangesAppraisal :
  ¬ (appraise noInheritedPrior requestParticularsAct
     ≡ appraise inheritedNegativePrior requestParticularsAct)
sameActDifferentPriorChangesAppraisal ()

record IdentityPriorProjection : Set where
  constructor identityPriorProjection
  field
    currentParticipant : Core.Participant
    projectedAct : CurrentAct
    importedTemplate : String
    priorLoad : PriorLoad
    projectedAppraisal : ActAppraisal
    appraisalMatchesProjection : projectedAppraisal ≡ appraise priorLoad projectedAct
    currentEvidenceParticularised projectionWovenBackIntoMemory correctionChannelOpen : Bool
    projectionReceipt : String

canonicalPriorContaminatedProjection : IdentityPriorProjection
canonicalPriorContaminatedProjection =
  identityPriorProjection dependentSubject requestParticularsAct
    "negative relative template" inheritedNegativePrior confirmingFaultAppraisal refl
    false true false
    "The current act is held fixed; only the inherited prior changes the appraisal."

------------------------------------------------------------------------
-- Causal order and recursive complaint expansion.
------------------------------------------------------------------------

data ChronologyShape : Set where
  actImpactObjectionResponseShape objectionDistressBlameShape : ChronologyShape

causalShapeDistinctFromReversedShape :
  ¬ (actImpactObjectionResponseShape ≡ objectionDistressBlameShape)
causalShapeDistinctFromReversedShape ()

record ChronologyProjection : Set where
  constructor chronologyProjection
  field
    sourceShape projectedShape : ChronologyShape
    initiatingActRetained primaryImpactRetained objectionReclassifiedAsOrigin : Bool
    projectionReceipt : String

canonicalCausalOrderLoss : ChronologyProjection
canonicalCausalOrderLoss =
  chronologyProjection actImpactObjectionResponseShape objectionDistressBlameShape
    false false true
    "The initiating act and impact are dropped, making the objection appear to originate the conflict."

data OpenBoundaryCount : Set where oneOpenBoundary twoOpenBoundaries : OpenBoundaryCount

expandCounterComplaint : OpenBoundaryCount → OpenBoundaryCount
expandCounterComplaint oneOpenBoundary = twoOpenBoundaries
expandCounterComplaint twoOpenBoundaries = twoOpenBoundaries

counterComplaintAddsBoundary : expandCounterComplaint oneOpenBoundary ≡ twoOpenBoundaries
counterComplaintAddsBoundary = refl

originalBoundaryNotResolvedByExpansion :
  ¬ (expandCounterComplaint oneOpenBoundary ≡ oneOpenBoundary)
originalBoundaryNotResolvedByExpansion ()

canonicalCausalConflictPath : Defensive.CausalConflictPath
canonicalCausalConflictPath =
  Defensive.causalConflictPath
    "initiating act" "primary impact" "objection"
    "secondary distress about the objection" "counter-allegation"
    "request to particularise and restore causal order" true
    "The original issue remains open after the counter-allegation is introduced."

------------------------------------------------------------------------
-- Pseudo-consultation and unsupported state promotion.
------------------------------------------------------------------------

canonicalConsultationEpisode : Shared.ConsultationEpisode
canonicalConsultationEpisode =
  Shared.consultationEpisode firstCaregiver dependentSubject
    "bounded proposal" "dependent participant input"
    Core.unilateralDecision false true
    "Input was requested but did not constrain the unilateral decision later narrated as joint."

canonicalPseudoConsultation : Shared.PseudoConsultationWitness canonicalConsultationEpisode
canonicalPseudoConsultation = record
  { inputWasRequested = true
  ; inputWasNotDecisionSensitive = true
  ; unilateralDecisionLaterPresentedAsJoint = true
  ; witnessReceipt = "Hearing input is not uptake when the decision is insensitive to it."
  }

presentPreferenceRepresentation : Core.TypedRepresentation
presentPreferenceRepresentation =
  Core.typedRepresentation dependentSubject Core.presentPreference
    "present preference" "current utterance"

canonicalPresentPreferencePromotion : Shared.PresentStatePromotion
canonicalPresentPreferencePromotion =
  Shared.presentStatePromotion presentPreferenceRepresentation
    Core.jointAgreementRepresentation false
    "A present preference lacks a witness promoting it to a historical joint agreement."

------------------------------------------------------------------------
-- Evidence layers and provenance roots.
------------------------------------------------------------------------

data EvidenceLayer : Set where
  originalRecordingLayer contemporaneousConversationLayer accountRecordLayer : EvidenceLayer
  professionalRecordLayer swornStatementLayer laterReconstructionLayer : EvidenceLayer
  generatedInterpretationLayer : EvidenceLayer

data ProvenanceRoot : Set where firstRoot secondRoot generatedRoot : ProvenanceRoot

record EvidenceItem : Set where
  constructor evidenceItem
  field
    evidenceLayer : EvidenceLayer
    evidenceRoot : ProvenanceRoot
    evidenceLabel : String
    exactEventParticularised exactTimeParticularised : Bool
    evidenceReceipt : String

open EvidenceItem public

data DistinctRoot : ProvenanceRoot → ProvenanceRoot → Set where
  firstSecondDistinct : DistinctRoot firstRoot secondRoot
  secondFirstDistinct : DistinctRoot secondRoot firstRoot
  firstGeneratedDistinct : DistinctRoot firstRoot generatedRoot
  generatedFirstDistinct : DistinctRoot generatedRoot firstRoot
  secondGeneratedDistinct : DistinctRoot secondRoot generatedRoot
  generatedSecondDistinct : DistinctRoot generatedRoot secondRoot

record IndependentEvidencePair (left right : EvidenceItem) : Set where
  constructor independentEvidencePair
  field
    rootsDistinct : DistinctRoot (evidenceRoot left) (evidenceRoot right)
    independenceReceipt : String

open IndependentEvidencePair public

sharedNarrativeReport₁ : EvidenceItem
sharedNarrativeReport₁ =
  evidenceItem laterReconstructionLayer firstRoot "first same-root report"
    false false "Provenance root is explicit."

sharedNarrativeReport₂ : EvidenceItem
sharedNarrativeReport₂ =
  evidenceItem swornStatementLayer firstRoot "second same-root report"
    true true "Different document form does not create an independent root."

sameRootReportsDoNotConstructIndependentPair :
  IndependentEvidencePair sharedNarrativeReport₁ sharedNarrativeReport₂ → ⊥
sameRootReportsDoNotConstructIndependentPair pair with rootsDistinct pair
... | ()

independentContemporaneousItem : EvidenceItem
independentContemporaneousItem =
  evidenceItem originalRecordingLayer secondRoot "independent contemporaneous record"
    true true "Distinct provenance root; substantive accuracy remains separately assessed."

canonicalIndependentPair :
  IndependentEvidencePair sharedNarrativeReport₁ independentContemporaneousItem
canonicalIndependentPair =
  independentEvidencePair firstSecondDistinct
    "The pair is provenance-distinct, not thereby automatically true or dispositive."

canonicalEvidenceHierarchy : List EvidenceLayer
canonicalEvidenceHierarchy =
  originalRecordingLayer ∷ contemporaneousConversationLayer ∷ accountRecordLayer
  ∷ professionalRecordLayer ∷ swornStatementLayer ∷ laterReconstructionLayer
  ∷ generatedInterpretationLayer ∷ []

------------------------------------------------------------------------
-- Node-specific acknowledgement versus coarse admission.
------------------------------------------------------------------------

data FiveNodeResponse : Set where
  acknowledgeEventImpactAndFaultContestIntentAndPattern : FiveNodeResponse
  wholesaleAffirmation wholesaleRejection : FiveNodeResponse

data CoarseAdmissionProjection : Set where coarseAdmission coarseDenial : CoarseAdmissionProjection

coarseProject : FiveNodeResponse → CoarseAdmissionProjection
coarseProject acknowledgeEventImpactAndFaultContestIntentAndPattern = coarseAdmission
coarseProject wholesaleAffirmation = coarseAdmission
coarseProject wholesaleRejection = coarseDenial

nodeSpecificAndWholesaleResponsesAreDistinct :
  ¬ (acknowledgeEventImpactAndFaultContestIntentAndPattern ≡ wholesaleAffirmation)
nodeSpecificAndWholesaleResponsesAreDistinct ()

coarseProjectionLosesNodeSpecificDifference :
  coarseProject acknowledgeEventImpactAndFaultContestIntentAndPattern
  ≡ coarseProject wholesaleAffirmation
coarseProjectionLosesNodeSpecificDifference = refl

record ClaimNodeSemantics : Set where
  constructor claimNodeSemantics
  field
    eventOccurred reportedImpactAcknowledged actInappropriate : Core.Stance
    dominationIntended coercivePatternAccepted : Core.Stance
    semanticsReceipt : String

canonicalNodeSpecificSemantics : ClaimNodeSemantics
canonicalNodeSpecificSemantics =
  claimNodeSemantics Core.affirmStance Core.affirmStance Core.affirmStance
    Core.rejectStance Core.rejectStance
    "Event, impact, and inappropriateness are acknowledged; attributed intent and pattern are contested."

------------------------------------------------------------------------
-- Fixed-record/live-account asymmetry and adjudicative non-injectivity.
------------------------------------------------------------------------

data AccountCarrier : Set where fixedRecordedAccount liveInteractiveAccount : AccountCarrier

record ProceduralExposure : Set where
  constructor proceduralExposure
  field
    accountCarrier : AccountCarrier
    exposedToCompression exposedToTimeLimit exposedToDemeanourInterpretation : Bool
    availableForReciprocalTesting : Bool
    exposureReceipt : String

fixedAccountExposure : ProceduralExposure
fixedAccountExposure = proceduralExposure fixedRecordedAccount false false false false
  "Stable fixed account, but unavailable for reciprocal testing when its author is absent."

liveAccountExposure : ProceduralExposure
liveAccountExposure = proceduralExposure liveInteractiveAccount true true true true
  "Reciprocally testable, but exposed to procedural compression, time, and demeanour interpretation."

data LivedRelationalHistory : Set where
  sameRecordDifferentContext₁ sameRecordDifferentContext₂ : LivedRelationalHistory

data AdjudicatedRecord : Set where canonicalOrderRecord : AdjudicatedRecord

adjudicate : LivedRelationalHistory → AdjudicatedRecord
adjudicate sameRecordDifferentContext₁ = canonicalOrderRecord
adjudicate sameRecordDifferentContext₂ = canonicalOrderRecord

distinctLivedHistories : ¬ (sameRecordDifferentContext₁ ≡ sameRecordDifferentContext₂)
distinctLivedHistories ()

adjudicationIsNonInjectiveWitness :
  adjudicate sameRecordDifferentContext₁ ≡ adjudicate sameRecordDifferentContext₂
adjudicationIsNonInjectiveWitness = refl

data AdjudicatedRecordDeterminesTotalIdentity : Set where

adjudicatedRecordDoesNotDetermineTotalIdentity :
  AdjudicatedRecordDeterminesTotalIdentity → ⊥
adjudicatedRecordDoesNotDetermineTotalIdentity ()

------------------------------------------------------------------------
-- Corrupted weave and repair.
------------------------------------------------------------------------

record CorruptedWeave : Set where
  constructor corruptedWeave
  field
    priorContaminatedInput exactContributionDropped dissentDropped : Bool
    decisionProvenanceDropped unresolvedBoundaryDropped : Bool
    currentPreferencePromotedToAgreement recursiveConflictExpansion : Bool
    corruptionReceipt : String

canonicalCorruptedWeave : CorruptedWeave
canonicalCorruptedWeave =
  corruptedWeave true true true true true true true
    "Prior-contaminated input is lossy-projected and woven back as complete shared state."

record ChronologyProjectionRepair : Set where
  constructor chronologyProjectionRepair
  field
    restoreInitiatingAct preservePrimaryImpact particulariseCounterAllegation : Bool
    distinguishHearingFromUptake distinguishPreferenceFromAgreement : Bool
    clusterEvidenceByProvenanceRoot preserveNodeSpecificAcknowledgement : Bool
    separateAdjudicatedRecordFromTotalIdentity useNeutralCustodyForContestedArchive : Bool
    repairReceipt : String

canonicalChronologyProjectionRepair : ChronologyProjectionRepair
canonicalChronologyProjectionRepair =
  chronologyProjectionRepair true true true true true true true true true
    "Repair restores causal order, exact response locality, provenance independence, and projection boundaries."

record RelationalChronologyProjectionBoundary : Set where
  constructor relationalChronologyProjectionBoundary
  field
    triangleRoleEqualsIdentityPromotion : Bool
    triangleRoleEqualsIdentityPromotionIsFalse : triangleRoleEqualsIdentityPromotion ≡ false
    inheritedTemplateDeterminesCurrentActPromotion : Bool
    inheritedTemplateDeterminesCurrentActPromotionIsFalse : inheritedTemplateDeterminesCurrentActPromotion ≡ false
    objectionBecomesOriginPromotion : Bool
    objectionBecomesOriginPromotionIsFalse : objectionBecomesOriginPromotion ≡ false
    requestedInputEqualsUptakePromotion : Bool
    requestedInputEqualsUptakePromotionIsFalse : requestedInputEqualsUptakePromotion ≡ false
    presentPreferenceEqualsJointAgreementPromotion : Bool
    presentPreferenceEqualsJointAgreementPromotionIsFalse : presentPreferenceEqualsJointAgreementPromotion ≡ false
    twoReportsEqualTwoIndependentSourcesPromotion : Bool
    twoReportsEqualTwoIndependentSourcesPromotionIsFalse : twoReportsEqualTwoIndependentSourcesPromotion ≡ false
    eventImpactAcknowledgementEqualsWholesaleAdmissionPromotion : Bool
    eventImpactAcknowledgementEqualsWholesaleAdmissionPromotionIsFalse : eventImpactAcknowledgementEqualsWholesaleAdmissionPromotion ≡ false
    fixedRecordEqualsReciprocallyTestedAccountPromotion : Bool
    fixedRecordEqualsReciprocallyTestedAccountPromotionIsFalse : fixedRecordEqualsReciprocallyTestedAccountPromotion ≡ false
    adjudicatedRecordEqualsLivedHypergraphPromotion : Bool
    adjudicatedRecordEqualsLivedHypergraphPromotionIsFalse : adjudicatedRecordEqualsLivedHypergraphPromotion ≡ false
    generatedInterpretationEqualsIndependentEvidencePromotion : Bool
    generatedInterpretationEqualsIndependentEvidencePromotionIsFalse : generatedInterpretationEqualsIndependentEvidencePromotion ≡ false
    boundaryReceipt : String

open RelationalChronologyProjectionBoundary public

canonicalRelationalChronologyProjectionBoundary : RelationalChronologyProjectionBoundary
canonicalRelationalChronologyProjectionBoundary =
  relationalChronologyProjectionBoundary
    false refl false refl false refl false refl false refl
    false refl false refl false refl false refl false refl
    "Current participants are evaluated through particular acts and evidence, not inherited family templates. Causal order, uptake, exact claim nodes, provenance roots, and projection boundaries remain typed."

diachronicAuthorityBoundary : Diachronic.DiachronicAuthorityPromotionBoundary
diachronicAuthorityBoundary = Diachronic.canonicalDiachronicAuthorityPromotionBoundary
