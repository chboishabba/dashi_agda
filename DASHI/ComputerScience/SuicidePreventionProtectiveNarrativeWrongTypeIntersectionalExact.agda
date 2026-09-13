module DASHI.ComputerScience.SuicidePreventionProtectiveNarrativeWrongTypeIntersectionalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as WrongType

------------------------------------------------------------------------
-- SUICIDE-PREVENTION COMMUNICATION: PROTECTIVE NARRATIVE / WRONGTYPE /
-- INTERSECTIONAL NON-FACTORABILITY / ADMISSIBILITY
--
-- Scope discipline:
--   * This is a formal model of evidence/communication obligations.
--   * It is not a clinical predictor, diagnosis, treatment rule, or individual
--     risk calculator.
--   * Empirical citations motivate the source receipts below; the generic
--     factorisation and admissibility statements are DASHI mathematics.
--
-- Primary references:
--
--   Marsha M. Linehan, Judith L. Goodstein, Stevan L. Nielsen, John A. Chiles,
--   "Reasons for staying alive when you are thinking of killing yourself:
--   The Reasons for Living Inventory", Journal of Consulting and Clinical
--   Psychology 51(2), 276-286 (1983).
--   DOI: 10.1037/0022-006X.51.2.276
--
--   Thomas Niederkrotenthaler, Martin Voracek, Arno Herberth, Benedikt Till,
--   Markus Strauss, Elmar Etzersdorfer, Brigitte Eisenwort, Gernot Sonneck,
--   "Role of media reports in completed and prevented suicide: Werther v.
--   Papageno effects", British Journal of Psychiatry 197(3), 234-243 (2010).
--   DOI: 10.1192/bjp.bp.109.074633
--
--   World Health Organization / International Association for Suicide
--   Prevention, "Preventing suicide: a resource for media professionals,
--   update 2023", ISBN 978-92-4-007684-6.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION RECEIPTS
--
-- The creator transcript is allowed to motivate a search, but it is not the
-- authority owner.  Paper identity, empirical result, creator gloss, and safe
-- communication guidance are distinct typed obligations.
------------------------------------------------------------------------

data EvidenceRole : Set where
  primaryStudy : EvidenceRole
  professionalGuidance : EvidenceRole
  creatorInterpretation : EvidenceRole

record SourceReceipt : Set where
  constructor source-receipt
  field
    authorTitle : String
    persistentId : String
    evidenceRole : EvidenceRole
    sourceLocated : Bool
    attributionReviewed : Bool
open SourceReceipt public

linehan1983 : SourceReceipt
linehan1983 = source-receipt
  "Linehan, Goodstein, Nielsen, Chiles — Reasons for staying alive when you are thinking of killing yourself: the Reasons for Living Inventory"
  "doi:10.1037/0022-006X.51.2.276"
  primaryStudy
  true
  true

niederkrotenthaler2010 : SourceReceipt
niederkrotenthaler2010 = source-receipt
  "Niederkrotenthaler et al. — Role of media reports in completed and prevented suicide: Werther v. Papageno effects"
  "doi:10.1192/bjp.bp.109.074633"
  primaryStudy
  true
  true

whoMedia2023 : SourceReceipt
whoMedia2023 = source-receipt
  "WHO / IASP — Preventing suicide: a resource for media professionals, update 2023"
  "ISBN:978-92-4-007684-6"
  professionalGuidance
  true
  true

creatorTranscript : SourceReceipt
creatorTranscript = source-receipt
  "Isaac Sanders social-video transcript supplied 2026-09-11"
  "video:DdHAaX2hi3Z"
  creatorInterpretation
  true
  false

------------------------------------------------------------------------
-- CLAIM ROLE != SOURCE ROLE
------------------------------------------------------------------------

data ClaimKind : Set where
  reasonsForLivingInventoryExists : ClaimKind
  positiveCopingCoverageAssociatedWithLowerRates : ClaimKind
  deathFocusedReportingCanBeHarmful : ClaimKind
  safeMediaPractice : ClaimKind
  creatorPersonalInterpretation : ClaimKind

record ClaimAttribution : Set where
  constructor claim-attribution
  field
    claimKind : ClaimKind
    source : SourceReceipt
    sourceDirectlyOwnsClaim : Bool
    requiresIndependentReview : Bool
open ClaimAttribution public

rflInventoryAttribution : ClaimAttribution
rflInventoryAttribution = claim-attribution
  reasonsForLivingInventoryExists linehan1983 true false

papagenoAssociationAttribution : ClaimAttribution
papagenoAssociationAttribution = claim-attribution
  positiveCopingCoverageAssociatedWithLowerRates niederkrotenthaler2010 true false

whoSafetyGuidanceAttribution : ClaimAttribution
whoSafetyGuidanceAttribution = claim-attribution
  safeMediaPractice whoMedia2023 true false

creatorGlossNeedsReview : ClaimAttribution
creatorGlossNeedsReview = claim-attribution
  creatorPersonalInterpretation creatorTranscript false true

------------------------------------------------------------------------
-- FACTORSTHROUGH: RISK CATALOGUE != REASONS-FOR-LIVING / PROTECTIVE ACCESS
--
-- Two situated states may have the same coarse risk-labelled surface while
-- differing in whether a concrete attachment / future event / relationship is
-- actually available as a reason-for-living resource.  Therefore a protective
-- accessibility consumer does not, in general, factor through the risk-only
-- projection.
--
-- This is a generic non-factorability witness, not a claim that any one reason
-- is sufficient to prevent suicide in an individual.
------------------------------------------------------------------------

data SituatedProtectiveState : Set where
  sameRiskSurfaceResourceUnavailable : SituatedProtectiveState
  sameRiskSurfaceResourceAccessible : SituatedProtectiveState

data RiskOnlySurface : Set where
  sameRiskLabel : RiskOnlySurface

riskOnlyObserver : SituatedProtectiveState → RiskOnlySurface
riskOnlyObserver sameRiskSurfaceResourceUnavailable = sameRiskLabel
riskOnlyObserver sameRiskSurfaceResourceAccessible = sameRiskLabel

protectiveAccessConsumer : SituatedProtectiveState → Bool
protectiveAccessConsumer sameRiskSurfaceResourceUnavailable = false
protectiveAccessConsumer sameRiskSurfaceResourceAccessible = true

protectiveAccessDiffers :
  protectiveAccessConsumer sameRiskSurfaceResourceUnavailable ≡
  protectiveAccessConsumer sameRiskSurfaceResourceAccessible → ⊥
protectiveAccessDiffers ()

riskOnlyNonFactorability :
  INF.NonFactorabilityWitness riskOnlyObserver protectiveAccessConsumer
riskOnlyNonFactorability = INF.nonFactorabilityWitness
  sameRiskSurfaceResourceUnavailable
  sameRiskSurfaceResourceAccessible
  refl
  protectiveAccessDiffers

riskCatalogueCannotRecoverProtectiveAccessibility :
  INF.FactorsThrough riskOnlyObserver protectiveAccessConsumer → ⊥
riskCatalogueCannotRecoverProtectiveAccessibility =
  INF.witnessRulesOutEveryFlatFactorisation riskOnlyNonFactorability

------------------------------------------------------------------------
-- INTERSECTIONAL / SITUATED REPAIR
--
-- A nominal reason label ("pet", "concert", "birthday", "sibling", etc.) is
-- not itself the protective relation.  Access, relationship, timing, safety,
-- material conditions, culture, disability/accessibility, and other situated
-- coordinates may alter the relevant consumer answer.  The theorem below only
-- says a one-label quotient cannot recover a distinction it has erased.
------------------------------------------------------------------------

data SituatedReasonState : Set where
  sameReasonLabelNoCurrentAccess : SituatedReasonState
  sameReasonLabelWithCurrentAccess : SituatedReasonState

data ReasonLabelSurface : Set where
  ordinaryAttachmentLabel : ReasonLabelSurface

reasonLabelObserver : SituatedReasonState → ReasonLabelSurface
reasonLabelObserver sameReasonLabelNoCurrentAccess = ordinaryAttachmentLabel
reasonLabelObserver sameReasonLabelWithCurrentAccess = ordinaryAttachmentLabel

situatedReasonAccessibility : SituatedReasonState → Bool
situatedReasonAccessibility sameReasonLabelNoCurrentAccess = false
situatedReasonAccessibility sameReasonLabelWithCurrentAccess = true

situatedReasonDiffers :
  situatedReasonAccessibility sameReasonLabelNoCurrentAccess ≡
  situatedReasonAccessibility sameReasonLabelWithCurrentAccess → ⊥
situatedReasonDiffers ()

singleReasonLabelNonFactorability :
  INF.NonFactorabilityWitness reasonLabelObserver situatedReasonAccessibility
singleReasonLabelNonFactorability = INF.nonFactorabilityWitness
  sameReasonLabelNoCurrentAccess
  sameReasonLabelWithCurrentAccess
  refl
  situatedReasonDiffers

singleReasonLabelCannotRecoverSituatedAccessibility :
  INF.FactorsThrough reasonLabelObserver situatedReasonAccessibility → ⊥
singleReasonLabelCannotRecoverSituatedAccessibility =
  INF.witnessRulesOutEveryFlatFactorisation singleReasonLabelNonFactorability

------------------------------------------------------------------------
-- WRONGTYPE: WELL-FORMED / TRUE-ISH CONTENT != ADMISSIBLE COMMUNICATION
--
-- A message can be grammatical, cited, and even contain true propositions but
-- still be the wrong candidate for a public-health communication obligation if
-- it violates the required safety/guidance consumer.  Conversely, rejection
-- under that consumer does not prove every proposition in the message false.
------------------------------------------------------------------------

safeSuicidePreventionCommunicationObligation : WrongType.IndexedObligation
safeSuicidePreventionCommunicationObligation = WrongType.indexed-obligation
  WrongType.admissibleTransitionObligation
  "suicide-prevention-media-safety"
  "WHO-2023 responsible suicide-prevention communication consumer"
  "public/social-media suicide-prevention narrative"

methodCentredWellFormedCandidate : WrongType.OfferedCandidate
methodCentredWellFormedCandidate = WrongType.offered-candidate
  "method-centred-suicide-story"
  "well-formed public narrative"
  "creator/media item"
  true

methodCentredIsWrongTypeForSafetyConsumer : WrongType.WrongTypeErrorReceipt
methodCentredIsWrongTypeForSafetyConsumer = WrongType.wrong-type-error-receipt
  safeSuicidePreventionCommunicationObligation
  methodCentredWellFormedCandidate
  WrongType.inadmissibleCandidate
  "fails safe-communication admission despite syntactic well-formedness"
  true

------------------------------------------------------------------------
-- ADMISSIBLE TRANSITION VIEW
--
-- Publication is modelled as a situated transition, not a scalar score.  A
-- transition must first be enabled by a safety obligation; only then may other
-- ranking/engagement/effect weights be considered.  This reuses the existing
-- repo-native AdmissibleTransitionSystem rather than inventing a second notion
-- of admissibility.
------------------------------------------------------------------------

data CommunicationState : Set where
  preventionContext : CommunicationState

data CommunicationParameter : Set where
  publicAudience : CommunicationParameter

data CommunicationMove : Set where
  publishCopingAndHelpSeekingNarrative : CommunicationMove
  publishMethodCentredNarrative : CommunicationMove

SafeEnabled :
  CommunicationMove → CommunicationParameter → CommunicationState → Set
SafeEnabled publishCopingAndHelpSeekingNarrative publicAudience preventionContext = ⊤
SafeEnabled publishMethodCentredNarrative publicAudience preventionContext = ⊥

communicationStep :
  CommunicationMove → CommunicationParameter → CommunicationState → CommunicationState
communicationStep publishCopingAndHelpSeekingNarrative publicAudience preventionContext = preventionContext
communicationStep publishMethodCentredNarrative publicAudience preventionContext = preventionContext

PreventionInvariant : CommunicationState → Set
PreventionInvariant preventionContext = ⊤

communicationPreservesInvariant :
  (move : CommunicationMove) →
  (parameter : CommunicationParameter) →
  (state : CommunicationState) →
  SafeEnabled move parameter state →
  PreventionInvariant state →
  PreventionInvariant (communicationStep move parameter state)
communicationPreservesInvariant publishCopingAndHelpSeekingNarrative publicAudience preventionContext enabled invariant = tt
communicationPreservesInvariant publishMethodCentredNarrative publicAudience preventionContext () invariant

safeCommunicationSystem : Admissible.AdmissibleTransitionSystem
safeCommunicationSystem = Admissible.admissibleTransitionSystem
  CommunicationState
  CommunicationParameter
  CommunicationMove
  SafeEnabled
  communicationStep
  PreventionInvariant
  communicationPreservesInvariant
  "WHO-guided suicide-prevention public-communication admission"

copingNarrativeIsAdmitted :
  Admissible.AdmittedStep
    safeCommunicationSystem
    publishCopingAndHelpSeekingNarrative
    publicAudience
    preventionContext
copingNarrativeIsAdmitted = Admissible.admittedStep tt tt

methodCentredNarrativeIsDisabled :
  SafeEnabled publishMethodCentredNarrative publicAudience preventionContext → ⊥
methodCentredNarrativeIsDisabled ()

methodCentredNarrativeCannotBeAdmitted :
  Admissible.AdmittedStep
    safeCommunicationSystem
    publishMethodCentredNarrative
    publicAudience
    preventionContext → ⊥
methodCentredNarrativeCannotBeAdmitted =
  Admissible.disabledExcludesAdmittedStep methodCentredNarrativeIsDisabled

------------------------------------------------------------------------
-- NO-PROMOTION FIREWALLS
------------------------------------------------------------------------

data OneOrdinaryReasonGuaranteesSurvival : Set where
data ProtectiveAssociationPredictsIndividualOutcome : Set where
data SourceCitationMakesCommunicationSafe : Set where
data RiskScoreDeterminesProtectiveResources : Set where
data DemographicLabelDeterminesProtectiveAccess : Set where
\data CreatorGlossEqualsPrimaryStudyResult : Set where

oneReasonDoesNotGuaranteeSurvival : OneOrdinaryReasonGuaranteesSurvival → ⊥
oneReasonDoesNotGuaranteeSurvival ()

populationAssociationDoesNotPredictIndividualOutcome :
  ProtectiveAssociationPredictsIndividualOutcome → ⊥
populationAssociationDoesNotPredictIndividualOutcome ()

citationDoesNotAutoAdmitCommunication : SourceCitationMakesCommunicationSafe → ⊥
citationDoesNotAutoAdmitCommunication ()

riskScoreDoesNotDetermineProtectiveResources : RiskScoreDeterminesProtectiveResources → ⊥
riskScoreDoesNotDetermineProtectiveResources ()

demographicLabelDoesNotDetermineProtectiveAccess :
  DemographicLabelDeterminesProtectiveAccess → ⊥
demographicLabelDoesNotDetermineProtectiveAccess ()

creatorGlossDoesNotBecomePrimaryResult : CreatorGlossEqualsPrimaryStudyResult → ⊥
creatorGlossDoesNotBecomePrimaryResult ()

------------------------------------------------------------------------
-- CROSS-POLLINATION BOUNDARY
------------------------------------------------------------------------

record ProtectiveNarrativeCrossPollinationBoundary : Set where
  constructor protective-narrative-cross-pollination-boundary
  field
    reasonsForLivingIsDistinctConsumerFromRiskCatalogue : Bool
    riskOnlyFactorsThroughProtectiveAccessibility : Bool
    ordinaryReasonLabelIsSituatedProtectiveRelation : Bool
    wellFormedMessageIsAutomaticallyAdmissible : Bool
    wrongTypeCanMeanSafeCommunicationObligationMismatch : Bool
    admissibilityPrecedesEffectOrEngagementWeight : Bool
    populationAssociationPredictsIndividualOutcome : Bool
    creatorInterpretationEqualsPrimarySource : Bool
open ProtectiveNarrativeCrossPollinationBoundary public

canonicalProtectiveNarrativeCrossPollinationBoundary :
  ProtectiveNarrativeCrossPollinationBoundary
canonicalProtectiveNarrativeCrossPollinationBoundary =
  protective-narrative-cross-pollination-boundary
    true
    false
    false
    false
    true
    true
    false
    false
