module DASHI.Reasoning.FolkLawEpistemicAuthorityBroadExact where

------------------------------------------------------------------------
-- Broad structural formalisation of the thread's legal-epistemic theory.
--
-- This module extends FolkLawEpistemicAuthorityCaptureExact rather than
-- replacing it.  It adds the pieces exposed by the broader discussion:
--
--   * socially learned anchors constrain which models are live;
--   * before refinement, folk and institutional models can form a genuine
--     Pareto trade-off rather than one simply dominating the other;
--   * verified explanation can refine the feasible model set;
--   * public rule visibility and captured interpretive authority can coexist;
--   * the Go/chess distinction is a non-descent theorem: an institutional
--     evaluator cannot in general be reconstructed from the folk observer;
--   * AI can enlarge the available action language while leaving the coarse
--     observer unchanged.
--
-- The module makes structural claims only.  It does not certify a historical
-- genealogy, a legal conclusion, or a psychological state in any person.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Reasoning.FolkLawEpistemicAuthorityCaptureExact as Base

------------------------------------------------------------------------
-- 1. Socially learned anchors and the live model set
------------------------------------------------------------------------

data LearnedAnchor : Set where
  sixMonthSurfaceRule : LearnedAnchor
  institutionsCanErr  : LearnedAnchor
  defendYourPosition  : LearnedAnchor

data AnchorStatus : Set where
  sociallySettled : AnchorStatus
  locallyTentative : AnchorStatus

anchorStatus : LearnedAnchor → AnchorStatus
anchorStatus sixMonthSurfaceRule = sociallySettled
anchorStatus institutionsCanErr  = sociallySettled
anchorStatus defendYourPosition  = sociallySettled

data CandidateModel : Set where
  folkModel          : CandidateModel
  institutionalModel : CandidateModel

data Dimension : Set where
  anchorFit       : Dimension
  evidenceFit     : Dimension
  revisionEase    : Dimension
  actionability   : Dimension

data Comparison : Set where
  leftBetter  : Comparison
  rightBetter : Comparison
  tied        : Comparison

preRefinementComparison : Dimension → Comparison
preRefinementComparison anchorFit     = leftBetter
preRefinementComparison evidenceFit   = rightBetter
preRefinementComparison revisionEase  = leftBetter
preRefinementComparison actionability = tied

record PreRefinementParetoTradeoff : Set where
  constructor preRefinementParetoTradeoff
  field
    folkHasAnchorAdvantage :
      preRefinementComparison anchorFit ≡ leftBetter
    folkHasRevisionEaseAdvantage :
      preRefinementComparison revisionEase ≡ leftBetter
    institutionHasEvidenceAdvantage :
      preRefinementComparison evidenceFit ≡ rightBetter
    neitherWinsActionability :
      preRefinementComparison actionability ≡ tied

canonicalPreRefinementTradeoff : PreRefinementParetoTradeoff
canonicalPreRefinementTradeoff =
  preRefinementParetoTradeoff refl refl refl refl

BeforeFeasible : CandidateModel → Set
BeforeFeasible folkModel          = ⊤
BeforeFeasible institutionalModel = ⊤

AfterVerifiedRefinementFeasible : CandidateModel → Set
AfterVerifiedRefinementFeasible folkModel          = ⊥
AfterVerifiedRefinementFeasible institutionalModel = ⊤

bothModelsInitiallyLive :
  BeforeFeasible folkModel × BeforeFeasible institutionalModel
bothModelsInitiallyLive = tt , tt

verifiedRefinementCanRemoveFolkModel :
  AfterVerifiedRefinementFeasible folkModel → ⊥
verifiedRefinementCanRemoveFolkModel impossible = impossible

institutionalModelRemainsFeasibleAfterRefinement :
  AfterVerifiedRefinementFeasible institutionalModel
institutionalModelRemainsFeasibleAfterRefinement = tt

------------------------------------------------------------------------
-- 2. Public rules can coexist with captured interpretation
------------------------------------------------------------------------

data RuleVisibility : Set where
  embeddedRulePractice : RuleVisibility
  publicRuleSurface    : RuleVisibility

record AuthorityProfile : Set where
  constructor authorityProfile
  field
    normMemorySeat          : Base.AuthoritySeat
    ruleVisibility          : RuleVisibility
    positionEvaluationSeat  : Base.AuthoritySeat
    bindingMeaningSeat      : Base.AuthoritySeat

open AuthorityProfile public

embeddedProfile : AuthorityProfile
embeddedProfile =
  authorityProfile
    Base.withinCommunity
    embeddedRulePractice
    Base.withinCommunity
    Base.withinCommunity

capturedPublicProfile : AuthorityProfile
capturedPublicProfile =
  authorityProfile
    Base.withinCommunity
    publicRuleSurface
    Base.differentiatedInstitution
    Base.differentiatedInstitution

record CaptureWithoutSecrecy : Set where
  constructor captureWithoutSecrecy
  field
    communityNormMemoryPersists :
      normMemorySeat embeddedProfile ≡ Base.withinCommunity ×
      normMemorySeat capturedPublicProfile ≡ Base.withinCommunity
    rulesBecomePublic :
      ruleVisibility capturedPublicProfile ≡ publicRuleSurface
    evaluationMovesInstitutional :
      positionEvaluationSeat capturedPublicProfile ≡
        Base.differentiatedInstitution
    bindingMeaningMovesInstitutional :
      bindingMeaningSeat capturedPublicProfile ≡
        Base.differentiatedInstitution

canonicalCaptureWithoutSecrecy : CaptureWithoutSecrecy
canonicalCaptureWithoutSecrecy =
  captureWithoutSecrecy (refl , refl) refl refl refl

------------------------------------------------------------------------
-- 3. Go-like non-descent: expert evaluation is not reconstructible from the
--    coarse folk observer in general.
------------------------------------------------------------------------

institutionalObserverDoesNotDescendThroughFolk :
  (reconstruct : Base.FolkObservation → Base.InstitutionalObservation) →
  ((state : Base.FineLegalState) →
    reconstruct (Base.folkObserver state) ≡ Base.institutionalObserver state) →
  ⊥
institutionalObserverDoesNotDescendThroughFolk reconstruct correct =
  Base.institutionViableNotNoProspect
    (trans
      (sym (correct Base.viableState))
      (correct Base.noProspectState))

record GoLikeEvaluationSeparation : Set where
  constructor goLikeEvaluationSeparation
  field
    ruleSurfaceMayBePublic : Bool
    ruleSurfaceMayBePublicIsTrue : ruleSurfaceMayBePublic ≡ true
    folkObserverMayStillCollide : Bool
    folkObserverMayStillCollideIsTrue : folkObserverMayStillCollide ≡ true
    institutionalEvaluationNeedNotDescend : Bool
    institutionalEvaluationNeedNotDescendIsTrue :
      institutionalEvaluationNeedNotDescend ≡ true

canonicalGoLikeEvaluationSeparation : GoLikeEvaluationSeparation
canonicalGoLikeEvaluationSeparation =
  goLikeEvaluationSeparation true refl true refl true refl

------------------------------------------------------------------------
-- 4. Objective apparentness, actual comprehension, and verified refinement
------------------------------------------------------------------------

broadObjectiveWitness : Base.ObjectivePersistenceGateway Base.objectiveWithoutComprehension
broadObjectiveWitness = Base.objectiveWitnessGateway

broadObjectiveWitnessNotComprehended :
  Base.ActuallyComprehended Base.objectiveWithoutComprehension → ⊥
broadObjectiveWitnessNotComprehended = Base.objectiveWitnessNotComprehended

verifiedConversationProducesComprehension :
  (state : Base.CommunicationState) →
  Base.ActuallyComprehended (Base.verifiedConversation state)
verifiedConversationProducesComprehension = Base.verifiedConversationComprehended

verifiedConversationStopsPersistence :
  (state : Base.CommunicationState) →
  Base.persisted (Base.verifiedConversation state) ≡ false
verifiedConversationStopsPersistence = Base.verifiedConversationStopsPersistence

------------------------------------------------------------------------
-- 5. AI actuation can enlarge the action language while the observer remains
--    unchanged. This deliberately does NOT state that a larger action set
--    worsens ideal optimal utility: old actions remain available.
------------------------------------------------------------------------

data LegalAction : Set where
  plainContinue  : LegalAction
  ornateContinue : LegalAction
  withdraw       : LegalAction

data Capability : Set where
  unaidedCapability : Capability
  aiAidedCapability : Capability

Available : Capability → LegalAction → Set
Available unaidedCapability plainContinue  = ⊤
Available unaidedCapability ornateContinue = ⊥
Available unaidedCapability withdraw       = ⊤
Available aiAidedCapability plainContinue  = ⊤
Available aiAidedCapability ornateContinue = ⊤
Available aiAidedCapability withdraw       = ⊤

baselinePlainAvailable : Available unaidedCapability plainContinue
baselinePlainAvailable = tt

baselineWithdrawAvailable : Available unaidedCapability withdraw
baselineWithdrawAvailable = tt

ornateUnavailableWithoutAI : Available unaidedCapability ornateContinue → ⊥
ornateUnavailableWithoutAI impossible = impossible

ornateAvailableWithAI : Available aiAidedCapability ornateContinue
ornateAvailableWithAI = tt

capabilityDoesNotRefineFolkObserver :
  (capability : Capability) →
  Observer.Observer Base.FineLegalState Base.FolkObservation
capabilityDoesNotRefineFolkObserver unaidedCapability = Base.folkObserver
capabilityDoesNotRefineFolkObserver aiAidedCapability = Base.folkObserver

sameFolkObservationAcrossCapabilities :
  (state : Base.FineLegalState) →
  capabilityDoesNotRefineFolkObserver unaidedCapability state ≡
  capabilityDoesNotRefineFolkObserver aiAidedCapability state
sameFolkObservationAcrossCapabilities state = refl

record EpistemicActuationBoundary : Set where
  constructor epistemicActuationBoundary
  field
    aiCanAddReachableAction : Bool
    aiCanAddReachableActionIsTrue : aiCanAddReachableAction ≡ true
    aiNecessarilyRefinesObserver : Bool
    aiNecessarilyRefinesObserverIsFalse : aiNecessarilyRefinesObserver ≡ false
    enlargedActionSetNecessarilyLowersOptimalUtility : Bool
    enlargedActionSetNecessarilyLowersOptimalUtilityIsFalse :
      enlargedActionSetNecessarilyLowersOptimalUtility ≡ false

canonicalEpistemicActuationBoundary : EpistemicActuationBoundary
canonicalEpistemicActuationBoundary =
  epistemicActuationBoundary true refl false refl false refl

------------------------------------------------------------------------
-- Broad boundary receipt
------------------------------------------------------------------------

record BroadEpistemicAuthorityBoundary : Set where
  constructor broadEpistemicAuthorityBoundary
  field
    learnedAnchorsConstrainLiveModels : Bool
    learnedAnchorsConstrainLiveModelsIsTrue :
      learnedAnchorsConstrainLiveModels ≡ true
    preRefinementTradeoffCanKeepMultipleModelsLive : Bool
    preRefinementTradeoffCanKeepMultipleModelsLiveIsTrue :
      preRefinementTradeoffCanKeepMultipleModelsLive ≡ true
    publicRulesAndCapturedInterpretationCanCoexist : Bool
    publicRulesAndCapturedInterpretationCanCoexistIsTrue :
      publicRulesAndCapturedInterpretationCanCoexist ≡ true
    folkObserverNeedNotDetermineInstitutionalEvaluation : Bool
    folkObserverNeedNotDetermineInstitutionalEvaluationIsTrue :
      folkObserverNeedNotDetermineInstitutionalEvaluation ≡ true
    verificationCanRefineFeasibleModelSet : Bool
    verificationCanRefineFeasibleModelSetIsTrue :
      verificationCanRefineFeasibleModelSet ≡ true
    actionCapabilityCanIncreaseWithoutObserverRefinement : Bool
    actionCapabilityCanIncreaseWithoutObserverRefinementIsTrue :
      actionCapabilityCanIncreaseWithoutObserverRefinement ≡ true

canonicalBroadEpistemicAuthorityBoundary : BroadEpistemicAuthorityBoundary
canonicalBroadEpistemicAuthorityBoundary =
  broadEpistemicAuthorityBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
