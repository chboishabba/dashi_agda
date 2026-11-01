module DASHI.Reasoning.FolkLawEpistemicAuthorityCaptureExact where

------------------------------------------------------------------------
-- Folk-law / institutional-law epistemic authority capture.
--
-- This is a structural model, not a historical claim about one particular
-- legal system and not legal advice.  It formalises the distinctions developed
-- in the accompanying thread:
--
--   * a coarse folk observer can be adequate for ordinary socialisation while
--     failing to distinguish states that an institutional decision procedure
--     distinguishes;
--   * publication/receipt of a rule is not the same thing as competent
--     evaluation of a position under that rule (the chess/Go distinction);
--   * objective/imputed apparentness is not actual comprehension;
--   * verified comprehension is therefore a genuinely additional observer;
--   * epistemic capture is represented as migration of authoritative
--     interpretation from a within-community seat to a differentiated
--     institutional seat, while community-level normative knowledge can remain.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- 1. Fine legal state versus socially learned folk-law surface
------------------------------------------------------------------------

data FineLegalState : Set where
  viableState     : FineLegalState
  noProspectState : FineLegalState

data FolkObservation : Set where
  looksEligible : FolkObservation

data InstitutionalObservation : Set where
  institutionSeesViable     : InstitutionalObservation
  institutionSeesNoProspect : InstitutionalObservation

folkObserver : Observer.Observer FineLegalState FolkObservation
folkObserver viableState     = looksEligible
folkObserver noProspectState = looksEligible

institutionalObserver :
  Observer.Observer FineLegalState InstitutionalObservation
institutionalObserver viableState     = institutionSeesViable
institutionalObserver noProspectState = institutionSeesNoProspect

viableNotNoProspect : viableState ≡ noProspectState → ⊥
viableNotNoProspect ()

institutionViableNotNoProspect :
  institutionSeesViable ≡ institutionSeesNoProspect → ⊥
institutionViableNotNoProspect ()

folkCollision : Observer.ObserverCollision folkObserver
folkCollision =
  Observer.observerCollision
    viableState
    noProspectState
    refl
    viableNotNoProspect

folkObserverNotSeparating : Observer.Separating folkObserver → ⊥
folkObserverNotSeparating = Observer.collisionBlocksSeparation folkCollision

institutionalObserverSeparating : Observer.Separating institutionalObserver
institutionalObserverSeparating viableState viableState equality = refl
institutionalObserverSeparating viableState noProspectState ()
institutionalObserverSeparating noProspectState viableState ()
institutionalObserverSeparating noProspectState noProspectState equality = refl

institutionRefinesFolk :
  Observer.Refines folkObserver institutionalObserver
institutionRefinesFolk x y equality = refl

institutionStrictlyRefinesFolk :
  Observer.StrictRefinement folkObserver institutionalObserver
institutionStrictlyRefinesFolk =
  Observer.strictRefinement
    institutionRefinesFolk
    viableState
    noProspectState
    refl
    institutionViableNotNoProspect

------------------------------------------------------------------------
-- 2. Public rules do not imply public position-evaluation competence.
--
-- This is the chess/Go point.  A tiny/public rule surface may coexist with a
-- much richer state evaluator.  The important failure is not lexical: the
-- coarse observer simply cannot compute every institutionally relevant result.
------------------------------------------------------------------------

data LegalOutcome : Set where
  proceedingLive : LegalOutcome
  proceedingLost : LegalOutcome

institutionalOutcome : FineLegalState → LegalOutcome
institutionalOutcome viableState     = proceedingLive
institutionalOutcome noProspectState = proceedingLost

liveNotLost : proceedingLive ≡ proceedingLost → ⊥
liveNotLost ()

institutionalOutcomeDoesNotDescendThroughFolk :
  (folkEvaluator : FolkObservation → LegalOutcome) →
  ((state : FineLegalState) →
    folkEvaluator (folkObserver state) ≡ institutionalOutcome state) →
  ⊥
institutionalOutcomeDoesNotDescendThroughFolk folkEvaluator correct =
  liveNotLost
    (trans
      (sym (correct viableState))
      (correct noProspectState))

record GoLikeOpacityBoundary : Set where
  constructor goLikeOpacityBoundary
  field
    explicitRuleSurfacePublic : Bool
    explicitRuleSurfacePublicIsTrue : explicitRuleSurfacePublic ≡ true
    folkSurfaceSeparatesPositions : Bool
    folkSurfaceSeparatesPositionsIsFalse :
      folkSurfaceSeparatesPositions ≡ false
    expertSurfaceSeparatesPositions : Bool
    expertSurfaceSeparatesPositionsIsTrue :
      expertSurfaceSeparatesPositions ≡ true

canonicalGoLikeOpacityBoundary : GoLikeOpacityBoundary
canonicalGoLikeOpacityBoundary =
  goLikeOpacityBoundary true refl false refl true refl

------------------------------------------------------------------------
-- 3. Receipt, objective apparentness, comprehension, persistence.
------------------------------------------------------------------------

record CommunicationState : Set where
  constructor communicationState
  field
    received            : Bool
    reasonablyApparent  : Bool
    comprehended        : Bool
    persisted           : Bool

open CommunicationState public

Received : CommunicationState → Set
Received state = received state ≡ true

ApparentlyNoProspect : CommunicationState → Set
ApparentlyNoProspect state = reasonablyApparent state ≡ true

ActuallyComprehended : CommunicationState → Set
ActuallyComprehended state = comprehended state ≡ true

Persists : CommunicationState → Set
Persists state = persisted state ≡ true

ObjectivePersistenceGateway : CommunicationState → Set
ObjectivePersistenceGateway state =
  ApparentlyNoProspect state × Persists state

VerifiedPersistenceGateway : CommunicationState → Set
VerifiedPersistenceGateway state =
  ActuallyComprehended state × Persists state

-- Canonical witness: information was received and the institutional inference
-- is objectively available, yet actual comprehension is absent and persistence
-- continues.  This is exactly the distinction an "ought to have known" test
-- can erase if receipt/apparentness is treated as comprehension.
objectiveWithoutComprehension : CommunicationState
objectiveWithoutComprehension =
  communicationState true true false true

objectiveWitnessReceived : Received objectiveWithoutComprehension
objectiveWitnessReceived = refl

objectiveWitnessGateway :
  ObjectivePersistenceGateway objectiveWithoutComprehension
objectiveWitnessGateway = refl , refl

objectiveWitnessNotComprehended :
  ActuallyComprehended objectiveWithoutComprehension → ⊥
objectiveWitnessNotComprehended ()

receiptDoesNotEntailComprehension :
  ((state : CommunicationState) → Received state → ActuallyComprehended state) →
  ⊥
receiptDoesNotEntailComprehension entail =
  objectiveWitnessNotComprehended
    (entail objectiveWithoutComprehension objectiveWitnessReceived)

objectiveGatewayDoesNotEntailActualComprehension :
  ((state : CommunicationState) →
    ObjectivePersistenceGateway state →
    ActuallyComprehended state) →
  ⊥
objectiveGatewayDoesNotEntailActualComprehension entail =
  objectiveWitnessNotComprehended
    (entail objectiveWithoutComprehension objectiveWitnessGateway)

------------------------------------------------------------------------
-- 4. Verification/teach-back adds an observer rather than merely another copy
--    of the original message.
--
-- `verifiedConversation` is a policy specimen: it models a successful
-- synchronous explanation/teach-back event followed by withdrawal.  It does
-- not claim that every conversation causes withdrawal.
------------------------------------------------------------------------

verifiedConversation : CommunicationState → CommunicationState
verifiedConversation state =
  communicationState true (reasonablyApparent state) true false

verifiedConversationIsReceived :
  (state : CommunicationState) →
  Received (verifiedConversation state)
verifiedConversationIsReceived state = refl

verifiedConversationComprehended :
  (state : CommunicationState) →
  ActuallyComprehended (verifiedConversation state)
verifiedConversationComprehended state = refl

verifiedConversationStopsPersistence :
  (state : CommunicationState) →
  persisted (verifiedConversation state) ≡ false
verifiedConversationStopsPersistence state = refl

------------------------------------------------------------------------
-- 5. Structural epistemic capture of authority.
------------------------------------------------------------------------

data AuthoritySeat : Set where
  withinCommunity             : AuthoritySeat
  differentiatedInstitution   : AuthoritySeat

record AuthorityAllocation : Set where
  constructor authorityAllocation
  field
    normMemorySeat          : AuthoritySeat
    interpretiveSeat        : AuthoritySeat
    adjudicativeSeat        : AuthoritySeat

open AuthorityAllocation public

embeddedCommunityAuthority : AuthorityAllocation
embeddedCommunityAuthority =
  authorityAllocation withinCommunity withinCommunity withinCommunity

capturedInterpretiveAuthority : AuthorityAllocation
capturedInterpretiveAuthority =
  authorityAllocation withinCommunity differentiatedInstitution differentiatedInstitution

record EpistemicCapture
    (before after : AuthorityAllocation) : Set where
  constructor epistemicCapture
  field
    communityNormMemoryPersists :
      normMemorySeat before ≡ withinCommunity ×
      normMemorySeat after ≡ withinCommunity
    interpretationStartsWithin :
      interpretiveSeat before ≡ withinCommunity
    interpretationMovesOutside :
      interpretiveSeat after ≡ differentiatedInstitution

open EpistemicCapture public

canonicalEpistemicCapture :
  EpistemicCapture embeddedCommunityAuthority capturedInterpretiveAuthority
canonicalEpistemicCapture =
  epistemicCapture (refl , refl) refl refl

------------------------------------------------------------------------
-- Boundary receipt: the formal claims intentionally stop at structural facts.
------------------------------------------------------------------------

record FolkLawEpistemicAuthorityBoundary : Set where
  constructor folkLawEpistemicAuthorityBoundary
  field
    folkObserverCanCollapseInstitutionallyDistinctStates : Bool
    folkObserverCanCollapseInstitutionallyDistinctStatesIsTrue :
      folkObserverCanCollapseInstitutionallyDistinctStates ≡ true
    publicRulesGuaranteePositionCompetence : Bool
    publicRulesGuaranteePositionCompetenceIsFalse :
      publicRulesGuaranteePositionCompetence ≡ false
    receiptGuaranteesComprehension : Bool
    receiptGuaranteesComprehensionIsFalse :
      receiptGuaranteesComprehension ≡ false
    objectiveApparentnessEqualsActualComprehension : Bool
    objectiveApparentnessEqualsActualComprehensionIsFalse :
      objectiveApparentnessEqualsActualComprehension ≡ false
    verificationAddsEpistemicInformation : Bool
    verificationAddsEpistemicInformationIsTrue :
      verificationAddsEpistemicInformation ≡ true

canonicalFolkLawEpistemicAuthorityBoundary : FolkLawEpistemicAuthorityBoundary
canonicalFolkLawEpistemicAuthorityBoundary =
  folkLawEpistemicAuthorityBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
