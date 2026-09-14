module DASHI.Law.SensibLawTreatyParticipationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- TREATY PARTICIPATION / STATE-BINDING REFINEMENT
--
-- Scope:
--   parent-convention participation != protocol participation
--   consent/deposit != date of effect
--   State binding != event-level applicability.
--
-- This carrier is intentionally generic.  Concrete participation facts must be
-- paid by a depositary or equivalently authoritative primary source.
------------------------------------------------------------------------

data ParticipationStatus : Set where
  participationUnresolved : ParticipationStatus
  signatoryOnly : ParticipationStatus
  consentDepositedNotYetEffective : ParticipationStatus
  boundForState : ParticipationStatus
  notBoundForState : ParticipationStatus

data ConsentMode : Set where
  consentModeUnresolved : ConsentMode
  signatureMode : ConsentMode
  ratificationMode : ConsentMode
  acceptanceMode : ConsentMode
  approvalMode : ConsentMode
  accessionMode : ConsentMode
  successionMode : ConsentMode
  otherRecordedConsentMode : ConsentMode

record StateInstrumentParticipation : Set where
  constructor stateInstrumentParticipation
  field
    participantLabel : String
    instrumentLabel : String
    participationStatus : ParticipationStatus
    consentMode : ConsentMode
    depositDate : String
    effectiveDateForState : String
    depositarySourceRef : String

open StateInstrumentParticipation public

------------------------------------------------------------------------
-- Exact projection defect I:
-- being a party to a parent convention does not determine whether the same
-- State is bound by a particular annexed protocol.
------------------------------------------------------------------------

data ParticipationWorld : Set where
  parentPartyProtocolNotBound : ParticipationWorld
  parentPartyProtocolBound : ParticipationWorld

data ParentConventionSurface : Set where
  sameParentConventionParty : ParentConventionSurface

data ProtocolParticipationSurface : Set where
  protocolNotBound : ProtocolParticipationSurface
  protocolBound : ProtocolParticipationSurface

data ParticipationQuery : Set where
  parentConventionPartyQuery : ParticipationQuery
  protocolBindingQuery : ParticipationQuery

data ParticipationAnswer : Set where
  parentConventionPartyObserved : ParticipationAnswer
  protocolBindingNotEstablished : ParticipationAnswer
  protocolBindingEstablished : ParticipationAnswer

parentConventionOnlyProjection : ParticipationWorld → ParentConventionSurface
parentConventionOnlyProjection world = sameParentConventionParty

protocolParticipationProjection : ParticipationWorld → ProtocolParticipationSurface
protocolParticipationProjection parentPartyProtocolNotBound = protocolNotBound
protocolParticipationProjection parentPartyProtocolBound = protocolBound

participationAnswer : ParticipationQuery → ParticipationWorld → ParticipationAnswer
participationAnswer parentConventionPartyQuery world = parentConventionPartyObserved
participationAnswer protocolBindingQuery parentPartyProtocolNotBound =
  protocolBindingNotEstablished
participationAnswer protocolBindingQuery parentPartyProtocolBound =
  protocolBindingEstablished

participationSemantics :
  Adequacy.QuerySemantics ParticipationWorld ParticipationQuery ParticipationAnswer
participationSemantics = Adequacy.querySemantics participationAnswer

parentConventionOnlyProtocolBindingAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    parentConventionOnlyProjection
    participationSemantics
    protocolBindingQuery
parentConventionOnlyProtocolBindingAdequacyDefect =
  Adequacy.queryAdequacyDefect
    parentPartyProtocolNotBound
    parentPartyProtocolBound
    refl
    (λ ())

parentConventionPartyCannotDetermineProtocolBinding :
  Adequacy.AdequateFor
    parentConventionOnlyProjection
    participationSemantics
    protocolBindingQuery →
  ⊥
parentConventionPartyCannotDetermineProtocolBinding =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    parentConventionOnlyProtocolBindingAdequacyDefect

parentAndProtocolProjection :
  ParticipationWorld → ParentConventionSurface × ProtocolParticipationSurface
parentAndProtocolProjection =
  Observer.pairObserver parentConventionOnlyProjection protocolParticipationProjection

joinedProtocolBindingAnswer :
  ParentConventionSurface × ProtocolParticipationSurface → ParticipationAnswer
joinedProtocolBindingAnswer (sameParentConventionParty , protocolNotBound) =
  protocolBindingNotEstablished
joinedProtocolBindingAnswer (sameParentConventionParty , protocolBound) =
  protocolBindingEstablished

parentAndProtocolDetermineBinding :
  Adequacy.AdequateFor
    parentAndProtocolProjection
    participationSemantics
    protocolBindingQuery
parentAndProtocolDetermineBinding =
  Adequacy.factorsForQuery
    joinedProtocolBindingAnswer
    (λ { parentPartyProtocolNotBound → refl
       ; parentPartyProtocolBound → refl
       })

parentAndProtocolStrictlyRefinesParentParty :
  Observer.StrictRefinement
    parentConventionOnlyProjection
    parentAndProtocolProjection
parentAndProtocolStrictlyRefinesParentParty =
  Observer.strictPairRefinement
    parentConventionOnlyProjection
    protocolParticipationProjection
    parentPartyProtocolNotBound
    parentPartyProtocolBound
    refl
    (λ ())

------------------------------------------------------------------------
-- Exact projection defect II:
-- even where the State is bound, applicability to a particular event still
-- depends on an independent factual/legal context coordinate.
------------------------------------------------------------------------

data ApplicabilityWorld : Set where
  boundStateEventOutsideScope : ApplicabilityWorld
  boundStateEventInsideScope : ApplicabilityWorld

data StateBindingSurface : Set where
  sameBoundState : StateBindingSurface

data EventContextSurface : Set where
  eventOutsideInstrumentScope : EventContextSurface
  eventInsideInstrumentScope : EventContextSurface

data EventApplicabilityQuery : Set where
  stateBindingQuery : EventApplicabilityQuery
  eventApplicabilityQuery : EventApplicabilityQuery

data EventApplicabilityAnswer : Set where
  stateBoundObserved : EventApplicabilityAnswer
  eventNotApplicable : EventApplicabilityAnswer
  eventApplicable : EventApplicabilityAnswer

stateBindingOnlyProjection : ApplicabilityWorld → StateBindingSurface
stateBindingOnlyProjection world = sameBoundState

eventContextProjection : ApplicabilityWorld → EventContextSurface
eventContextProjection boundStateEventOutsideScope = eventOutsideInstrumentScope
eventContextProjection boundStateEventInsideScope = eventInsideInstrumentScope

eventApplicabilityAnswer :
  EventApplicabilityQuery → ApplicabilityWorld → EventApplicabilityAnswer
eventApplicabilityAnswer stateBindingQuery world = stateBoundObserved
eventApplicabilityAnswer eventApplicabilityQuery boundStateEventOutsideScope =
  eventNotApplicable
eventApplicabilityAnswer eventApplicabilityQuery boundStateEventInsideScope =
  eventApplicable

eventApplicabilitySemantics :
  Adequacy.QuerySemantics ApplicabilityWorld EventApplicabilityQuery EventApplicabilityAnswer
eventApplicabilitySemantics = Adequacy.querySemantics eventApplicabilityAnswer

stateBindingOnlyEventApplicabilityAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    stateBindingOnlyProjection
    eventApplicabilitySemantics
    eventApplicabilityQuery
stateBindingOnlyEventApplicabilityAdequacyDefect =
  Adequacy.queryAdequacyDefect
    boundStateEventOutsideScope
    boundStateEventInsideScope
    refl
    (λ ())

stateBindingCannotDetermineEventApplicability :
  Adequacy.AdequateFor
    stateBindingOnlyProjection
    eventApplicabilitySemantics
    eventApplicabilityQuery →
  ⊥
stateBindingCannotDetermineEventApplicability =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    stateBindingOnlyEventApplicabilityAdequacyDefect

stateBindingAndEventContextProjection :
  ApplicabilityWorld → StateBindingSurface × EventContextSurface
stateBindingAndEventContextProjection =
  Observer.pairObserver stateBindingOnlyProjection eventContextProjection

joinedEventApplicabilityAnswer :
  StateBindingSurface × EventContextSurface → EventApplicabilityAnswer
joinedEventApplicabilityAnswer (sameBoundState , eventOutsideInstrumentScope) =
  eventNotApplicable
joinedEventApplicabilityAnswer (sameBoundState , eventInsideInstrumentScope) =
  eventApplicable

stateBindingAndEventContextDetermineApplicability :
  Adequacy.AdequateFor
    stateBindingAndEventContextProjection
    eventApplicabilitySemantics
    eventApplicabilityQuery
stateBindingAndEventContextDetermineApplicability =
  Adequacy.factorsForQuery
    joinedEventApplicabilityAnswer
    (λ { boundStateEventOutsideScope → refl
       ; boundStateEventInsideScope → refl
       })

stateBindingAndEventContextStrictlyRefinesBinding :
  Observer.StrictRefinement
    stateBindingOnlyProjection
    stateBindingAndEventContextProjection
stateBindingAndEventContextStrictlyRefinesBinding =
  Observer.strictPairRefinement
    stateBindingOnlyProjection
    eventContextProjection
    boundStateEventOutsideScope
    boundStateEventInsideScope
    refl
    (λ ())

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data ParentPartyImpliesProtocolParty : Set where
data SignatureImpliesBinding : Set where
data DepositImpliesImmediateEffect : Set where
data StateBindingImpliesEventApplicability : Set where
data DepositaryListingCreatesSubstantiveRule : Set where

parentPartyDoesNotImplyProtocolParty : ParentPartyImpliesProtocolParty → ⊥
parentPartyDoesNotImplyProtocolParty ()

signatureDoesNotByItselfEstablishBinding : SignatureImpliesBinding → ⊥
signatureDoesNotByItselfEstablishBinding ()

depositDoesNotByItselfEstablishImmediateEffect : DepositImpliesImmediateEffect → ⊥
depositDoesNotByItselfEstablishImmediateEffect ()

stateBindingDoesNotByItselfEstablishEventApplicability :
  StateBindingImpliesEventApplicability → ⊥
stateBindingDoesNotByItselfEstablishEventApplicability ()

depositaryListingDoesNotCreateSubstantiveRule :
  DepositaryListingCreatesSubstantiveRule → ⊥
depositaryListingDoesNotCreateSubstantiveRule ()

parentConventionPartyDoesNotDetermineProtocolParty : Bool
parentConventionPartyDoesNotDetermineProtocolParty = true

consentActionDoesNotEqualEffectiveDate : Bool
consentActionDoesNotEqualEffectiveDate = true

stateBindingDoesNotEqualEventApplicability : Bool
stateBindingDoesNotEqualEventApplicability = true

depositaryStatusIsStatusEvidenceNotSubstantiveRuleCreation : Bool
depositaryStatusIsStatusEvidenceNotSubstantiveRuleCreation = true
