module DASHI.Law.SensibLawInternationalInstrumentLifecycleExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- INTERNATIONAL-INSTRUMENT LIFECYCLE
--
-- Scope:
--   negotiation status != instrument nature != legal effect != applicability.
--
-- This is a generic SensibLaw carrier.  It does not decide whether a specific
-- instrument exists, whether a State is bound, or whether a rule applies to a
-- particular event.  Those are source- and context-indexed downstream facts.
------------------------------------------------------------------------

data NegotiationStatus : Set where
  discussionStatus : NegotiationStatus
  proposalStatus : NegotiationStatus
  consensusElements : NegotiationStatus
  adoptedInstrument : NegotiationStatus

data InstrumentNature : Set where
  instrumentNatureUnresolved : InstrumentNature
  politicalInstrument : InstrumentNature
  nonBindingInstrument : InstrumentNature
  legallyBindingInstrument : InstrumentNature

data LegalEffectStatus : Set where
  noNewBindingEffect : LegalEffectStatus
  adoptedNotInForce : LegalEffectStatus
  bindingInForce : LegalEffectStatus

data ApplicabilityStatus : Set where
  applicabilityUnresolved : ApplicabilityStatus
  boundStateContextRequired : ApplicabilityStatus
  applicable : ApplicabilityStatus
  notApplicable : ApplicabilityStatus

record InstrumentLifecycleSnapshot : Set where
  constructor instrumentLifecycleSnapshot
  field
    negotiationStatus : NegotiationStatus
    instrumentNature : InstrumentNature
    legalEffectStatus : LegalEffectStatus
    applicabilityStatus : ApplicabilityStatus

open InstrumentLifecycleSnapshot public

------------------------------------------------------------------------
-- Query-indexed non-factorability:
-- identical visible consensus text does not determine binding legal effect.
------------------------------------------------------------------------

data InstrumentWorld : Set where
  consensusElementsOnlyWorld : InstrumentWorld
  adoptedBindingInForceWorld : InstrumentWorld

data ConsensusSurface : Set where
  sameConsensusText : ConsensusSurface

data InstitutionalSurface : Set where
  elementsWithoutAdoption : InstitutionalSurface
  adoptedAndInForce : InstitutionalSurface

data InstrumentQuery : Set where
  textualConsensusQuery : InstrumentQuery
  bindingEffectQuery : InstrumentQuery

data InstrumentAnswer : Set where
  consensusTextObserved : InstrumentAnswer
  noBindingEstablished : InstrumentAnswer
  bindingEstablished : InstrumentAnswer

consensusOnlyProjection : InstrumentWorld → ConsensusSurface
consensusOnlyProjection world = sameConsensusText

institutionalProjection : InstrumentWorld → InstitutionalSurface
institutionalProjection consensusElementsOnlyWorld = elementsWithoutAdoption
institutionalProjection adoptedBindingInForceWorld = adoptedAndInForce

instrumentAnswer : InstrumentQuery → InstrumentWorld → InstrumentAnswer
instrumentAnswer textualConsensusQuery world = consensusTextObserved
instrumentAnswer bindingEffectQuery consensusElementsOnlyWorld = noBindingEstablished
instrumentAnswer bindingEffectQuery adoptedBindingInForceWorld = bindingEstablished

instrumentSemantics :
  Adequacy.QuerySemantics InstrumentWorld InstrumentQuery InstrumentAnswer
instrumentSemantics = Adequacy.querySemantics instrumentAnswer

consensusOnlyBindingAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    consensusOnlyProjection
    instrumentSemantics
    bindingEffectQuery
consensusOnlyBindingAdequacyDefect =
  Adequacy.queryAdequacyDefect
    consensusElementsOnlyWorld
    adoptedBindingInForceWorld
    refl
    (λ ())

consensusOnlyCannotDetermineBinding :
  Adequacy.AdequateFor
    consensusOnlyProjection
    instrumentSemantics
    bindingEffectQuery →
  ⊥
consensusOnlyCannotDetermineBinding =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    consensusOnlyBindingAdequacyDefect

consensusAndInstitutionalProjection :
  InstrumentWorld → ConsensusSurface × InstitutionalSurface
consensusAndInstitutionalProjection =
  Observer.pairObserver consensusOnlyProjection institutionalProjection

joinedBindingAnswer :
  ConsensusSurface × InstitutionalSurface → InstrumentAnswer
joinedBindingAnswer (sameConsensusText , elementsWithoutAdoption) =
  noBindingEstablished
joinedBindingAnswer (sameConsensusText , adoptedAndInForce) =
  bindingEstablished

consensusAndInstitutionalDetermineBinding :
  Adequacy.AdequateFor
    consensusAndInstitutionalProjection
    instrumentSemantics
    bindingEffectQuery
consensusAndInstitutionalDetermineBinding =
  Adequacy.factorsForQuery
    joinedBindingAnswer
    (λ { consensusElementsOnlyWorld → refl
       ; adoptedBindingInForceWorld → refl
       })

consensusAndInstitutionalStrictlyRefinesConsensus :
  Observer.StrictRefinement
    consensusOnlyProjection
    consensusAndInstitutionalProjection
consensusAndInstitutionalStrictlyRefinesConsensus =
  Observer.strictPairRefinement
    consensusOnlyProjection
    institutionalProjection
    consensusElementsOnlyWorld
    adoptedBindingInForceWorld
    refl
    (λ ())

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data ConsensusImpliesTreaty : Set where
data AdoptionImpliesEntryIntoForce : Set where
data EntryIntoForceImpliesEveryStateBound : Set where
data StateBoundImpliesEveryContextApplicable : Set where

data CitationCreatesBindingEffect : Set where

consensusDoesNotByItselfEstablishTreaty : ConsensusImpliesTreaty → ⊥
consensusDoesNotByItselfEstablishTreaty ()

adoptionDoesNotByItselfEstablishEntryIntoForce :
  AdoptionImpliesEntryIntoForce → ⊥
adoptionDoesNotByItselfEstablishEntryIntoForce ()

entryIntoForceDoesNotBindEveryStateAutomatically :
  EntryIntoForceImpliesEveryStateBound → ⊥
entryIntoForceDoesNotBindEveryStateAutomatically ()

stateBindingDoesNotSetEveryFactualApplicabilityQuestion :
  StateBoundImpliesEveryContextApplicable → ⊥
stateBindingDoesNotSetEveryFactualApplicabilityQuestion ()

citationDoesNotCreateBindingEffect : CitationCreatesBindingEffect → ⊥
citationDoesNotCreateBindingEffect ()

consensusDoesNotCreateTreatyAuthority : Bool
consensusDoesNotCreateTreatyAuthority = true

adoptionDoesNotEqualEntryIntoForce : Bool
adoptionDoesNotEqualEntryIntoForce = true

entryIntoForceDoesNotEqualUniversalStateBinding : Bool
entryIntoForceDoesNotEqualUniversalStateBinding = true

stateBindingDoesNotEqualEventApplicability : Bool
stateBindingDoesNotEqualEventApplicability = true

citationDoesNotCreateLegalAuthority : Bool
citationDoesNotCreateLegalAuthority = true
