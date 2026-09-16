module DASHI.Applications.CounterUASReferenceRevisionAndCorroborationExact where

open import DASHI.Core.Prelude

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Reasoning.PNFRevisionSelectiveReopeningExact as Reopening
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- COUNTER-UAS REFERENCE REVISION + CROSS-MODAL CORROBORATION
--
-- Thin application adapter only. Generic revision, retained history,
-- supersession impact, stale-vs-refuted separation, and selective reopening
-- remain owned by the canonical core/reasoning modules imported above.
--
-- Defensive epistemic scope only: no emitter-defeat, interference, waveform,
-- targeting, or mitigation procedure is represented here.
------------------------------------------------------------------------

existingAppendOnlyRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
existingAppendOnlyRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

existingSelectiveReopeningBoundary : Reopening.PNFRevisionReopeningBoundary
existingSelectiveReopeningBoundary = Reopening.canonicalPNFRevisionReopeningBoundary

------------------------------------------------------------------------
-- I. Counter-UAS instantiation of append-only evidence revision.
--
-- The canonical fixture already has precisely the temporal shape needed for a
-- promoted signature/reference that later receives a defeater: earlier support
-- remains in history while the current consumer conclusion changes from
-- promote to hold.  We expose that witness rather than rebuilding the calculus.
------------------------------------------------------------------------

counterUASReferenceRevisionWitness :
  Revision.ConclusionRevision Revision.fixtureSystem
counterUASReferenceRevisionWitness = Revision.canonicalConclusionRevision

promotedThenDefeatedRevisionIsCanonical : Bool
promotedThenDefeatedRevisionIsCanonical = true

historicalPromotionMustBeDeletedAfterDefeater : Bool
historicalPromotionMustBeDeletedAfterDefeater = false

laterDefeaterMayChangeCurrentEligibility : Bool
laterDefeaterMayChangeCurrentEligibility = true

referenceRevisionCreatesOperationalAuthority : Bool
referenceRevisionCreatesOperationalAuthority = false

------------------------------------------------------------------------
-- II. Modality count does not determine independent corroboration.
--
-- Both worlds visibly contain three modalities (RF, radar, EO). In one world
-- all three are downstream renderings of one shared upstream lineage; in the
-- other they have independently paid genealogies.  Therefore modality count
-- alone cannot answer the independent-corroboration query.
------------------------------------------------------------------------

data CorroborationWorld : Set where
  threeModalitiesSharedUpstream : CorroborationWorld
  threeModalitiesIndependentLineages : CorroborationWorld

data ModalityCountSurface : Set where
  threeVisibleModalities : ModalityCountSurface

data GenealogySurface : Set where
  sharedUpstreamGenealogy : GenealogySurface
  independentlyPaidGenealogies : GenealogySurface

data CorroborationQuery : Set where
  modalityCountQuery : CorroborationQuery
  independentCorroborationQuery : CorroborationQuery

data CorroborationAnswer : Set where
  threeModalitiesObserved : CorroborationAnswer
  corroborationNotIndependent : CorroborationAnswer
  independentCorroborationPaidAnswer : CorroborationAnswer

modalityCountProjection : CorroborationWorld → ModalityCountSurface
modalityCountProjection world = threeVisibleModalities

genealogyProjection : CorroborationWorld → GenealogySurface
genealogyProjection threeModalitiesSharedUpstream = sharedUpstreamGenealogy
genealogyProjection threeModalitiesIndependentLineages = independentlyPaidGenealogies

corroborationAnswer : CorroborationQuery → CorroborationWorld → CorroborationAnswer
corroborationAnswer modalityCountQuery world = threeModalitiesObserved
corroborationAnswer independentCorroborationQuery threeModalitiesSharedUpstream =
  corroborationNotIndependent
corroborationAnswer independentCorroborationQuery threeModalitiesIndependentLineages =
  independentCorroborationPaidAnswer

corroborationSemantics :
  Adequacy.QuerySemantics CorroborationWorld CorroborationQuery CorroborationAnswer
corroborationSemantics = Adequacy.querySemantics corroborationAnswer

modalityCountCorroborationAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    modalityCountProjection
    corroborationSemantics
    independentCorroborationQuery
modalityCountCorroborationAdequacyDefect =
  Adequacy.queryAdequacyDefect
    threeModalitiesSharedUpstream
    threeModalitiesIndependentLineages
    refl
    (λ ())

modalityCountCannotDetermineIndependentCorroboration :
  Adequacy.AdequateFor
    modalityCountProjection
    corroborationSemantics
    independentCorroborationQuery →
  ⊥
modalityCountCannotDetermineIndependentCorroboration =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    modalityCountCorroborationAdequacyDefect

modalityAndGenealogyProjection :
  CorroborationWorld → ModalityCountSurface × GenealogySurface
modalityAndGenealogyProjection =
  Observer.pairObserver modalityCountProjection genealogyProjection

joinedCorroborationAnswer :
  ModalityCountSurface × GenealogySurface → CorroborationAnswer
joinedCorroborationAnswer (threeVisibleModalities , sharedUpstreamGenealogy) =
  corroborationNotIndependent
joinedCorroborationAnswer (threeVisibleModalities , independentlyPaidGenealogies) =
  independentCorroborationPaidAnswer

modalityAndGenealogyDetermineIndependentCorroboration :
  Adequacy.AdequateFor
    modalityAndGenealogyProjection
    corroborationSemantics
    independentCorroborationQuery
modalityAndGenealogyDetermineIndependentCorroboration =
  Adequacy.factorsForQuery
    joinedCorroborationAnswer
    (λ { threeModalitiesSharedUpstream → refl
       ; threeModalitiesIndependentLineages → refl
       })

sharedUpstreamCorroborationPaid : Bool
sharedUpstreamCorroborationPaid = false

independentLineagesCorroborationPaid : Bool
independentLineagesCorroborationPaid = true

------------------------------------------------------------------------
-- Application boundary: chronology/revision and corroboration genealogy are
-- evidentiary coordinates only.  Neither creates semantic identity, threat
-- status, or operational/legal authority.
------------------------------------------------------------------------

record CounterUASReferenceRevisionAndCorroborationBoundary : Set where
  constructor counterUASReferenceRevisionAndCorroborationBoundary
  field
    laterDefeaterDeletesHistoricalPromotion : Bool
    laterDefeaterDeletesHistoricalPromotionIsFalse :
      laterDefeaterDeletesHistoricalPromotion ≡ false
    modalityCountEqualsIndependentCorroboration : Bool
    modalityCountEqualsIndependentCorroborationIsFalse :
      modalityCountEqualsIndependentCorroboration ≡ false
    sharedUpstreamPaysIndependentGenealogy : Bool
    sharedUpstreamPaysIndependentGenealogyIsFalse :
      sharedUpstreamPaysIndependentGenealogy ≡ false
    revisionCreatesOperationalAuthority : Bool
    revisionCreatesOperationalAuthorityIsFalse :
      revisionCreatesOperationalAuthority ≡ false

canonicalCounterUASReferenceRevisionAndCorroborationBoundary :
  CounterUASReferenceRevisionAndCorroborationBoundary
canonicalCounterUASReferenceRevisionAndCorroborationBoundary =
  counterUASReferenceRevisionAndCorroborationBoundary
    false refl
    false refl
    false refl
    false refl
