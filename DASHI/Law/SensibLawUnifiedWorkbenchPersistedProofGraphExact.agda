module DASHI.Law.SensibLawUnifiedWorkbenchPersistedProofGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawUnifiedWorkbenchProjectionExact as Workbench

------------------------------------------------------------------------
-- M10 PERSISTED PROOF-GRAPH AVAILABILITY
--
-- Matter/Proof availability is a projection of persisted graph presence.
-- The UI cannot infer or manufacture proof availability from text, adjacency,
-- keywords, selection, or renderer state.
------------------------------------------------------------------------

data PersistedProofGraphState : Set where
  noPersistedProofGraph : PersistedProofGraphState
  persistedProofGraph : PersistedProofGraphState

matterProofAvailability :
  PersistedProofGraphState → Workbench.Availability
matterProofAvailability noPersistedProofGraph = Workbench.unavailable
matterProofAvailability persistedProofGraph = Workbench.available

absentGraphMeansUnavailable :
  matterProofAvailability noPersistedProofGraph
    ≡ Workbench.unavailable
absentGraphMeansUnavailable = refl

presentGraphMeansAvailable :
  matterProofAvailability persistedProofGraph
    ≡ Workbench.available
presentGraphMeansAvailable = refl

data UiInfersProofGraphFromKeywords : Set where
data RendererCreatesProofGraph : Set where
data GraphPresenceCreatesSemanticAuthority : Set where
data GraphPresenceCreatesClaimTruth : Set where
data GraphPresencePaysResidual : Set where

uiCannotInferProofGraph :
  UiInfersProofGraphFromKeywords → ⊥
uiCannotInferProofGraph ()

rendererCannotCreateProofGraph :
  RendererCreatesProofGraph → ⊥
rendererCannotCreateProofGraph ()

graphPresenceDoesNotCreateAuthority :
  GraphPresenceCreatesSemanticAuthority → ⊥
graphPresenceDoesNotCreateAuthority ()

graphPresenceDoesNotCreateTruth :
  GraphPresenceCreatesClaimTruth → ⊥
graphPresenceDoesNotCreateTruth ()

graphPresenceDoesNotPayResidual :
  GraphPresencePaysResidual → ⊥
graphPresenceDoesNotPayResidual ()

record PersistedProofGraphBoundary : Set where
  constructor persistedProofGraphBoundary
  field
    absentGraphProjectsUnavailable : Bool
    absentGraphProjectsUnavailableIsTrue :
      absentGraphProjectsUnavailable ≡ true

    presentGraphProjectsAvailable : Bool
    presentGraphProjectsAvailableIsTrue :
      presentGraphProjectsAvailable ≡ true

    uiMayInferMissingGraph : Bool
    uiMayInferMissingGraphIsFalse :
      uiMayInferMissingGraph ≡ false

    rendererMayCreateGraph : Bool
    rendererMayCreateGraphIsFalse :
      rendererMayCreateGraph ≡ false

    graphPresenceCreatesAuthority : Bool
    graphPresenceCreatesAuthorityIsFalse :
      graphPresenceCreatesAuthority ≡ false

    graphPresenceCreatesTruth : Bool
    graphPresenceCreatesTruthIsFalse :
      graphPresenceCreatesTruth ≡ false

    graphPresencePaysResidual : Bool
    graphPresencePaysResidualIsFalse :
      graphPresencePaysResidual ≡ false

open PersistedProofGraphBoundary public

canonicalPersistedProofGraphBoundary : PersistedProofGraphBoundary
canonicalPersistedProofGraphBoundary =
  persistedProofGraphBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
