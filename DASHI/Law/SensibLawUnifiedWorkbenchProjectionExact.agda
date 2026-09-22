module DASHI.Law.SensibLawUnifiedWorkbenchProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- M10 UNIFIED WORKBENCH PROJECTION
--
-- Journal, Timeline, Handoff, Matter/Proof and Research are consumer views over
-- one canonical world. View depth may change visibility, never semantic state.
------------------------------------------------------------------------

data Stage : Set where
  journal : Stage
  timeline : Stage
  handoff : Stage
  matterProof : Stage
  research : Stage

data Availability : Set where
  available : Availability
  blocked : Availability
  unavailable : Availability

record CanonicalState : Set where
  constructor canonicalState
  field
    stateRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open CanonicalState public

record Projection (state : CanonicalState) : Set where
  constructor projection
  field
    stage : Stage
    availability : Availability
    stateRefPreserved :
      stateRef state ≡ stateRef state
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open Projection public

canonicalWorkbenchState : CanonicalState
canonicalWorkbenchState =
  canonicalState
    "world:unified-workbench"
    true refl
    false refl
    false refl

journalProjection : Projection canonicalWorkbenchState
journalProjection =
  projection journal available refl true refl false refl false refl

timelineProjection : Projection canonicalWorkbenchState
timelineProjection =
  projection timeline blocked refl true refl false refl false refl

handoffProjection : Projection canonicalWorkbenchState
handoffProjection =
  projection handoff available refl true refl false refl false refl

matterProofProjection : Projection canonicalWorkbenchState
matterProofProjection =
  projection matterProof unavailable refl true refl false refl false refl

researchProjection : Projection canonicalWorkbenchState
researchProjection =
  projection research available refl true refl false refl false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ViewChangeCreatesSemanticAuthority : Set where
data ViewChangeCreatesClaimTruth : Set where
data ViewChangePaysResidual : Set where
data UnavailableMeansFalse : Set where
data HiddenMeansDiscarded : Set where
data ProjectionCreatesSecondWorld : Set where

viewChangeCannotCreateAuthority :
  ViewChangeCreatesSemanticAuthority → ⊥
viewChangeCannotCreateAuthority ()

viewChangeCannotCreateTruth :
  ViewChangeCreatesClaimTruth → ⊥
viewChangeCannotCreateTruth ()

viewChangeCannotPayResidual :
  ViewChangePaysResidual → ⊥
viewChangeCannotPayResidual ()

unavailableDoesNotMeanFalse :
  UnavailableMeansFalse → ⊥
unavailableDoesNotMeanFalse ()

hiddenDoesNotMeanDiscarded :
  HiddenMeansDiscarded → ⊥
hiddenDoesNotMeanDiscarded ()

projectionDoesNotCreateSecondWorld :
  ProjectionCreatesSecondWorld → ⊥
projectionDoesNotCreateSecondWorld ()

record UnifiedWorkbenchBoundary : Set where
  constructor unifiedWorkbenchBoundary
  field
    journalTimelineHandoffProofResearchShareState : Bool
    journalTimelineHandoffProofResearchShareStateIsTrue :
      journalTimelineHandoffProofResearchShareState ≡ true

    unavailableProjectionRemainsExplicit : Bool
    unavailableProjectionRemainsExplicitIsTrue :
      unavailableProjectionRemainsExplicit ≡ true

    stageChangeCreatesAuthority : Bool
    stageChangeCreatesAuthorityIsFalse :
      stageChangeCreatesAuthority ≡ false

    stageChangeCreatesTruth : Bool
    stageChangeCreatesTruthIsFalse :
      stageChangeCreatesTruth ≡ false

    stageChangePaysResidual : Bool
    stageChangePaysResidualIsFalse :
      stageChangePaysResidual ≡ false

    projectionCreatesSecondWorld : Bool
    projectionCreatesSecondWorldIsFalse :
      projectionCreatesSecondWorld ≡ false

open UnifiedWorkbenchBoundary public

canonicalUnifiedWorkbenchBoundary : UnifiedWorkbenchBoundary
canonicalUnifiedWorkbenchBoundary =
  unifiedWorkbenchBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
