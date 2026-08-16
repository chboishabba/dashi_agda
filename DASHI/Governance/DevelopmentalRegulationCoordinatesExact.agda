module DASHI.Governance.DevelopmentalRegulationCoordinatesExact where

open import DASHI.Core.Prelude

import DASHI.Governance.DevelopmentalAgencyState as Agency

------------------------------------------------------------------------
-- Regulation coordinates.
--
-- Food/interoception, belief revision and attention/volition may share a
-- feedback topology without being the same psychological variable.  This
-- module makes that non-collapse exact.
------------------------------------------------------------------------

data RegulationCoordinate : Set where
  interoceptive : RegulationCoordinate
  epistemic : RegulationCoordinate
  volitional : RegulationCoordinate

record CoordinateProjection
  (S : Agency.DevelopmentalAgencySystem) : Set₁ where
  field
    projectCapacity :
      RegulationCoordinate →
      Agency.Subject S →
      Agency.Domain S →
      Agency.Stage S →
      Agency.Capacity S

    interoceptiveExact :
      (subject : Agency.Subject S) →
      (domain : Agency.Domain S) →
      (stage : Agency.Stage S) →
      projectCapacity interoceptive subject domain stage
      ≡ Agency.interoceptiveCapacity S subject domain stage

    epistemicExact :
      (subject : Agency.Subject S) →
      (domain : Agency.Domain S) →
      (stage : Agency.Stage S) →
      projectCapacity epistemic subject domain stage
      ≡ Agency.epistemicRevisionCapacity S subject domain stage

    volitionalExact :
      (subject : Agency.Subject S) →
      (domain : Agency.Domain S) →
      (stage : Agency.Stage S) →
      projectCapacity volitional subject domain stage
      ≡ Agency.volitionalCapacity S subject domain stage

------------------------------------------------------------------------
-- The coordinates are constructively distinct.
------------------------------------------------------------------------

interoceptiveIsNotEpistemic : interoceptive ≡ epistemic → ⊥
interoceptiveIsNotEpistemic ()

epistemicIsNotVolitional : epistemic ≡ volitional → ⊥
epistemicIsNotVolitional ()

interoceptiveIsNotVolitional : interoceptive ≡ volitional → ⊥
interoceptiveIsNotVolitional ()

------------------------------------------------------------------------
-- Shared topology only supplies a shape-level relation.  It does not identify
-- the state carriers or empirical mechanisms in two domains.
------------------------------------------------------------------------

record FeedbackTopology : Set₁ where
  field
    State : Set
    Signal : Set
    Input : Set
    emitSignal : State → Signal
    chooseInput : State → Signal → Input

record SameFeedbackShape : Set₁ where
  field
    left : FeedbackTopology
    right : FeedbackTopology

record RegulationCoordinateBoundary : Set where
  constructor regulationCoordinateBoundary
  field
    sharedFeedbackTopologyEqualsSamePsychology : Bool
    foodEvidencePromotesReligiousMechanism : Bool
    screenEvidencePromotesInteroceptiveMechanism : Bool
    coordinateSpecificEvidenceRequired : Bool

canonicalRegulationCoordinateBoundary : RegulationCoordinateBoundary
canonicalRegulationCoordinateBoundary =
  regulationCoordinateBoundary false false false true
