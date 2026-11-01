module DASHI.Core.MinimalObservationLevelPerConsumerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.ProjectionHierarchyCompatibleFibreBidiExact as Projection

------------------------------------------------------------------------
-- NESTED FIBRES -> MINIMAL OBSERVATION LEVEL PER CONSUMER
--
-- Full hidden-state identification is not the objective.  For a given consumer,
-- ask for the least observation level at which that consumer is constant on the
-- surviving compatible fibre.
------------------------------------------------------------------------

data ObservationLevel : Set where
  coarseLevel : ObservationLevel
  middleLevel : ObservationLevel
  fineLevel : ObservationLevel

fibreAt : ObservationLevel → Bidi.ResidualFibre Projection.Hidden
fibreAt coarseLevel = Projection.coarseFibre
fibreAt middleLevel = Projection.middleFibre
fibreAt fineLevel = Projection.fineFibre

ConsumerClosedAtLevel :
  (Projection.Hidden → Projection.Decision) → ObservationLevel → Set
ConsumerClosedAtLevel consumer level =
  Bidi.PointIdentifies (fibreAt level) consumer

middleDecisionClosedAtMiddle :
  ConsumerClosedAtLevel Projection.middleDecision middleLevel
middleDecisionClosedAtMiddle = Projection.middleConsumerClosed

acceptedNotRejected :
  Projection.accepted ≡ Projection.rejected → ⊥
acceptedNotRejected ()

middleDecisionNotClosedAtCoarse :
  ConsumerClosedAtLevel Projection.middleDecision coarseLevel → ⊥
middleDecisionNotClosedAtCoarse closed =
  acceptedNotRejected (closed Projection.h0 Projection.h2 tt tt)

middleDecisionClosedAtFine :
  ConsumerClosedAtLevel Projection.middleDecision fineLevel
middleDecisionClosedAtFine Projection.h0 Projection.h0 left right = refl
middleDecisionClosedAtFine Projection.h0 Projection.h1 left ()
middleDecisionClosedAtFine Projection.h0 Projection.h2 left ()
middleDecisionClosedAtFine Projection.h0 Projection.h3 left ()
middleDecisionClosedAtFine Projection.h1 right ()
middleDecisionClosedAtFine Projection.h2 right ()
middleDecisionClosedAtFine Projection.h3 right ()

record MinimalMiddleObservationFor
    (consumer : Projection.Hidden → Projection.Decision) : Set₁ where
  constructor minimal-middle-observation-for
  field
    closedAtMiddle : ConsumerClosedAtLevel consumer middleLevel
    notClosedAtCoarse : ConsumerClosedAtLevel consumer coarseLevel → ⊥

open MinimalMiddleObservationFor public

middleIsMinimalForMiddleDecision :
  MinimalMiddleObservationFor Projection.middleDecision
middleIsMinimalForMiddleDecision =
  minimal-middle-observation-for
    middleDecisionClosedAtMiddle
    middleDecisionNotClosedAtCoarse

------------------------------------------------------------------------
-- The middle fibre is still non-singleton, so this is a literal consumer-level
-- closure before full hidden-state identification.
------------------------------------------------------------------------

middleClosureStillNotPointSingleton = Projection.middleNotPointSingleton

data ConsumerMinimalLevelIsGlobalIdentificationLevel : Set where
data FinerObservationAlwaysChangesConsumerAnswer : Set where

globalIdentificationDoesNotFollowFromConsumerMinimality :
  ConsumerMinimalLevelIsGlobalIdentificationLevel → ⊥
globalIdentificationDoesNotFollowFromConsumerMinimality ()

finerObservationNeedNotChangeConsumerAnswer :
  FinerObservationAlwaysChangesConsumerAnswer → ⊥
finerObservationNeedNotChangeConsumerAnswer ()

record MinimalObservationBoundary : Set where
  constructor minimal-observation-boundary
  field
    closureMayOccurBeforeSingleton : Bool
    minimalLevelIsConsumerRelative : Bool
    finerLevelMayPreserveSameConsumerAnswer : Bool
    fullMechanismIdentificationRequiredForEveryConsumer : Bool

canonicalMinimalObservationBoundary : MinimalObservationBoundary
canonicalMinimalObservationBoundary =
  minimal-observation-boundary true true true false
