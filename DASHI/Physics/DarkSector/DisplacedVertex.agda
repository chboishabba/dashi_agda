module DASHI.Physics.DarkSector.DisplacedVertex where

open import DASHI.Core.Prelude
open import Data.Nat using (_≤ᵇ_)

import DASHI.Physics.DarkSector.BoostedDecayGeometry as Boost

andBool : Bool → Bool → Bool
andBool true true = true
andBool true false = false
andBool false true = false
andBool false false = false

------------------------------------------------------------------------
-- Reconstructed event geometry.  Acceptance includes displacement bounds,
-- visible daughter multiplicity, and an independently supplied quality flag.

record VertexEvent : Set where
  constructor vertexEvent
  field
    interactionPoint : Nat
    decayPoint : Nat
    minimumAcceptedDisplacement : Nat
    maximumAcceptedDisplacement : Nat
    visibleDaughterTracks : Nat
    minimumDaughterTracks : Nat
    vertexQualityPasses : Bool

open VertexEvent public

vertexDisplacement : VertexEvent → Nat
vertexDisplacement event = decayPoint event ∸ interactionPoint event

withinDisplacementWindow : VertexEvent → Bool
withinDisplacementWindow event =
  andBool
    (minimumAcceptedDisplacement event ≤ᵇ vertexDisplacement event)
    (vertexDisplacement event ≤ᵇ maximumAcceptedDisplacement event)

daughterMultiplicityPasses : VertexEvent → Bool
daughterMultiplicityPasses event =
  minimumDaughterTracks event ≤ᵇ visibleDaughterTracks event

isDisplacedVertex : VertexEvent → Bool
isDisplacedVertex event =
  andBool
    (withinDisplacementWindow event)
    (andBool
      (daughterMultiplicityPasses event)
      (vertexQualityPasses event))

canonicalDisplacedEvent : VertexEvent
canonicalDisplacedEvent =
  vertexEvent 0 8 2 10 2 2 true

canonicalPromptEvent : VertexEvent
canonicalPromptEvent =
  vertexEvent 0 0 2 10 2 2 true

canonicalOutsideDetectorEvent : VertexEvent
canonicalOutsideDetectorEvent =
  vertexEvent 0 12 2 10 2 2 true

canonicalDisplacementMatchesBoostedGeometry :
  vertexDisplacement canonicalDisplacedEvent
  ≡
  Boost.laboratoryDisplacement Boost.canonicalBoostedDecay
canonicalDisplacementMatchesBoostedGeometry = refl

canonicalEventIsDisplacedVertex :
  isDisplacedVertex canonicalDisplacedEvent ≡ true
canonicalEventIsDisplacedVertex = refl

promptEventIsNotDisplacedVertex :
  isDisplacedVertex canonicalPromptEvent ≡ false
promptEventIsNotDisplacedVertex = refl

outsideEventIsNotAcceptedDisplacedVertex :
  isDisplacedVertex canonicalOutsideDetectorEvent ≡ false
outsideEventIsNotAcceptedDisplacedVertex = refl

------------------------------------------------------------------------
-- Prompt and displaced samples are explicit rather than inferred from one
-- undifferentiated event class.

data ControlSample : Set where
  promptControlSample : ControlSample
  displacedControlSample : ControlSample

sampleEvent : ControlSample → VertexEvent
sampleEvent promptControlSample = canonicalPromptEvent
sampleEvent displacedControlSample = canonicalDisplacedEvent

record DisplacedVertexBoundary : Set where
  constructor displacedVertexBoundary
  field
    nonzeroLifetimeAutomaticallyPassesDetectorAcceptance : Bool
    nonzeroLifetimeAutomaticallyPassesDetectorAcceptanceIsFalse :
      nonzeroLifetimeAutomaticallyPassesDetectorAcceptance ≡ false

    nonzeroDisplacementAloneIsReconstructedVertex : Bool
    nonzeroDisplacementAloneIsReconstructedVertexIsFalse :
      nonzeroDisplacementAloneIsReconstructedVertex ≡ false

    finiteAcceptedVertexIsEvidenceForActualDarkSector : Bool
    finiteAcceptedVertexIsEvidenceForActualDarkSectorIsFalse :
      finiteAcceptedVertexIsEvidenceForActualDarkSector ≡ false

open DisplacedVertexBoundary public

canonicalDisplacedVertexBoundary : DisplacedVertexBoundary
canonicalDisplacedVertexBoundary =
  displacedVertexBoundary false refl false refl false refl
