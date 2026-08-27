module DASHI.Biology.BodyModulatedDecisionCoordinatesExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach

------------------------------------------------------------------------
-- BODY STATE MODULATES MULTIPLE DECISION COORDINATES, NOT ACCESS ALONE.
------------------------------------------------------------------------

record DecisionControlVector : Set where
  constructor decisionControlVector
  field
    attentionGain : Nat
    memoryRetrievalGain : Nat
    valuationBias : Nat
    precisionGain : Nat
    evidenceGain : Nat
    decisionThreshold : Nat
    motorReadiness : Nat
    confidenceGain : Nat
    learningRate : Nat

open DecisionControlVector public

regulatedControls : DecisionControlVector
regulatedControls = decisionControlVector 2 2 1 2 2 1 1 2 1

mobilisedControls : DecisionControlVector
mobilisedControls = decisionControlVector 3 1 3 3 3 2 3 1 2

sameAccessSurface : Reach.BodyContext → Bool
sameAccessSurface Reach.regulatedContext = true
sameAccessSurface Reach.mobilisedContext = true

sameAccessDoesNotDetermineThreshold :
  sameAccessSurface Reach.regulatedContext
  ≡ sameAccessSurface Reach.mobilisedContext
sameAccessDoesNotDetermineThreshold = refl

thresholdStillDiffers :
  decisionThreshold regulatedControls
  ≡ decisionThreshold mobilisedControls → ⊥
thresholdStillDiffers ()

attentionStillDiffers :
  attentionGain regulatedControls
  ≡ attentionGain mobilisedControls → ⊥
attentionStillDiffers ()

memoryRetrievalStillDiffers :
  memoryRetrievalGain regulatedControls
  ≡ memoryRetrievalGain mobilisedControls → ⊥
memoryRetrievalStillDiffers ()

valuationStillDiffers :
  valuationBias regulatedControls
  ≡ valuationBias mobilisedControls → ⊥
valuationStillDiffers ()

precisionStillDiffers :
  precisionGain regulatedControls
  ≡ precisionGain mobilisedControls → ⊥
precisionStillDiffers ()

evidenceStillDiffers :
  evidenceGain regulatedControls
  ≡ evidenceGain mobilisedControls → ⊥
evidenceStillDiffers ()

motorReadinessStillDiffers :
  motorReadiness regulatedControls
  ≡ motorReadiness mobilisedControls → ⊥
motorReadinessStillDiffers ()

confidenceStillDiffers :
  confidenceGain regulatedControls
  ≡ confidenceGain mobilisedControls → ⊥
confidenceStillDiffers ()

learningRateStillDiffers :
  learningRate regulatedControls
  ≡ learningRate mobilisedControls → ⊥
learningRateStillDiffers ()

record BodyDecisionControlBoundary : Set where
  constructor bodyDecisionControlBoundary
  field
    accessibilityDeterminesAllDecisionControl : Bool
    bodyStateIsOnlyAThresholdParameter : Bool
    finiteControlVectorIsQuantitativeHumanFit : Bool

canonicalBodyDecisionControlBoundary : BodyDecisionControlBoundary
canonicalBodyDecisionControlBoundary =
  bodyDecisionControlBoundary false false false
