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
    valuationBias : Nat
    precisionGain : Nat
    decisionThreshold : Nat
    motorReadiness : Nat
    learningRate : Nat

open DecisionControlVector public

regulatedControls : DecisionControlVector
regulatedControls = decisionControlVector 2 1 2 1 1 1

mobilisedControls : DecisionControlVector
mobilisedControls = decisionControlVector 3 3 3 2 3 2

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

motorReadinessStillDiffers :
  motorReadiness regulatedControls
  ≡ motorReadiness mobilisedControls → ⊥
motorReadinessStillDiffers ()

record BodyDecisionControlBoundary : Set where
  constructor bodyDecisionControlBoundary
  field
    accessibilityDeterminesAllDecisionControl : Bool
    bodyStateIsOnlyAThresholdParameter : Bool
    finiteControlVectorIsQuantitativeHumanFit : Bool

canonicalBodyDecisionControlBoundary : BodyDecisionControlBoundary
canonicalBodyDecisionControlBoundary =
  bodyDecisionControlBoundary false false false
