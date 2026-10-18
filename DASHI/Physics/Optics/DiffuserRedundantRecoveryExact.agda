module DASHI.Physics.Optics.DiffuserRedundantRecoveryExact where

-- FINITE CONSTRUCTIVE BRIDGE
-- A saturated sensor pixel may be locally non-injective while the complete
-- multiplexed observation remains injective because an independent pixel
-- retains the missing scene distinction.
--
-- This is a theorem about a finite observer/codec.  No claim is made that a
-- physically calibrated diffuser or zone plate realises this exact codebook.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as Camera

one two : ℕ
one = suc zero
two = suc one

-- Two alternative scene states. Their first sensor contributions are large
-- enough to hit the full-well cap in both cases; an independent second
-- detector sample, despite sharing the exposure, retains the distinction.
data Scene : Set where
  firstScene secondScene : Scene

data Depth : Set where
  near far : Depth

trueDepth : Scene → Depth
trueDepth firstScene = near
trueDepth secondScene = far

data Recorded : Set where
  recorded : ℕ → ℕ → Recorded

-- This is an *unsaturated* optical code, prior to the finite detector cap.
opticalCode : Scene → Recorded
opticalCode firstScene  = recorded one zero
opticalCode secondScene = recorded two one

-- First pixel clips both signals to one; the second stays discriminative.
recordedCode : Scene → Recorded
recordedCode firstScene =
  recorded (Camera.clipAtOne one) (Camera.clipAtOne zero)
recordedCode secondScene =
  recorded (Camera.clipAtOne two) (Camera.clipAtOne one)

-- One clipped pixel alone cannot resolve near/far.
firstPixel : Recorded → ℕ
firstPixel (recorded x y) = x

secondPixel : Recorded → ℕ
secondPixel (recorded x y) = y

firstPixelCollision :
  firstPixel (recordedCode firstScene) ≡
  firstPixel (recordedCode secondScene)
firstPixelCollision = refl

secondPixelFirst : secondPixel (recordedCode firstScene) ≡ zero
secondPixelFirst = refl

secondPixelSecond : secondPixel (recordedCode secondScene) ≡ one
secondPixelSecond = refl

decodeDepth : Recorded → Depth
decodeDepth (recorded x zero) = near
decodeDepth (recorded x (suc y)) = far

-- Crucial round trip: the complete *clipped* exposure retains enough
-- information to recover depth, despite the saturated first component.
redundantRecovery : (scene : Scene) →
  decodeDepth (recordedCode scene) ≡ trueDepth scene
redundantRecovery firstScene = refl
redundantRecovery secondScene = refl

-- This includes an exact scene-level decoder for the restricted two-state
-- class, proving the entire observation is injective on that class.
decodeScene : Recorded → Scene
decodeScene (recorded x zero) = firstScene
decodeScene (recorded x (suc y)) = secondScene

sceneRoundTrip : (scene : Scene) →
  decodeScene (recordedCode scene) ≡ scene
sceneRoundTrip firstScene = refl
sceneRoundTrip secondScene = refl

recordedCodeInjective :
  (a b : Scene) →
  recordedCode a ≡ recordedCode b → a ≡ b
recordedCodeInjective a b equal =
  trans (sym (sceneRoundTrip a))
    (trans (cong decodeScene equal) (sceneRoundTrip b))

-- The opposite boundary: if the only surviving observable is the first
-- clipped pixel then these two scenes are indistinguishable. A decoder cannot
-- return the correct depth for both.
nearNotFar : near ≡ far → ⊥
nearNotFar ()

firstPixelOnlyCannotRecoverDepth :
  (decoder : ℕ → Depth) →
  ((scene : Scene) →
    decoder (firstPixel (recordedCode scene)) ≡ trueDepth scene) →
  ⊥
firstPixelOnlyCannotRecoverDepth decoder correct =
  nearNotFar
    (trans (sym (correct firstScene))
      (trans (cong decoder firstPixelCollision)
        (correct secondScene)))

-- Generic redundant-observer criterion: a recovery map from the *complete*
-- observation is sufficient to establish the required consumer.
-- This avoids mistaking a non-injective single pixel for a non-injective
-- entire optical exposure.
record RecoverableConsumer
    (Fine Observation Outcome : Set)
    (observe : Fine → Observation)
    (consumer : Fine → Outcome) : Set where
  field
    recover : Observation → Outcome
    faithful : (x : Fine) → recover (observe x) ≡ consumer x

open RecoverableConsumer public

consumerFactorsThrough :
  ∀ {Fine Observation Outcome : Set}
    {observe : Fine → Observation}
    {consumer : Fine → Outcome} →
  RecoverableConsumer Fine Observation Outcome observe consumer →
  (a b : Fine) →
  observe a ≡ observe b →
  consumer a ≡ consumer b
consumerFactorsThrough witness a b same =
  trans (sym (faithful witness a))
    (trans (cong (recover witness) same) (faithful witness b))

depthRecoveryReceipt :
  RecoverableConsumer Scene Recorded Depth recordedCode trueDepth
depthRecoveryReceipt = record
  { recover = decodeDepth
  ; faithful = redundantRecovery
  }

-- This proves that the two alternatives cannot collapse to the same
-- *complete* recorded sample, since the depth consumer differs.
recordedCollisionWouldContradictDepth :
  recordedCode firstScene ≡ recordedCode secondScene → ⊥
recordedCollisionWouldContradictDepth same =
  nearNotFar
    (consumerFactorsThrough depthRecoveryReceipt
      firstScene secondScene same)
