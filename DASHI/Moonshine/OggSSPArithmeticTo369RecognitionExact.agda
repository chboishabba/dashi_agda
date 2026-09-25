module DASHI.Moonshine.OggSSPArithmeticTo369RecognitionExact where

------------------------------------------------------------------------
-- ARITHMETIC -> 369 SMALL-CHARACTERISTIC RECOGNITION
--
-- This is the directional recognition cut requested by the live programme:
--
--   G_p^arith  --->  G_p^369
--
-- It is intentionally distinct from the older reverse-facing compatibility
-- owner.  The arithmetic source is supplied by the marked-source sockets;
-- the 369 targets are the exact repo-native p=2/p=3 action groupoids.
--
-- No arithmetic source socket is inhabited here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Moonshine.OggSSPSmallCharacteristicArithmeticSourceSocketExact as SourceSocket
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Target
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualCodecExact as Codec
import DASHI.Moonshine.OggSSPSmallCharacteristicCodecIndexedRecognitionExact as LaneCodec
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. p=3 arithmetic -> 369 recognition.
------------------------------------------------------------------------

record P3ArithmeticTo369Recognition
    (source : SourceSocket.P3MarkedFrobeniusSource) : Set₁ where
  field
    functor :
      Recognition.ActionRecognitionFunctor
        (SourceSocket.action source)
        Target.constantC2Action

    fullRecognition :
      Recognition.OrbitStabilizerRecognition
        functor
        (SourceSocket.orbits source)
        Target.constantTernaryOrbitPresentation

open P3ArithmeticTo369Recognition public

p3OrbitRecognition :
  {source : SourceSocket.P3MarkedFrobeniusSource} →
  (recognition : P3ArithmeticTo369Recognition source) →
  Recognition.OrbitRecognition
    (P3ArithmeticTo369Recognition.functor recognition)
    (SourceSocket.orbits source)
    Target.constantTernaryOrbitPresentation
p3OrbitRecognition recognition =
  Recognition.orbitRecognition
    (P3ArithmeticTo369Recognition.fullRecognition recognition)

p3Pi0Surjection :
  {source : SourceSocket.P3MarkedFrobeniusSource} →
  (recognition : P3ArithmeticTo369Recognition source) →
  Recognition.Pi0Surjection (p3OrbitRecognition recognition)
p3Pi0Surjection recognition =
  Recognition.pi0Surjection
    (P3ArithmeticTo369Recognition.fullRecognition recognition)

p3Pi0Embedding :
  {source : SourceSocket.P3MarkedFrobeniusSource} →
  (recognition : P3ArithmeticTo369Recognition source) →
  Recognition.Pi0Embedding (p3OrbitRecognition recognition)
p3Pi0Embedding recognition =
  Recognition.pi0Embedding
    (P3ArithmeticTo369Recognition.fullRecognition recognition)

p3StabilizerRecognition :
  {source : SourceSocket.P3MarkedFrobeniusSource} →
  (recognition : P3ArithmeticTo369Recognition source) →
  Recognition.StabilizerRecognition (p3OrbitRecognition recognition)
p3StabilizerRecognition recognition =
  Recognition.stabilizerRecognition
    (P3ArithmeticTo369Recognition.fullRecognition recognition)

------------------------------------------------------------------------
-- 2. p=2 arithmetic -> retained-orientation 369 recognition.
--
-- The target is the ten-state discrete carrier because the codec theorem proves
-- that the five-orbit coarse projection has no left inverse on the ten-state
-- carrier.
------------------------------------------------------------------------

record P2ArithmeticTo369Recognition
    (source : SourceSocket.P2MarkedArithmeticSource) : Set₁ where
  field
    functor :
      Recognition.ActionRecognitionFunctor
        (SourceSocket.action source)
        Target.p2DiscreteAction

    fullRecognition :
      Recognition.OrbitStabilizerRecognition
        functor
        (SourceSocket.orbits source)
        Target.p2DiscreteOrbitPresentation

open P2ArithmeticTo369Recognition public

p2OrbitRecognition :
  {source : SourceSocket.P2MarkedArithmeticSource} →
  (recognition : P2ArithmeticTo369Recognition source) →
  Recognition.OrbitRecognition
    (P2ArithmeticTo369Recognition.functor recognition)
    (SourceSocket.orbits source)
    Target.p2DiscreteOrbitPresentation
p2OrbitRecognition recognition =
  Recognition.orbitRecognition
    (P2ArithmeticTo369Recognition.fullRecognition recognition)

p2Pi0Surjection :
  {source : SourceSocket.P2MarkedArithmeticSource} →
  (recognition : P2ArithmeticTo369Recognition source) →
  Recognition.Pi0Surjection (p2OrbitRecognition recognition)
p2Pi0Surjection recognition =
  Recognition.pi0Surjection
    (P2ArithmeticTo369Recognition.fullRecognition recognition)

p2Pi0Embedding :
  {source : SourceSocket.P2MarkedArithmeticSource} →
  (recognition : P2ArithmeticTo369Recognition source) →
  Recognition.Pi0Embedding (p2OrbitRecognition recognition)
p2Pi0Embedding recognition =
  Recognition.pi0Embedding
    (P2ArithmeticTo369Recognition.fullRecognition recognition)

p2StabilizerRecognition :
  {source : SourceSocket.P2MarkedArithmeticSource} →
  (recognition : P2ArithmeticTo369Recognition source) →
  Recognition.StabilizerRecognition (p2OrbitRecognition recognition)
p2StabilizerRecognition recognition =
  Recognition.stabilizerRecognition
    (P2ArithmeticTo369Recognition.fullRecognition recognition)

------------------------------------------------------------------------
-- 3. Exact lane indexing and codec target are part of the recognition target.
------------------------------------------------------------------------

p2RecognitionLaneKey : LaneCodec.ExactOggLaneKey
p2RecognitionLaneKey = LaneCodec.p2LaneKey

p3RecognitionLaneKey : LaneCodec.ExactOggLaneKey
p3RecognitionLaneKey = LaneCodec.p3LaneKey

p2TargetCodecReopensExactly :
  (state : Target.P2ResidualObject) →
  Codec.p2Decode (Codec.p2Encode state) ≡ state
p2TargetCodecReopensExactly =
  Codec.p2DecodeEncodeExact

p3TargetCodecReopensExactly :
  (state : Target.ConstantTernaryState) →
  Codec.p3Reopen
    (Codec.p3Project state)
    (Codec.p3Residual state)
  ≡ state
p3TargetCodecReopensExactly =
  Codec.p3ReopenExact

------------------------------------------------------------------------
-- 4. Directionality firewall.
------------------------------------------------------------------------

data ReverseCompatibilityAutomaticallyBuildsArithmeticTo369 : Set where
data CardinalityMatchAutomaticallyBuildsArithmeticTo369 : Set where
data CoarseJReceiptAutomaticallyBuildsArithmeticTo369 : Set where

reverseCompatibilityDoesNotBuildArithmeticTo369 :
  ReverseCompatibilityAutomaticallyBuildsArithmeticTo369 → ⊥
reverseCompatibilityDoesNotBuildArithmeticTo369 ()

cardinalityMatchDoesNotBuildArithmeticTo369 :
  CardinalityMatchAutomaticallyBuildsArithmeticTo369 → ⊥
cardinalityMatchDoesNotBuildArithmeticTo369 ()

coarseJReceiptDoesNotBuildArithmeticTo369 :
  CoarseJReceiptAutomaticallyBuildsArithmeticTo369 → ⊥
coarseJReceiptDoesNotBuildArithmeticTo369 ()

recognitionClaimOrigin : Attribution.ClaimOrigin
recognitionClaimOrigin = Attribution.openRecognitionConjecture

------------------------------------------------------------------------
-- 5. Current frontier.
------------------------------------------------------------------------

data ArithmeticTo369Residual : Set where
  missingP2MarkedArithmeticSource : ArithmeticTo369Residual
  missingP3MarkedFrobeniusSource : ArithmeticTo369Residual
  missingP2ArithmeticTo369Functor : ArithmeticTo369Residual
  missingP3ArithmeticTo369Functor : ArithmeticTo369Residual

record ArithmeticTo369RecognitionBoundary : Set where
  constructor arithmetic-to369-recognition-boundary
  field
    correctFunctorDirectionOwned : Bool
    p2TargetIsExactRetainedOrientationCodec : Bool
    p3TargetIsExactDependentResidualCodec : Bool
    exactOggLaneKeysOwned : Bool
    fullPi0BijectionRequired : Bool
    stabilizerRecognitionRequired : Bool
    reverseCompatibilityNotPromoted : Bool
    p2RecognitionInhabited : Bool
    p3RecognitionInhabited : Bool
    firstResidual : ArithmeticTo369Residual

canonicalArithmeticTo369RecognitionBoundary :
  ArithmeticTo369RecognitionBoundary
canonicalArithmeticTo369RecognitionBoundary =
  arithmetic-to369-recognition-boundary
    true true true true true true true
    false false
    missingP2MarkedArithmeticSource
