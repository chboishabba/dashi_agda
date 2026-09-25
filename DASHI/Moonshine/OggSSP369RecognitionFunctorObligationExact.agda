module DASHI.Moonshine.OggSSP369RecognitionFunctorObligationExact where

------------------------------------------------------------------------
-- OGG / SSP SMALL-CHARACTERISTIC -> 369 RECOGNITION FUNCTOR OBLIGATION
--
-- DASHI CONTRIBUTION / OPEN RECOGNITION CUT
--
-- Reuse the canonical action/orbit/stabilizer recognition contract.  The
-- source groupoids are already exact:
--
--   p=3 : constant ternary states // C2
--   p=2 : strict-sheet x five-orbit carrier // C2
--   p=2 : retained-orientation discrete groupoid
--
-- What remains open is construction of the arithmetic/Fricke target groupoid
-- and a functor into a 369 presentation satisfying the exact orbit/stabilizer
-- recognition package.
--
-- No cardinality equality is promoted to recognition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualCodecExact as Codec
import DASHI.Moonshine.OggSSPSmallCharacteristicCodecIndexedRecognitionExact as LaneCodec
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

------------------------------------------------------------------------
-- 1. Generic target obligation for one already-owned source action groupoid.
------------------------------------------------------------------------

record RecognitionTargetFor
    {SourceState SourceSymmetry : Set}
    (sourceAction :
      Action.InvertibleSymmetryAction SourceState SourceSymmetry)
    (sourceOrbits :
      Orbit.OrbitPresentation sourceAction) : Set₁ where
  field
    TargetState : Set
    TargetSymmetry : Set

    targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry

    targetOrbits :
      Orbit.OrbitPresentation targetAction

    recognitionFunctor :
      Recognition.ActionRecognitionFunctor
        sourceAction
        targetAction

    fullRecognition :
      Recognition.OrbitStabilizerRecognition
        recognitionFunctor
        sourceOrbits
        targetOrbits

open RecognitionTargetFor public

P3RecognitionTarget : Set₁
P3RecognitionTarget =
  RecognitionTargetFor
    Small.constantC2Action
    Small.constantTernaryOrbitPresentation

P2GaugeRecognitionTarget : Set₁
P2GaugeRecognitionTarget =
  RecognitionTargetFor
    Small.p2ResidualC2Action
    Small.p2ResidualOrbitPresentation

P2RetainedOrientationRecognitionTarget : Set₁
P2RetainedOrientationRecognitionTarget =
  RecognitionTargetFor
    Small.p2DiscreteAction
    Small.p2DiscreteOrbitPresentation

------------------------------------------------------------------------
-- 2. p=3 recognition must preserve the two orbit strata.
------------------------------------------------------------------------

p3OrbitRecognition :
  (target : P3RecognitionTarget) ->
  Recognition.OrbitRecognition
    (recognitionFunctor target)
    Small.constantTernaryOrbitPresentation
    (targetOrbits target)
p3OrbitRecognition target =
  Recognition.orbitRecognition (fullRecognition target)

p3Pi0Embedding :
  (target : P3RecognitionTarget) ->
  Recognition.Pi0Embedding (p3OrbitRecognition target)
p3Pi0Embedding target =
  Recognition.pi0Embedding (fullRecognition target)

p3StabilizerRecognition :
  (target : P3RecognitionTarget) ->
  Recognition.StabilizerRecognition (p3OrbitRecognition target)
p3StabilizerRecognition target =
  Recognition.stabilizerRecognition (fullRecognition target)

p3MappedZeroAndNonzeroOrbitsRemainDistinct :
  (target : P3RecognitionTarget) ->
  Recognition.mapOrbit
    (p3OrbitRecognition target)
    Small.zeroConstantOrbit
  ≡
  Recognition.mapOrbit
    (p3OrbitRecognition target)
    Small.nonzeroConstantOrbit
  ->
  ⊥
p3MappedZeroAndNonzeroOrbitsRemainDistinct target same =
  impossible
  where
    sourceSame :
      Small.zeroConstantOrbit ≡ Small.nonzeroConstantOrbit
    sourceSame =
      Recognition.reflectsOrbitEquality
        (p3Pi0Embedding target)
        same

    impossible : ⊥
    impossible with sourceSame
    ... | ()

p3MappedFlipFixesZeroRepresentative :
  (target : P3RecognitionTarget) ->
  Action.act
    (targetAction target)
    (Recognition.mapSymmetry (recognitionFunctor target) C2.flip)
    (Orbit.representative
      (targetOrbits target)
      (Recognition.mapOrbit
        (p3OrbitRecognition target)
        Small.zeroConstantOrbit))
  ≡
  Orbit.representative
    (targetOrbits target)
    (Recognition.mapOrbit
      (p3OrbitRecognition target)
      Small.zeroConstantOrbit)
p3MappedFlipFixesZeroRepresentative target =
  Recognition.preservesStabilizer
    (p3StabilizerRecognition target)
    Small.zeroConstantOrbit
    C2.flip
    refl

p3SourceFlipDoesNotFixNonzeroRepresentative :
  Action.act
    Small.constantC2Action
    C2.flip
    (Orbit.representative
      Small.constantTernaryOrbitPresentation
      Small.nonzeroConstantOrbit)
  ≡
  Orbit.representative
    Small.constantTernaryOrbitPresentation
    Small.nonzeroConstantOrbit
  ->
  ⊥
p3SourceFlipDoesNotFixNonzeroRepresentative ()

p3MappedFlipDoesNotFixNonzeroRepresentative :
  (target : P3RecognitionTarget) ->
  Action.act
    (targetAction target)
    (Recognition.mapSymmetry (recognitionFunctor target) C2.flip)
    (Orbit.representative
      (targetOrbits target)
      (Recognition.mapOrbit
        (p3OrbitRecognition target)
        Small.nonzeroConstantOrbit))
  ≡
  Orbit.representative
    (targetOrbits target)
    (Recognition.mapOrbit
      (p3OrbitRecognition target)
      Small.nonzeroConstantOrbit)
  ->
  ⊥
p3MappedFlipDoesNotFixNonzeroRepresentative target targetFix =
  p3SourceFlipDoesNotFixNonzeroRepresentative
    (Recognition.reflectsMappedStabilizer
      (p3StabilizerRecognition target)
      Small.nonzeroConstantOrbit
      C2.flip
      targetFix)

------------------------------------------------------------------------
-- 3. p=2 target semantics after codec cross-pollination.
--
-- The five-orbit projection is now known to have no left inverse on the
-- ten-object carrier.  Retained orientation is therefore not optional if the
-- target is required to reconstruct that carrier exactly.  What remains open
-- is whether the arithmetic supersingular/Fricke source is the same object.
------------------------------------------------------------------------

p2RetainedOrientationCodecReopensExactly :
  (state : Small.P2ResidualObject) →
  Codec.p2Decode (Codec.p2Encode state) ≡ state
p2RetainedOrientationCodecReopensExactly =
  Codec.p2DecodeEncodeExact

p2FiveOrbitProjectionCannotReopenTenCarrier :
  (recover : DASHI.Biology.TriadicKernelLiftQuotientExact.NineOrbit →
    Small.P2ResidualObject) →
  ((state : Small.P2ResidualObject) →
    recover (Codec.p2Project state) ≡ state) →
  (orbit : DASHI.Biology.TriadicKernelLiftQuotientExact.NineOrbit) →
  ⊥
p2FiveOrbitProjectionCannotReopenTenCarrier =
  Codec.p2CoarseProjectionHasNoLeftInverse

data ArithmeticRecognizesP2GaugeQuotient : Set where
data ArithmeticRecognizesP2RetainedOrientation : Set where
data CardinalityTenDecidesP2Recognition : Set where

arithmeticP2GaugeRecognitionStillOpen :
  ArithmeticRecognizesP2GaugeQuotient -> ⊥
arithmeticP2GaugeRecognitionStillOpen ()

arithmeticP2RetainedOrientationRecognitionStillOpen :
  ArithmeticRecognizesP2RetainedOrientation -> ⊥
arithmeticP2RetainedOrientationRecognitionStillOpen ()

cardinalityTenDoesNotDecideRecognition :
  CardinalityTenDecidesP2Recognition -> ⊥
cardinalityTenDoesNotDecideRecognition ()

------------------------------------------------------------------------
-- 4. Attribution / promotion boundary.
------------------------------------------------------------------------

recognitionObligationClaimOrigin : Source.ClaimOrigin
recognitionObligationClaimOrigin =
  Source.openRecognitionConjecture

data RecognitionTargetAlreadyConstructed : Set where
data Pi0CountEqualityCreatesFunctor : Set where
data StabilizerCardinalityAloneCreatesSameObjectRecognition : Set where

recognitionTargetStillOpen :
  RecognitionTargetAlreadyConstructed -> ⊥
recognitionTargetStillOpen ()

pi0CountEqualityDoesNotCreateFunctor :
  Pi0CountEqualityCreatesFunctor -> ⊥
pi0CountEqualityDoesNotCreateFunctor ()

stabilizerCardinalityDoesNotCreateSameObjectRecognition :
  StabilizerCardinalityAloneCreatesSameObjectRecognition -> ⊥
stabilizerCardinalityDoesNotCreateSameObjectRecognition ()

record OggSSP369RecognitionFunctorBoundary : Set where
  constructor ogg-ssp369-recognition-functor-boundary
  field
    p3SourceActionGroupoidExact : Bool
    p3TwoOrbitStrataMustRemainDistinct : Bool
    p3EnhancedZeroStabilizerMustBePreserved : Bool
    p3NonzeroFlipNonstabilizerMustBeReflected : Bool
    p2GaugeSourceAvailable : Bool
    p2RetainedOrientationSourceAvailable : Bool
    p2RetainedOrientationExactCodecOwned : Bool
    p2CoarseFiveOrbitProjectionProvablyLossy : Bool
    p2ForkResolvedByCardinality : Bool
    p2ExactLaneKeyOwned : Bool
    p3ExactLaneKeyOwned : Bool
    targetArithmetic369GroupoidConstructed : Bool
    fullRecognitionRequiresPi0Bijection : Bool
    fullRecognitionRequiresStabilizerPreservationReflection : Bool
    externalArithmeticAttributedUpstream : Bool

canonicalOggSSP369RecognitionFunctorBoundary :
  OggSSP369RecognitionFunctorBoundary
canonicalOggSSP369RecognitionFunctorBoundary =
  ogg-ssp369-recognition-functor-boundary
    true true true true
    true true true true false true true false
    true true true
