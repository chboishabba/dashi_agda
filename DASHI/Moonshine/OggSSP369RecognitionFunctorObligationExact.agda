module DASHI.Moonshine.OggSSP369RecognitionFunctorObligationExact where

------------------------------------------------------------------------
-- OGG / SSP SMALL-CHARACTERISTIC REVERSE-COMPATIBILITY FUNCTOR OBLIGATION
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
-- This owner is now explicitly the REVERSE compatibility direction:
--
--   G_p^369  --->  G_p^arith.
--
-- The canonical live recognition direction requested by the programme is
--
--   G_p^arith ---> G_p^369
--
-- and is owned separately by OggSSPArithmeticTo369RecognitionExact.
--
-- What remains open here is construction of an arithmetic/Fricke target
-- groupoid compatible with the already-owned 369 action groupoids.
-- No cardinality equality and no reverse compatibility witness is promoted
-- to the canonical arithmetic->369 recognition theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Core.ProvenancePreservingRecognitionFunctorExact as ProvenanceRecognition
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualCodecExact as Codec
import DASHI.Moonshine.OggSSPSmallCharacteristicCodecIndexedRecognitionExact as LaneCodec
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Moonshine.OggSSPArithmeticTo369RecognitionExact as Forward

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

p2RecognitionLaneKey : LaneCodec.ExactOggLaneKey
p2RecognitionLaneKey = LaneCodec.p2LaneKey

p3RecognitionLaneKey : LaneCodec.ExactOggLaneKey
p3RecognitionLaneKey = LaneCodec.p3LaneKey

p2RecognitionLaneDecodesExactly :
  LaneCodec.decodeExactLaneKey p2RecognitionLaneKey
  ≡ LaneCodec.lane p2RecognitionLaneKey
p2RecognitionLaneDecodesExactly =
  LaneCodec.decodeExactLaneKeyCorrect p2RecognitionLaneKey

p3RecognitionLaneDecodesExactly :
  LaneCodec.decodeExactLaneKey p3RecognitionLaneKey
  ≡ LaneCodec.lane p3RecognitionLaneKey
p3RecognitionLaneDecodesExactly =
  LaneCodec.decodeExactLaneKeyCorrect p3RecognitionLaneKey

p2FiveOrbitProjectionCannotReopenTenCarrier :
  (recover : Triadic.NineOrbit →
    Small.P2ResidualObject) →
  ((state : Small.P2ResidualObject) →
    recover (Codec.p2Project state) ≡ state) →
  (orbit : Triadic.NineOrbit) →
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
-- 4. Retained-orientation recognition can demand provenance preservation.
--
-- The source provenance here is the strict binary orientation itself.  This
-- does NOT prove that arithmetic chooses the retained-orientation branch; it
-- states exactly what must be preserved if that branch is the intended
-- recognition semantics.
------------------------------------------------------------------------

p2Orientation :
  Small.P2ResidualObject ->
  Compression.StrictSignedSide
p2Orientation = proj₁

record P2RetainedOrientationProvenanceTarget : Set₁ where
  field
    TargetState : Set
    TargetSymmetry : Set
    TargetProvenance : Set

    targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry

    targetOrbits :
      Orbit.OrbitPresentation targetAction

    targetProvenance :
      TargetState -> TargetProvenance

    provenanceRecognition :
      ProvenanceRecognition.ProvenancePreservingActionRecognition
        Small.p2DiscreteAction
        targetAction
        p2Orientation
        targetProvenance

    fullOrbitRecognition :
      ProvenanceRecognition.ProvenancePreservingOrbitRecognition
        provenanceRecognition
        Small.p2DiscreteOrbitPresentation
        targetOrbits

open P2RetainedOrientationProvenanceTarget public

data RetainedOrientationRecognitionMayEraseOrientation : Set where

retainedOrientationRecognitionMayNotEraseOrientation :
  RetainedOrientationRecognitionMayEraseOrientation -> ⊥
retainedOrientationRecognitionMayNotEraseOrientation ()

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
    retainedOrientationBranchRequiresOrientationProvenance : Bool
    externalArithmeticAttributedUpstream : Bool
    thisOwnerIsReverseCompatibilitySurface : Bool
    canonicalArithmeticTo369DirectionOwnedSeparately : Bool

canonicalOggSSP369RecognitionFunctorBoundary :
  OggSSP369RecognitionFunctorBoundary
canonicalOggSSP369RecognitionFunctorBoundary =
  ogg-ssp369-recognition-functor-boundary
    true true true true true
    true true true true false true true false
    true true true
