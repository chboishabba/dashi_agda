module DASHI.Moonshine.OggSSPP2Base369RecognitionForkExact where

------------------------------------------------------------------------
-- p=2 OGG/SSP CANDIDATE GROUPOIDS -> INDEPENDENT BASE369 TARGETS
--
-- DASHI CONTRIBUTION
--
-- Source fine carrier:
--   StrictSignedSide x NineOrbit
--
-- Independent target fine carrier:
--   Base369 OrientationPolarity x NineOrbit
--
-- Two semantics are recognised exactly:
--
--   gauge branch:
--     C2 flips the orientation sheet, pi0 = NineOrbit (5 components)
--
--   retained branch:
--     identity-only morphisms, pi0 = all ten fine states
--
-- Both recognitions preserve exact orientation provenance.  Therefore Base369
-- can realise either candidate semantics.  This does NOT decide which one is
-- the arithmetic supersingular/Fricke groupoid.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Core.ProvenancePreservingRecognitionFunctorExact as Provenance
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as Target
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Source
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact fine-carrier rechart.
------------------------------------------------------------------------

sideToPolarity :
  Compression.StrictSignedSide ->
  Mobius.OrientationPolarity
sideToPolarity Compression.lowerSide = Mobius.negative
sideToPolarity Compression.upperSide = Mobius.positive

polarityToSide :
  Mobius.OrientationPolarity ->
  Compression.StrictSignedSide
polarityToSide Mobius.negative = Compression.lowerSide
polarityToSide Mobius.positive = Compression.upperSide

sideRoundTrip :
  (side : Compression.StrictSignedSide) ->
  polarityToSide (sideToPolarity side) ≡ side
sideRoundTrip Compression.lowerSide = refl
sideRoundTrip Compression.upperSide = refl

polarityRoundTrip :
  (polarity : Mobius.OrientationPolarity) ->
  sideToPolarity (polarityToSide polarity) ≡ polarity
polarityRoundTrip Mobius.negative = refl
polarityRoundTrip Mobius.positive = refl

sourceToTargetState :
  Source.P2ResidualObject ->
  Target.P2Base369State
sourceToTargetState (side , orbit) =
  sideToPolarity side , orbit

targetToSourceState :
  Target.P2Base369State ->
  Source.P2ResidualObject
targetToSourceState (polarity , orbit) =
  polarityToSide polarity , orbit

sourceTargetStateRoundTrip :
  (state : Source.P2ResidualObject) ->
  targetToSourceState (sourceToTargetState state) ≡ state
sourceTargetStateRoundTrip (Compression.lowerSide , orbit) = refl
sourceTargetStateRoundTrip (Compression.upperSide , orbit) = refl

targetSourceStateRoundTrip :
  (state : Target.P2Base369State) ->
  sourceToTargetState (targetToSourceState state) ≡ state
targetSourceStateRoundTrip (Mobius.negative , orbit) = refl
targetSourceStateRoundTrip (Mobius.positive , orbit) = refl

sourceToTargetStateInjective :
  {left right : Source.P2ResidualObject} ->
  sourceToTargetState left ≡ sourceToTargetState right ->
  left ≡ right
sourceToTargetStateInjective {left} {right} same =
  trans
    (sym (sourceTargetStateRoundTrip left))
    (trans
      (cong targetToSourceState same)
      (sourceTargetStateRoundTrip right))

------------------------------------------------------------------------
-- 2. Orientation flips commute under the rechart.
------------------------------------------------------------------------

sideFlipCommutes :
  (side : Compression.StrictSignedSide) ->
  sideToPolarity (Source.flipStrictSide side)
  ≡ Mobius.flipOrientationPolarity (sideToPolarity side)
sideFlipCommutes Compression.lowerSide = refl
sideFlipCommutes Compression.upperSide = refl

------------------------------------------------------------------------
-- 3. Gauge-branch action recognition.
------------------------------------------------------------------------

p2GaugeActionRecognition :
  Recognition.ActionRecognitionFunctor
    Source.p2ResidualC2Action
    Target.p2GaugeAction
p2GaugeActionRecognition =
  Recognition.action-recognition-functor
    sourceToTargetState
    (λ g -> g)
    refl
    (λ g h -> refl)
    (λ g -> refl)
    equivariant
  where
    equivariant :
      (g : C2.C2) ->
      (state : Source.P2ResidualObject) ->
      sourceToTargetState (Source.actP2ResidualC2 g state)
      ≡
      Target.actGaugeC2 g (sourceToTargetState state)
    equivariant C2.identity state = refl
    equivariant C2.flip (side , orbit)
      rewrite sideFlipCommutes side = refl

p2GaugeOrbitRecognition :
  Recognition.OrbitRecognition
    p2GaugeActionRecognition
    Source.p2ResidualOrbitPresentation
    Target.p2GaugeOrbitPresentation
p2GaugeOrbitRecognition =
  Recognition.orbit-recognition
    (λ orbit -> orbit)
    (λ state -> refl)

p2GaugePi0Embedding :
  Recognition.Pi0Embedding p2GaugeOrbitRecognition
p2GaugePi0Embedding =
  Recognition.pi0-embedding (λ same -> same)

p2GaugePi0Surjection :
  Recognition.Pi0Surjection p2GaugeOrbitRecognition
p2GaugePi0Surjection =
  Recognition.pi0-surjection
    (λ orbit -> orbit)
    (λ orbit -> refl)

p2GaugeStabilizerRecognition :
  Recognition.StabilizerRecognition p2GaugeOrbitRecognition
p2GaugeStabilizerRecognition =
  Recognition.stabilizer-recognition
    (λ orbit -> refl)
    preserves
    reflects
  where
    preserves :
      (orbit : Triadic.NineOrbit) ->
      (g : C2.C2) ->
      Action.act Source.p2ResidualC2Action g
        (Orbit.representative Source.p2ResidualOrbitPresentation orbit)
      ≡
      Orbit.representative Source.p2ResidualOrbitPresentation orbit
      ->
      Action.act Target.p2GaugeAction g
        (Orbit.representative Target.p2GaugeOrbitPresentation orbit)
      ≡
      Orbit.representative Target.p2GaugeOrbitPresentation orbit
    preserves orbit C2.identity same = refl
    preserves orbit C2.flip ()

    reflects :
      (orbit : Triadic.NineOrbit) ->
      (g : C2.C2) ->
      Action.act Target.p2GaugeAction g
        (Orbit.representative Target.p2GaugeOrbitPresentation orbit)
      ≡
      Orbit.representative Target.p2GaugeOrbitPresentation orbit
      ->
      Action.act Source.p2ResidualC2Action g
        (Orbit.representative Source.p2ResidualOrbitPresentation orbit)
      ≡
      Orbit.representative Source.p2ResidualOrbitPresentation orbit
    reflects orbit C2.identity same = refl
    reflects orbit C2.flip ()

p2GaugeFullRecognition :
  Recognition.OrbitStabilizerRecognition
    p2GaugeActionRecognition
    Source.p2ResidualOrbitPresentation
    Target.p2GaugeOrbitPresentation
p2GaugeFullRecognition =
  Recognition.orbit-stabilizer-recognition
    p2GaugeOrbitRecognition
    p2GaugePi0Embedding
    p2GaugePi0Surjection
    p2GaugeStabilizerRecognition

------------------------------------------------------------------------
-- 4. Retained-orientation action/orbit recognition.
------------------------------------------------------------------------

p2RetainedActionRecognition :
  Recognition.ActionRecognitionFunctor
    Source.p2DiscreteAction
    Target.p2RetainedAction
p2RetainedActionRecognition =
  Recognition.action-recognition-functor
    sourceToTargetState
    (λ tt -> tt)
    refl
    (λ tt tt -> refl)
    (λ tt -> refl)
    (λ tt state -> refl)

p2RetainedOrbitRecognition :
  Recognition.OrbitRecognition
    p2RetainedActionRecognition
    Source.p2DiscreteOrbitPresentation
    Target.p2RetainedOrbitPresentation
p2RetainedOrbitRecognition =
  Recognition.orbit-recognition
    sourceToTargetState
    (λ state -> refl)

p2RetainedPi0Embedding :
  Recognition.Pi0Embedding p2RetainedOrbitRecognition
p2RetainedPi0Embedding =
  Recognition.pi0-embedding
    sourceToTargetStateInjective

p2RetainedPi0Surjection :
  Recognition.Pi0Surjection p2RetainedOrbitRecognition
p2RetainedPi0Surjection =
  Recognition.pi0-surjection
    targetToSourceState
    targetSourceStateRoundTrip

p2RetainedStabilizerRecognition :
  Recognition.StabilizerRecognition p2RetainedOrbitRecognition
p2RetainedStabilizerRecognition =
  Recognition.stabilizer-recognition
    (λ state -> refl)
    (λ state tt same -> refl)
    (λ state tt same -> refl)

p2RetainedFullRecognition :
  Recognition.OrbitStabilizerRecognition
    p2RetainedActionRecognition
    Source.p2DiscreteOrbitPresentation
    Target.p2RetainedOrbitPresentation
p2RetainedFullRecognition =
  Recognition.orbit-stabilizer-recognition
    p2RetainedOrbitRecognition
    p2RetainedPi0Embedding
    p2RetainedPi0Surjection
    p2RetainedStabilizerRecognition

------------------------------------------------------------------------
-- 5. Provenance preservation on both branches.
------------------------------------------------------------------------

SourceOrientationProvenance : Set
SourceOrientationProvenance =
  Compression.StrictSignedSide

TargetOrientationProvenance : Set
TargetOrientationProvenance =
  Mobius.OrientationPolarity

sourceOrientationProvenance :
  Source.P2ResidualObject ->
  SourceOrientationProvenance
sourceOrientationProvenance = proj₁

targetOrientationProvenance :
  Target.P2Base369State ->
  TargetOrientationProvenance
targetOrientationProvenance = proj₁

sideToPolarityInjective :
  {left right : Compression.StrictSignedSide} ->
  sideToPolarity left ≡ sideToPolarity right ->
  left ≡ right
sideToPolarityInjective {left} {right} same =
  trans
    (sym (sideRoundTrip left))
    (trans
      (cong polarityToSide same)
      (sideRoundTrip right))

gaugeProvenanceRecognition :
  Provenance.ProvenancePreservingActionRecognition
    Source.p2ResidualC2Action
    Target.p2GaugeAction
    sourceOrientationProvenance
    targetOrientationProvenance
gaugeProvenanceRecognition =
  Provenance.provenance-preserving-action-recognition
    p2GaugeActionRecognition
    sideToPolarity
    (λ (side , orbit) -> refl)
    reflect
  where
    reflect :
      {left right : Source.P2ResidualObject} ->
      targetOrientationProvenance (sourceToTargetState left)
      ≡ targetOrientationProvenance (sourceToTargetState right)
      ->
      sourceOrientationProvenance left
      ≡ sourceOrientationProvenance right
    reflect {(leftSide , leftOrbit)} {(rightSide , rightOrbit)} same =
      sideToPolarityInjective same

gaugeProvenanceOrbitRecognition :
  Provenance.ProvenancePreservingOrbitRecognition
    gaugeProvenanceRecognition
    Source.p2ResidualOrbitPresentation
    Target.p2GaugeOrbitPresentation
gaugeProvenanceOrbitRecognition =
  Provenance.provenance-preserving-orbit-recognition
    p2GaugeOrbitRecognition
    p2GaugePi0Embedding
    p2GaugePi0Surjection
    p2GaugeStabilizerRecognition

retainedProvenanceRecognition :
  Provenance.ProvenancePreservingActionRecognition
    Source.p2DiscreteAction
    Target.p2RetainedAction
    sourceOrientationProvenance
    targetOrientationProvenance
retainedProvenanceRecognition =
  Provenance.provenance-preserving-action-recognition
    p2RetainedActionRecognition
    sideToPolarity
    (λ (side , orbit) -> refl)
    reflect
  where
    reflect :
      {left right : Source.P2ResidualObject} ->
      targetOrientationProvenance (sourceToTargetState left)
      ≡ targetOrientationProvenance (sourceToTargetState right)
      ->
      sourceOrientationProvenance left
      ≡ sourceOrientationProvenance right
    reflect {(leftSide , leftOrbit)} {(rightSide , rightOrbit)} same =
      sideToPolarityInjective same

retainedProvenanceOrbitRecognition :
  Provenance.ProvenancePreservingOrbitRecognition
    retainedProvenanceRecognition
    Source.p2DiscreteOrbitPresentation
    Target.p2RetainedOrbitPresentation
retainedProvenanceOrbitRecognition =
  Provenance.provenance-preserving-orbit-recognition
    p2RetainedOrbitRecognition
    p2RetainedPi0Embedding
    p2RetainedPi0Surjection
    p2RetainedStabilizerRecognition

------------------------------------------------------------------------
-- 6. What this closes, and what remains open.
------------------------------------------------------------------------

gaugeBranchRecognisedByIndependent369Target : Bool
gaugeBranchRecognisedByIndependent369Target = true

retainedBranchRecognisedByIndependent369Target : Bool
retainedBranchRecognisedByIndependent369Target = true

data Both369RecognitionsDecideArithmeticBranch : Set where
data CarrierEquivalenceMakesGaugeAndRetainedGroupoidsEquivalent : Set where

both369RecognitionsDoNotDecideArithmeticBranch :
  Both369RecognitionsDecideArithmeticBranch -> ⊥
both369RecognitionsDoNotDecideArithmeticBranch ()

sameFineCarrierDoesNotMakeGroupoidsEquivalent :
  CarrierEquivalenceMakesGaugeAndRetainedGroupoidsEquivalent -> ⊥
sameFineCarrierDoesNotMakeGroupoidsEquivalent ()

recognitionClaimOrigin : Attribution.ClaimOrigin
recognitionClaimOrigin =
  Attribution.repositoryNewExtension

record OggSSPP2Base369RecognitionForkBoundary : Set where
  constructor ogg-ssp-p2-base369-recognition-fork-boundary
  field
    exactFineCarrierRechartProved : Bool
    gaugeActionEquivarianceProved : Bool
    gaugePi0BijectionProved : Bool
    gaugeStabilizersRecognised : Bool
    retainedPi0BijectionProved : Bool
    retainedStabilizersRecognised : Bool
    orientationProvenancePreservedOnGaugeBranch : Bool
    orientationProvenancePreservedOnRetainedBranch : Bool
    bothBase369SemanticsConstructed : Bool
    arithmeticBranchDecisionPaid : Bool
    sameFineCarrierMakesGroupoidsSameObject : Bool

canonicalOggSSPP2Base369RecognitionForkBoundary :
  OggSSPP2Base369RecognitionForkBoundary
canonicalOggSSPP2Base369RecognitionForkBoundary =
  ogg-ssp-p2-base369-recognition-fork-boundary
    true true true true
    true true true true
    true false false
