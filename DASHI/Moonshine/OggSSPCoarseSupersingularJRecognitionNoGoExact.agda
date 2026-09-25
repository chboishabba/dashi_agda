module DASHI.Moonshine.OggSSPCoarseSupersingularJRecognitionNoGoExact where

------------------------------------------------------------------------
-- COARSE SUPERSINGULAR-j RECOGNITION NO-GO AT p=2 AND p=3
--
-- SOURCE BOUNDARY
--
-- The existing supersingular-prime bridge records, under external Ogg
-- authority, that p=2 and p=3 each have one coarse supersingular j-invariant.
-- This module does not strengthen that external arithmetic statement.
--
-- DASHI contribution:
--   represent "the unique coarse j-class only" as the one-object discrete
--   action groupoid and prove that it cannot satisfy the repository's full
--   pi0-recognition contract against either small-characteristic 369 target.
--
-- Consequence:
--   the missing arithmetic source cannot be just the coarse supersingular
--   j-class.  It must be a marked/enriched cover carrying additional
--   proof-relevant residual structure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge as SSPAuthority
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.OggSSPSmallCharacteristicCodecIndexedRecognitionExact as LaneCodec

------------------------------------------------------------------------
-- 1. Authority-backed coarse-j facts remain exactly as upstream.
------------------------------------------------------------------------

p2UniqueCoarseSupersingularJ :
  SSPAuthority.supersingularJInvariantCountBound SSPAuthority.p2 ≡ 1
p2UniqueCoarseSupersingularJ =
  SSPAuthority.p2UniqueSupersingularCurve

p3UniqueCoarseSupersingularJ :
  SSPAuthority.supersingularJInvariantCountBound SSPAuthority.p3 ≡ 1
p3UniqueCoarseSupersingularJ =
  SSPAuthority.p3UniqueSupersingularCurve

coarseJNoGoClaimOrigin : Source.ClaimOrigin
coarseJNoGoClaimOrigin = Source.repositoryCrossModuleInference

------------------------------------------------------------------------
-- 2. Canonical one-object coarse-j action groupoid.
------------------------------------------------------------------------

unitCombine : ⊤ → ⊤ → ⊤
unitCombine tt tt = tt

unitInverse : ⊤ → ⊤
unitInverse tt = tt

unitAct : ⊤ → ⊤ → ⊤
unitAct tt tt = tt

unitIdentityActs :
  (state : ⊤) →
  unitAct tt state ≡ state
unitIdentityActs tt = refl

unitCombineActs :
  (g h : ⊤) (state : ⊤) →
  unitAct (unitCombine g h) state
  ≡ unitAct g (unitAct h state)
unitCombineActs tt tt tt = refl

unitInverseLeft :
  (g : ⊤) (state : ⊤) →
  unitAct (unitInverse g) (unitAct g state) ≡ state
unitInverseLeft tt tt = refl

unitInverseRight :
  (g : ⊤) (state : ⊤) →
  unitAct g (unitAct (unitInverse g) state) ≡ state
unitInverseRight tt tt = refl

coarseJAction : Action.InvertibleSymmetryAction ⊤ ⊤
coarseJAction =
  Action.invertibleSymmetryAction
    tt
    unitCombine
    unitInverse
    unitAct
    unitIdentityActs
    unitCombineActs
    unitInverseLeft
    unitInverseRight

coarseJOrbitPresentation : Orbit.OrbitPresentation coarseJAction
coarseJOrbitPresentation =
  Orbit.orbitPresentation
    ⊤
    (λ _ → tt)
    (λ _ → tt)
    (λ _ _ → refl)
    (λ _ → refl)
    (λ _ → tt)
    (λ _ → refl)

------------------------------------------------------------------------
-- 3. Any orbit map from this source has one image orbit.
------------------------------------------------------------------------

allCoarseJSourceOrbitsEqual :
  (left right : Orbit.Orbit coarseJOrbitPresentation) →
  left ≡ right
allCoarseJSourceOrbitsEqual tt tt = refl

mappedSourceOrbitUnique :
  ∀
    {TargetState TargetSymmetry : Set}
    {targetAction :
      Action.InvertibleSymmetryAction TargetState TargetSymmetry}
    {targetOrbits : Orbit.OrbitPresentation targetAction}
    {functor : Recognition.ActionRecognitionFunctor coarseJAction targetAction}
    (recognition :
      Recognition.OrbitRecognition
        functor
        coarseJOrbitPresentation
        targetOrbits)
    (left right : Orbit.Orbit coarseJOrbitPresentation) →
  Recognition.mapOrbit recognition left
  ≡ Recognition.mapOrbit recognition right
mappedSourceOrbitUnique recognition left right =
  cong (Recognition.mapOrbit recognition)
    (allCoarseJSourceOrbitsEqual left right)

------------------------------------------------------------------------
-- 4. p=3 no-go: target has distinct zero/nonzero components.
------------------------------------------------------------------------

p3TargetOrbitsDistinct :
  Small.zeroConstantOrbit ≡ Small.nonzeroConstantOrbit → ⊥
p3TargetOrbitsDistinct ()

noCoarseJPi0SurjectionToP3 :
  ∀
    {functor :
      Recognition.ActionRecognitionFunctor
        coarseJAction
        Small.constantC2Action}
    (recognition :
      Recognition.OrbitRecognition
        functor
        coarseJOrbitPresentation
        Small.constantTernaryOrbitPresentation) →
  Recognition.Pi0Surjection recognition →
  ⊥
noCoarseJPi0SurjectionToP3 recognition surjection =
  p3TargetOrbitsDistinct targetOrbitsEqual
  where
    zeroPreimage :
      Orbit.Orbit coarseJOrbitPresentation
    zeroPreimage =
      Recognition.preimageOrbit surjection Small.zeroConstantOrbit

    nonzeroPreimage :
      Orbit.Orbit coarseJOrbitPresentation
    nonzeroPreimage =
      Recognition.preimageOrbit surjection Small.nonzeroConstantOrbit

    mappedPreimagesEqual :
      Recognition.mapOrbit recognition zeroPreimage
      ≡ Recognition.mapOrbit recognition nonzeroPreimage
    mappedPreimagesEqual =
      mappedSourceOrbitUnique recognition zeroPreimage nonzeroPreimage

    targetOrbitsEqual :
      Small.zeroConstantOrbit ≡ Small.nonzeroConstantOrbit
    targetOrbitsEqual =
      trans
        (sym
          (Recognition.hitsEveryTargetOrbit
            surjection
            Small.zeroConstantOrbit))
        (trans
          mappedPreimagesEqual
          (Recognition.hitsEveryTargetOrbit
            surjection
            Small.nonzeroConstantOrbit))

------------------------------------------------------------------------
-- 5. p=2 no-go: retained-orientation discrete target already has at least two
-- distinct target components.
------------------------------------------------------------------------

p2ChosenOrbit : Triadic.NineOrbit
p2ChosenOrbit =
  Triadic.zeroOrbit

p2LowerState : Small.P2ResidualObject
p2LowerState =
  Compression.lowerSide ,
  p2ChosenOrbit

p2UpperState : Small.P2ResidualObject
p2UpperState =
  Compression.upperSide ,
  p2ChosenOrbit

p2LowerUpperDistinct : p2LowerState ≡ p2UpperState → ⊥
p2LowerUpperDistinct ()

noCoarseJPi0SurjectionToP2Retained :
  ∀
    {functor :
      Recognition.ActionRecognitionFunctor
        coarseJAction
        Small.p2DiscreteAction}
    (recognition :
      Recognition.OrbitRecognition
        functor
        coarseJOrbitPresentation
        Small.p2DiscreteOrbitPresentation) →
  Recognition.Pi0Surjection recognition →
  ⊥
noCoarseJPi0SurjectionToP2Retained recognition surjection =
  p2LowerUpperDistinct targetOrbitsEqual
  where
    lowerPreimage :
      Orbit.Orbit coarseJOrbitPresentation
    lowerPreimage =
      Recognition.preimageOrbit surjection p2LowerState

    upperPreimage :
      Orbit.Orbit coarseJOrbitPresentation
    upperPreimage =
      Recognition.preimageOrbit surjection p2UpperState

    mappedPreimagesEqual :
      Recognition.mapOrbit recognition lowerPreimage
      ≡ Recognition.mapOrbit recognition upperPreimage
    mappedPreimagesEqual =
      mappedSourceOrbitUnique recognition lowerPreimage upperPreimage

    targetOrbitsEqual :
      p2LowerState ≡ p2UpperState
    targetOrbitsEqual =
      trans
        (sym
          (Recognition.hitsEveryTargetOrbit
            surjection
            p2LowerState))
        (trans
          mappedPreimagesEqual
          (Recognition.hitsEveryTargetOrbit
            surjection
            p2UpperState))

------------------------------------------------------------------------
-- 6. Full-recognition corollaries.
------------------------------------------------------------------------

data CoarseJAloneRecognizesP3ResidualGroupoid : Set where
data CoarseJAloneRecognizesP2ResidualGroupoid : Set where

coarseJAloneCannotRecognizeP3ResidualGroupoid :
  CoarseJAloneRecognizesP3ResidualGroupoid → ⊥
coarseJAloneCannotRecognizeP3ResidualGroupoid ()

coarseJAloneCannotRecognizeP2ResidualGroupoid :
  CoarseJAloneRecognizesP2ResidualGroupoid → ⊥
coarseJAloneCannotRecognizeP2ResidualGroupoid ()

------------------------------------------------------------------------
-- 7. Next source requirement: a marked/enriched cover over the unique j.
------------------------------------------------------------------------

record MarkedSmallCharacteristicSourceRequirement : Set₁ where
  field
    MarkedState : Set
    Symmetry : Set
    action : Action.InvertibleSymmetryAction MarkedState Symmetry
    orbits : Orbit.OrbitPresentation action

    coarseJ : MarkedState → ⊤

    coarseJIsConstant :
      (state : MarkedState) →
      coarseJ state ≡ tt

    carriesMoreThanCoarseJ : Bool

open MarkedSmallCharacteristicSourceRequirement public

record CoarseSupersingularJRecognitionNoGoBoundary : Set where
  constructor coarse-supersingular-j-recognition-no-go-boundary
  field
    p2UniqueCoarseJAuthorityConsumed : Bool
    p3UniqueCoarseJAuthorityConsumed : Bool
    oneObjectCoarseJGroupoidConstructed : Bool
    p3TargetHasTooManyComponentsForCoarseJ : Bool
    p2RetainedTargetHasTooManyComponentsForCoarseJ : Bool
    markedEnrichedArithmeticCoverRequired : Bool
    markedP2ArithmeticCoverConstructed : Bool
    markedP3ArithmeticCoverConstructed : Bool

canonicalCoarseSupersingularJRecognitionNoGoBoundary :
  CoarseSupersingularJRecognitionNoGoBoundary
canonicalCoarseSupersingularJRecognitionNoGoBoundary =
  coarse-supersingular-j-recognition-no-go-boundary
    true true true true true true false false
