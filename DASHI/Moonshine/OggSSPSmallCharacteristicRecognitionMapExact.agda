module DASHI.Moonshine.OggSSPSmallCharacteristicRecognitionMapExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC ORBIT/STABILIZER RECOGNITION MAP
--
-- Highest-alpha recognition contract for the p=2 / p=3 residual problem.
--
-- A numerical match is not enough.  A recognition map must preserve:
--
--   * object-to-orbit incidence;
--   * the orbit carrier up to explicit two-sided inverse;
--   * stabilizer size on corresponding orbit strata.
--
-- This is deliberately weaker than claiming a categorical functor on an
-- arithmetic supersingular groupoid that the repository does not yet own.
-- It is exactly the structure currently needed to prevent 5=10-style
-- cardinal coincidences from being mistaken for same-object recognition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)

import DASHI.Core.OrbitStabilizerResidualPresentationExact as Generic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2Bridge
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small

------------------------------------------------------------------------
-- 1. Generic recognition contract.
------------------------------------------------------------------------

record OrbitStabilizerRecognitionMap
    {SourceState SourceGroup TargetState TargetGroup : Set}
    (sourceAction :
      Symmetry.InvertibleSymmetryAction SourceState SourceGroup)
    (sourcePresentation : Generic.OrbitPresentation sourceAction)
    (targetAction :
      Symmetry.InvertibleSymmetryAction TargetState TargetGroup)
    (targetPresentation : Generic.OrbitPresentation targetAction)
    (sourceStabilizerSize :
      Generic.Orbit sourcePresentation -> Nat)
    (targetStabilizerSize :
      Generic.Orbit targetPresentation -> Nat)
    : Set₁ where
  constructor orbit-stabilizer-recognition-map
  field
    objectMap : SourceState -> TargetState

    orbitMap :
      Generic.Orbit sourcePresentation ->
      Generic.Orbit targetPresentation

    orbitBack :
      Generic.Orbit targetPresentation ->
      Generic.Orbit sourcePresentation

    objectOrbitPreserved :
      (state : SourceState) ->
      orbitMap
        (Generic.orbitOf sourcePresentation state)
      ≡ Generic.orbitOf
          targetPresentation
          (objectMap state)

    orbitLeftInverse :
      (orbit : Generic.Orbit sourcePresentation) ->
      orbitBack (orbitMap orbit) ≡ orbit

    orbitRightInverse :
      (orbit : Generic.Orbit targetPresentation) ->
      orbitMap (orbitBack orbit) ≡ orbit

    stabilizerSizePreserved :
      (orbit : Generic.Orbit sourcePresentation) ->
      sourceStabilizerSize orbit
      ≡ targetStabilizerSize (orbitMap orbit)

open OrbitStabilizerRecognitionMap public

------------------------------------------------------------------------
-- 2. The three repo-native target signatures.
------------------------------------------------------------------------

p3TargetStabilizerSize : Small.ConstantTernaryOrbit -> Nat
p3TargetStabilizerSize = Small.constantStabilizerSize

p2FlipTargetStabilizerSize : Triadic.NineOrbit -> Nat
p2FlipTargetStabilizerSize orbit = 1

p2RetainedTargetStabilizerSize : Small.P2ResidualObject -> Nat
p2RetainedTargetStabilizerSize state = 1

record P3ArithmeticRecognitionTarget
    {ArithmeticState ArithmeticGroup : Set}
    (arithmeticAction :
      Symmetry.InvertibleSymmetryAction ArithmeticState ArithmeticGroup)
    (arithmeticPresentation :
      Generic.OrbitPresentation arithmeticAction)
    (arithmeticStabilizerSize :
      Generic.Orbit arithmeticPresentation -> Nat)
    : Set₁ where
  constructor p3-arithmetic-recognition-target
  field
    recognition :
      OrbitStabilizerRecognitionMap
        arithmeticAction
        arithmeticPresentation
        Small.constantC2Action
        Small.constantTernaryOrbitPresentation
        arithmeticStabilizerSize
        p3TargetStabilizerSize

record P2FlipArithmeticRecognitionTarget
    {ArithmeticState ArithmeticGroup : Set}
    (arithmeticAction :
      Symmetry.InvertibleSymmetryAction ArithmeticState ArithmeticGroup)
    (arithmeticPresentation :
      Generic.OrbitPresentation arithmeticAction)
    (arithmeticStabilizerSize :
      Generic.Orbit arithmeticPresentation -> Nat)
    : Set₁ where
  constructor p2-flip-arithmetic-recognition-target
  field
    recognition :
      OrbitStabilizerRecognitionMap
        arithmeticAction
        arithmeticPresentation
        Small.p2ResidualC2Action
        Small.p2ResidualOrbitPresentation
        arithmeticStabilizerSize
        p2FlipTargetStabilizerSize

record P2RetainedArithmeticRecognitionTarget
    {ArithmeticState ArithmeticGroup : Set}
    (arithmeticAction :
      Symmetry.InvertibleSymmetryAction ArithmeticState ArithmeticGroup)
    (arithmeticPresentation :
      Generic.OrbitPresentation arithmeticAction)
    (arithmeticStabilizerSize :
      Generic.Orbit arithmeticPresentation -> Nat)
    : Set₁ where
  constructor p2-retained-arithmetic-recognition-target
  field
    recognition :
      OrbitStabilizerRecognitionMap
        arithmeticAction
        arithmeticPresentation
        Small.p2DiscreteAction
        Small.p2DiscreteOrbitPresentation
        arithmeticStabilizerSize
        p2RetainedTargetStabilizerSize

------------------------------------------------------------------------
-- 3. Structural consequence: recognition cannot be cardinality-only.
------------------------------------------------------------------------

data ResidualCardinalityMatchAloneIsRecognition : Set where

cardinalityMatchAloneDoesNotSupplyRecognition :
  ResidualCardinalityMatchAloneIsRecognition -> ⊥
cardinalityMatchAloneDoesNotSupplyRecognition ()

record RecognitionBoundary : Set where
  constructor recognition-boundary
  field
    objectOrbitIncidenceRequired : Bool
    orbitBijectionRequired : Bool
    stabilizerPreservationRequired : Bool
    p3TargetSignatureConstructed : Bool
    p2FlipTargetSignatureConstructed : Bool
    p2RetainedTargetSignatureConstructed : Bool
    arithmeticP3RecognitionInhabited : Bool
    arithmeticP2FlipRecognitionInhabited : Bool
    arithmeticP2RetainedRecognitionInhabited : Bool

canonicalRecognitionBoundary : RecognitionBoundary
canonicalRecognitionBoundary =
  recognition-boundary
    true true true
    true true true
    false false false
