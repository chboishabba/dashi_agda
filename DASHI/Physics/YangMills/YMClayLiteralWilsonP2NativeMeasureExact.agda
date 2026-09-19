{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonP2NativeMeasureExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; map)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact as Bounds
import DASHI.Physics.YangMills.BalabanLiteralWilsonNativeThermodynamicProducerExact as NativeThermo
import DASHI.Physics.YangMills.BalabanLiteralWilsonNativePhysicalMeasureExact as NativeMeasure

------------------------------------------------------------------------
-- P2 ON THE NATIVE WILSON MEASURE CARRIER, WITH NO DISTANCE SEMANTICS.
--
-- Expectation convergence only consumes bounded observables.  Euclidean
-- support-distance geometry belongs to P1/S2a and is not logically required
-- for the three P2 limits.
------------------------------------------------------------------------

record NativeWilsonP2Limits
    {Measure : Set} {n : Nat}
    {operationsInputs :
      NativeThermo.NativeWilsonOSOperationsInputs Measure n}
    (measureInputs :
      NativeMeasure.NativeWilsonPreferredPhysicalMeasureInputs
        Measure n operationsInputs)
    (translateLoop :
      Wilson.RationalWilsonPath n → Nat → Wilson.RationalWilsonPath n)
    (left right : List (Wilson.RationalWilsonPath n))
    (time : Nat) : Set₁ where
  private
    dataSet = NativeMeasure.nativeWilsonPhysicalMeasureData measureInputs
    wilson = Bounds.literalRationalSU2WilsonCylinderBounds
    leftObservable = T5.productLoopObservable wilson left
    translatedRightObservable =
      T5.productLoopObservable wilson
        (map (λ loop → translateLoop loop time) right)
  field
    leftExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff) leftObservable)
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet) leftObservable)

    translatedRightExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            translatedRightObservable)
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          translatedRightObservable)

    productExpectationConverges :
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.expectation (Gram.operations dataSet)
            (Gram.measureSequence dataSet cutoff)
            (Wilson.multiplyObservable
              leftObservable translatedRightObservable))
        (Gram.expectation (Gram.operations dataSet)
          (Gram.continuumMeasure dataSet)
          (Wilson.multiplyObservable
            leftObservable translatedRightObservable))

open NativeWilsonP2Limits public

nativeWilsonP2Limits :
  ∀ {Measure n operationsInputs}
    (measureInputs :
      NativeMeasure.NativeWilsonPreferredPhysicalMeasureInputs
        Measure n operationsInputs)
    (translateLoop :
      Wilson.RationalWilsonPath n → Nat → Wilson.RationalWilsonPath n)
    (left right : List (Wilson.RationalWilsonPath n))
    (time : Nat) →
  NativeWilsonP2Limits measureInputs translateLoop left right time
nativeWilsonP2Limits measureInputs translateLoop left right time =
  let
    dataSet = NativeMeasure.nativeWilsonPhysicalMeasureData measureInputs
    wilson = Bounds.literalRationalSU2WilsonCylinderBounds
    translated = map (λ loop → translateLoop loop time) right
    leftObservable = T5.productLoopObservable wilson left
    rightObservable = T5.productLoopObservable wilson translated
    leftQuant = Bounds.finiteLiteralWilsonCylinderBound left
    rightQuant = Bounds.finiteLiteralWilsonCylinderBound translated
    leftMajorant = T5.productLoopBound wilson left
    rightMajorant = T5.productLoopBound wilson translated
    productQuant =
      Bounds.quantitativeMultiplyBound
        leftObservable rightObservable leftMajorant rightMajorant
        leftQuant rightQuant
    leftBounded =
      NativeMeasure.quantitativeBoundIsNativePhysicalBounded
        measureInputs leftObservable leftMajorant leftQuant
    rightBounded =
      NativeMeasure.quantitativeBoundIsNativePhysicalBounded
        measureInputs rightObservable rightMajorant rightQuant
    productBounded =
      NativeMeasure.quantitativeBoundIsNativePhysicalBounded
        measureInputs
        (Wilson.multiplyObservable leftObservable rightObservable)
        (T5.multiplyScalar wilson leftMajorant rightMajorant)
        productQuant
  in
  record
    { NativeWilsonP2Limits.leftExpectationConverges =
        R278.selectedExpectationConverges
          dataSet leftObservable leftBounded
    ; NativeWilsonP2Limits.translatedRightExpectationConverges =
        R278.selectedExpectationConverges
          dataSet rightObservable rightBounded
    ; NativeWilsonP2Limits.productExpectationConverges =
        R278.selectedExpectationConverges
          dataSet
          (Wilson.multiplyObservable leftObservable rightObservable)
          productBounded
    }

p2SupportDistanceGeometryRequired : Agda.Builtin.Bool.Bool
p2SupportDistanceGeometryRequired = Agda.Builtin.Bool.false

p2NativeMeasureCompilerLevel : ProofLevel
p2NativeMeasureCompilerLevel = machineChecked
