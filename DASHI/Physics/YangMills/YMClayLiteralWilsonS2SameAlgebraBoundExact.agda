{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonS2SameAlgebraBoundExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; map)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.YMClayLiteralWilsonS2CanonicalProductPresentationExact as S2
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonTraceBoundExact as Trace

------------------------------------------------------------------------
-- ROUTE-S S2 / WILSON BOUNDS ON THE SAME T5 OBSERVABLE ALGEBRA
--
-- Construct the Wilson bound package directly on Gram.operations:
--
--   Wilson multiplyObservable := Gram.multiplyObservable
--   Wilson Bound O b          := Gram.BoundedObservable O.
--
-- The numerical bound parameter remains available for the finite-product
-- recursion but carries no second boundedness predicate.  Therefore the
-- multiplication weld and Wilson-bound -> T5-bounded weld are definitional.
------------------------------------------------------------------------

record SameAlgebraWilsonBoundInputs
    {Measure TestObservable Loop : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    : Set₁ where
  field
    loopObservable : Loop → TestObservable

    one groupRank : ℚ
    multiplyScalar : ℚ → ℚ → ℚ

    literalLoopBounded : ∀ loop →
      Gram.BoundedObservable dataSet (loopObservable loop)

    boundedMultiplyClosed : ∀ left right →
      Gram.BoundedObservable dataSet left →
      Gram.BoundedObservable dataSet right →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet) left right)

    identityObservable : TestObservable
    identityBounded :
      Gram.BoundedObservable dataSet identityObservable

open SameAlgebraWilsonBoundInputs public

sameAlgebraWilsonCylinderBoundData :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ} →
  SameAlgebraWilsonBoundInputs {Loop = Loop} dataSet →
  Thermo.WilsonCylinderBoundData Loop TestObservable ℚ
sameAlgebraWilsonCylinderBoundData {dataSet = dataSet} inputs = record
  { Thermo.WilsonCylinderBoundData.loopObservable = loopObservable inputs
  ; Thermo.WilsonCylinderBoundData.multiplyObservable =
      Gram.multiplyObservable (Gram.operations dataSet)
  ; Thermo.WilsonCylinderBoundData.identityObservable =
      identityObservable inputs
  ; Thermo.WilsonCylinderBoundData.Bound =
      λ observable _ → Gram.BoundedObservable dataSet observable
  ; Thermo.WilsonCylinderBoundData.one = one inputs
  ; Thermo.WilsonCylinderBoundData.groupRank = groupRank inputs
  ; Thermo.WilsonCylinderBoundData.multiplyScalar = multiplyScalar inputs
  ; Thermo.WilsonCylinderBoundData.wilsonLoopObservableUniformBound =
      literalLoopBounded inputs
  ; Thermo.WilsonCylinderBoundData.multiplyBound =
      λ left right leftBound rightBound leftBounded rightBounded →
        boundedMultiplyClosed inputs left right leftBounded rightBounded
  ; Thermo.WilsonCylinderBoundData.identityBound = identityBounded inputs
  }

record SameAlgebraCanonicalS2Inputs
    {Measure TestObservable Loop : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (finite : R296.ExactT5JMagnitudePresentation dataSet extension)
    : Set₁ where
  field
    boundInputs : SameAlgebraWilsonBoundInputs {Loop = Loop} dataSet

    translateLoop : Loop → Nat → Loop

    supportDistanceIsTime : ∀ left right time →
      let wilson = sameAlgebraWilsonCylinderBoundData boundInputs in
      R304.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        (Thermo.productLoopObservable wilson left)
        (Thermo.productLoopObservable wilson
          (map (λ loop → translateLoop loop time) right))
      ≡ time

open SameAlgebraCanonicalS2Inputs public

asCanonicalWilsonProductS2Inputs :
  ∀ {Measure TestObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension} →
  SameAlgebraCanonicalS2Inputs {Loop = Loop} finite →
  S2.CanonicalWilsonProductS2Inputs finite
asCanonicalWilsonProductS2Inputs {dataSet = dataSet} inputs = record
  { S2.CanonicalWilsonProductS2Inputs.wilson =
      sameAlgebraWilsonCylinderBoundData (boundInputs inputs)
  ; S2.CanonicalWilsonProductS2Inputs.translateLoop = translateLoop inputs
  ; S2.CanonicalWilsonProductS2Inputs.supportDistanceIsTime =
      supportDistanceIsTime inputs
  ; S2.CanonicalWilsonProductS2Inputs.wilsonMultiplyIsT5Multiply =
      λ left right → refl
  ; S2.CanonicalWilsonProductS2Inputs.wilsonBoundImpliesT5Bounded =
      λ observable bound bounded → bounded
  }

------------------------------------------------------------------------
-- Frontier reduction.
------------------------------------------------------------------------

independentWilsonT5MultiplicationWeldRequired : Bool
independentWilsonT5MultiplicationWeldRequired = false

independentWilsonT5MultiplicationWeldRequiredIsFalse :
  independentWilsonT5MultiplicationWeldRequired ≡ false
independentWilsonT5MultiplicationWeldRequiredIsFalse = refl

independentWilsonBoundPredicateWeldRequired : Bool
independentWilsonBoundPredicateWeldRequired = false

independentWilsonBoundPredicateWeldRequiredIsFalse :
  independentWilsonBoundPredicateWeldRequired ≡ false
independentWilsonBoundPredicateWeldRequiredIsFalse = refl


rationalSU2NormalizedTraceBoundCompilerLevel : ProofLevel
rationalSU2NormalizedTraceBoundCompilerLevel =
  Trace.rationalSU2NormalizedTraceBoundLevel

independentCompactGroupTraceInequalityStillRequired : Bool
independentCompactGroupTraceInequalityStillRequired = false

independentCompactGroupTraceInequalityStillRequiredIsFalse :
  independentCompactGroupTraceInequalityStillRequired ≡ false
independentCompactGroupTraceInequalityStillRequiredIsFalse = refl

quantitativeBoundToGramPredicateStillPhysical : Bool
quantitativeBoundToGramPredicateStillPhysical = true

quantitativeBoundToGramPredicateStillPhysicalIsTrue :
  quantitativeBoundToGramPredicateStillPhysical ≡ true
quantitativeBoundToGramPredicateStillPhysicalIsTrue = refl

literalLoopBoundednessStillPhysical : Bool
literalLoopBoundednessStillPhysical = true

literalLoopBoundednessStillPhysicalIsTrue :
  literalLoopBoundednessStillPhysical ≡ true
literalLoopBoundednessStillPhysicalIsTrue = refl

boundedObservableMultiplicationClosureStillPhysical : Bool
boundedObservableMultiplicationClosureStillPhysical = true

boundedObservableMultiplicationClosureStillPhysicalIsTrue :
  boundedObservableMultiplicationClosureStillPhysical ≡ true
boundedObservableMultiplicationClosureStillPhysicalIsTrue = refl

identityObservableBoundednessStillPhysical : Bool
identityObservableBoundednessStillPhysical = true

identityObservableBoundednessStillPhysicalIsTrue :
  identityObservableBoundednessStillPhysical ≡ true
identityObservableBoundednessStillPhysicalIsTrue = refl

sameAlgebraWilsonBoundCompilerLevel : ProofLevel
sameAlgebraWilsonBoundCompilerLevel = machineChecked

sameAlgebraRemainingBoundednessInputsLevel : ProofLevel
sameAlgebraRemainingBoundednessInputsLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
