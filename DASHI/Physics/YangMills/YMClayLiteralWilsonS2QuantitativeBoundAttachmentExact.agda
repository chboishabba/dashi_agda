{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonS2QuantitativeBoundAttachmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (map)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact as Bounds
import DASHI.Physics.YangMills.YMClayLiteralWilsonS2CanonicalProductPresentationExact as S2

------------------------------------------------------------------------
-- ROUTE-S S2 / QUANTITATIVE WILSON BOUNDS -> T5 BOUNDED-OBSERVABLE ATTACHMENT
--
-- The concrete rational-SU(2) lane now proves an inspectable quantitative
-- bound for every finite Wilson cylinder.  R315 does not need separate
-- primitive assumptions saying:
--
--   * every literal loop is T5-bounded,
--   * T5 bounded observables are closed under multiplication,
--   * the identity is T5-bounded.
--
-- Its actual consumer only needs each Wilson-cylinder Bound proof interpreted
-- as the existing Gram.BoundedObservable predicate.  Because the finite-product
-- Bound proof is already constructed by the Wilson cylinder compiler, one
-- semantic attachment pays all three old boundedness leaves on the selected
-- literal Wilson algebra.
------------------------------------------------------------------------

record QuantitativeLiteralWilsonS2Inputs
    {Measure : Set}
    {n : Nat}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData
        Measure (Wilson.RationalWilsonObservable n) ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (finite : R296.ExactT5JMagnitudePresentation dataSet extension)
    : Set₁ where
  field
    translateLoop :
      Wilson.RationalWilsonPath n →
      Nat →
      Wilson.RationalWilsonPath n

    supportDistanceIsTime : ∀ left right time →
      R304.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        (Thermo.productLoopObservable
          Bounds.literalRationalSU2WilsonCylinderBounds left)
        (Thermo.productLoopObservable
          Bounds.literalRationalSU2WilsonCylinderBounds
          (map (λ loop → translateLoop loop time) right))
      ≡ time

    pointwiseMultiplyIsT5Multiply : ∀ left right →
      Wilson.multiplyObservable left right
      ≡ Gram.multiplyObservable (Gram.operations dataSet) left right

    quantitativeBoundImpliesT5Bounded : ∀ observable majorant →
      Bounds.QuantitativeBound observable majorant →
      Gram.BoundedObservable dataSet observable

open QuantitativeLiteralWilsonS2Inputs public

asCanonicalWilsonProductS2Inputs :
  ∀ {Measure n}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData
        Measure (Wilson.RationalWilsonObservable n) ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension} →
  QuantitativeLiteralWilsonS2Inputs finite →
  S2.CanonicalWilsonProductS2Inputs finite
asCanonicalWilsonProductS2Inputs inputs = record
  { S2.CanonicalWilsonProductS2Inputs.wilson =
      Bounds.literalRationalSU2WilsonCylinderBounds
  ; S2.CanonicalWilsonProductS2Inputs.translateLoop =
      translateLoop inputs
  ; S2.CanonicalWilsonProductS2Inputs.supportDistanceIsTime =
      supportDistanceIsTime inputs
  ; S2.CanonicalWilsonProductS2Inputs.wilsonMultiplyIsT5Multiply =
      pointwiseMultiplyIsT5Multiply inputs
  ; S2.CanonicalWilsonProductS2Inputs.wilsonBoundImpliesT5Bounded =
      quantitativeBoundImpliesT5Bounded inputs
  }

quantitativeLiteralWilsonS2BuildsBoundedTests :
  ∀ {Measure n}
    {dataSet :
      Gram.PhysicalMeasureConvergenceData
        Measure (Wilson.RationalWilsonObservable n) ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (inputs : QuantitativeLiteralWilsonS2Inputs finite) →
  _
quantitativeLiteralWilsonS2BuildsBoundedTests inputs =
  S2.canonicalWilsonBoundedTests
    (asCanonicalWilsonProductS2Inputs inputs)

------------------------------------------------------------------------
-- Min-cut accounting.
------------------------------------------------------------------------

separateLiteralLoopBoundednessLeafRequired : Bool
separateLiteralLoopBoundednessLeafRequired = false

separateLiteralLoopBoundednessLeafRequiredIsFalse :
  separateLiteralLoopBoundednessLeafRequired ≡ false
separateLiteralLoopBoundednessLeafRequiredIsFalse = refl

separateBoundedMultiplicationClosureLeafRequired : Bool
separateBoundedMultiplicationClosureLeafRequired = false

separateBoundedMultiplicationClosureLeafRequiredIsFalse :
  separateBoundedMultiplicationClosureLeafRequired ≡ false
separateBoundedMultiplicationClosureLeafRequiredIsFalse = refl

separateIdentityBoundednessLeafRequired : Bool
separateIdentityBoundednessLeafRequired = false

separateIdentityBoundednessLeafRequiredIsFalse :
  separateIdentityBoundednessLeafRequired ≡ false
separateIdentityBoundednessLeafRequiredIsFalse = refl

singleQuantitativeBoundPredicateAttachmentStillPhysical : Bool
singleQuantitativeBoundPredicateAttachmentStillPhysical = true

singleQuantitativeBoundPredicateAttachmentStillPhysicalIsTrue :
  singleQuantitativeBoundPredicateAttachmentStillPhysical ≡ true
singleQuantitativeBoundPredicateAttachmentStillPhysicalIsTrue = refl

pointwiseMultiplyToT5MultiplySameObjectStillPhysical : Bool
pointwiseMultiplyToT5MultiplySameObjectStillPhysical = true

pointwiseMultiplyToT5MultiplySameObjectStillPhysicalIsTrue :
  pointwiseMultiplyToT5MultiplySameObjectStillPhysical ≡ true
pointwiseMultiplyToT5MultiplySameObjectStillPhysicalIsTrue = refl

supportDistanceTimeStillPhysical : Bool
supportDistanceTimeStillPhysical = true

supportDistanceTimeStillPhysicalIsTrue :
  supportDistanceTimeStillPhysical ≡ true
supportDistanceTimeStillPhysicalIsTrue = refl

quantitativeWilsonFiniteProductBoundLevel : ProofLevel
quantitativeWilsonFiniteProductBoundLevel =
  Bounds.literalRationalSU2WilsonCylinderBoundDataLevel

quantitativeBoundAttachmentCompilerLevel : ProofLevel
quantitativeBoundAttachmentCompilerLevel = machineChecked

quantitativeBoundPredicateAttachmentLevel : ProofLevel
quantitativeBoundPredicateAttachmentLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
