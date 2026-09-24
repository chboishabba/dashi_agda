module DASHI.Physics.Closure.NSWholeSpaceR3RadialFactorBudgetExact where

------------------------------------------------------------------------
-- A / MEASURE-AWARE LOW-FREQUENCY FACTOR BUDGET
--
-- The pointwise heat-cube route asks the complete state factor to supply
-- a^3 ~ |xi|^6.  On R^3 that is stronger than the Lebesgue integral needs.
--
-- Write
--
--   q = |xi|^2 > 0,      a = nu q.
--
-- Radial Lebesgue measure contributes q.  The divergence-form nonlinear Gram
-- is already quadratic in the output frequency, so its physical majorant is
-- expected to contribute one further q.  Therefore if the remaining signed
-- second-moment factor contributes only one q,
--
--   gramFactor         <= q * G,
--   secondMomentFactor <= q * Q,
--
-- then
--
--   gramFactor * secondMomentFactor <= q^2 * (G * Q),
--
-- and the radial density closes the complete inverse-cube singularity:
--
--   q * a^{-3} * (gramFactor * secondMomentFactor)
--      <= nu^{-3} * (G * Q).
--
-- This owner proves that reduction on the canonical Bishop-real carrier.  It
-- does NOT manufacture the remaining physical second-moment q-gain or the
-- radial/Fubini same-object weld.  It removes the obsolete requirement that
-- the residual lane itself supply |xi|^4 after the raw Gram q-factor is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low
import DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact as Radial

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

record R3RadialFactorBudget
    (dataSet : Radial.PositiveViscosityRadiusSquare)
    (gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant : BishopReal.ℝ) : Set where
  constructor r3-radial-factor-budget
  field
    gramFactorNonnegative :
      BishopReal.NonNegative gramFactor

    secondMomentFactorNonnegative :
      BishopReal.NonNegative secondMomentFactor

    gramMajorantNonnegative :
      BishopReal.NonNegative gramMajorant

    secondMomentMajorantNonnegative :
      BishopReal.NonNegative secondMomentMajorant

    gramCarriesRadiusSquare :
      BishopReal._≤_
        gramFactor
        (BishopReal._*_
          (Radial.radiusSquared dataSet)
          gramMajorant)

    secondMomentCarriesRadiusSquare :
      BishopReal._≤_
        secondMomentFactor
        (BishopReal._*_
          (Radial.radiusSquared dataSet)
          secondMomentMajorant)

open R3RadialFactorBudget public

radiusSquareNonnegative :
  (dataSet : Radial.PositiveViscosityRadiusSquare) →
  BishopReal.NonNegative (Radial.radiusSquared dataSet)
radiusSquareNonnegative dataSet =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx (Radial.radiusSquaredPositive dataSet))

factorProductBelowRawRadiusFourth :
  ∀ {dataSet gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant} →
  (budget :
    R3RadialFactorBudget
      dataSet
      gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant) →
  BishopReal._≤_
    (BishopReal._*_ gramFactor secondMomentFactor)
    (BishopReal._*_
      (BishopReal._*_
        (Radial.radiusSquared dataSet)
        gramMajorant)
      (BishopReal._*_
        (Radial.radiusSquared dataSet)
        secondMomentMajorant))
factorProductBelowRawRadiusFourth budget =
  BishopP.*-mono-≤
    (gramFactorNonnegative budget)
    (secondMomentFactorNonnegative budget)
    (gramCarriesRadiusSquare budget)
    (secondMomentCarriesRadiusSquare budget)

rawRadiusFourthIsSquareTimesMajorants :
  (q gramMajorant secondMomentMajorant : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_ q gramMajorant)
      (BishopReal._*_ q secondMomentMajorant))
    (BishopReal._*_
      (square q)
      (BishopReal._*_ gramMajorant secondMomentMajorant))
rawRadiusFourthIsSquareTimesMajorants
    q gramMajorant secondMomentMajorant =
  let open BishopP.ℝ-Solver
  in
  solve 3
    (λ q' g s →
      (q' ⊗ g) ⊗ (q' ⊗ s)
      ⊜
      (q' ⊗ q') ⊗ (g ⊗ s))
    BishopP.≃-refl
    q gramMajorant secondMomentMajorant

factorProductCarriesRadiusFourth :
  ∀ {dataSet gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant} →
  (budget :
    R3RadialFactorBudget
      dataSet
      gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant) →
  BishopReal._≤_
    (BishopReal._*_ gramFactor secondMomentFactor)
    (BishopReal._*_
      (square (Radial.radiusSquared dataSet))
      (BishopReal._*_ gramMajorant secondMomentMajorant))
factorProductCarriesRadiusFourth
    {dataSet} {gramMajorant = gramMajorant}
    {secondMomentMajorant = secondMomentMajorant}
    budget =
  BishopP.≤-respʳ-≃
    (rawRadiusFourthIsSquareTimesMajorants
      (Radial.radiusSquared dataSet)
      gramMajorant
      secondMomentMajorant)
    (factorProductBelowRawRadiusFourth budget)

inverseHeatCubeNonnegative :
  (dataSet : Radial.PositiveViscosityRadiusSquare) →
  BishopReal.NonNegative
    (Radial.inverseCube
      (Radial.heatRate dataSet)
      (Radial.heatRateNonzero dataSet))
inverseHeatCubeNonnegative dataSet =
  Low.inverseCubeNonnegative (Radial.heatRatePositive dataSet)

radialInverseCubeFactorPayment :
  ∀ {dataSet gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant} →
  (budget :
    R3RadialFactorBudget
      dataSet
      gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant) →
  BishopReal._≤_
    (BishopReal._*_
      (Radial.radiusSquared dataSet)
      (BishopReal._*_
        (Radial.inverseCube
          (Radial.heatRate dataSet)
          (Radial.heatRateNonzero dataSet))
        (BishopReal._*_ gramFactor secondMomentFactor)))
    (BishopReal._*_
      (Radial.inverseCube
        (Radial.viscosity dataSet)
        (Radial.viscosityNonzero dataSet))
      (BishopReal._*_ gramMajorant secondMomentMajorant))
radialInverseCubeFactorPayment
    {dataSet} {gramMajorant = gramMajorant}
    {secondMomentMajorant = secondMomentMajorant}
    budget =
  let
    invA =
      Radial.inverseCube
        (Radial.heatRate dataSet)
        (Radial.heatRateNonzero dataSet)

    inner :
      BishopReal._≤_
        (BishopReal._*_
          invA
          (BishopReal._*_ gramFactor secondMomentFactor))
        (BishopReal._*_
          invA
          (BishopReal._*_
            (square (Radial.radiusSquared dataSet))
            (BishopReal._*_ gramMajorant secondMomentMajorant)))
    inner =
      BishopP.*-monoˡ-≤-nonNeg
        (factorProductCarriesRadiusFourth budget)
        (inverseHeatCubeNonnegative dataSet)

    radialScaled :
      BishopReal._≤_
        (BishopReal._*_
          (Radial.radiusSquared dataSet)
          (BishopReal._*_
            invA
            (BishopReal._*_ gramFactor secondMomentFactor)))
        (BishopReal._*_
          (Radial.radiusSquared dataSet)
          (BishopReal._*_
            invA
            (BishopReal._*_
              (square (Radial.radiusSquared dataSet))
              (BishopReal._*_ gramMajorant secondMomentMajorant))))
    radialScaled =
      BishopP.*-monoˡ-≤-nonNeg
        inner
        (radiusSquareNonnegative dataSet)
  in
  BishopP.≤-respʳ-≃
    (Radial.radiusDensityCancelsInverseCubeAgainstFourthOrder
      dataSet
      (BishopReal._*_ gramMajorant secondMomentMajorant))
    radialScaled

------------------------------------------------------------------------
-- Frontier reduction.
--
-- Existing whole-space owners already prove the raw divergence-form Gram is
-- quadratic in xi.  Once that exact scaling is converted into the required
-- nonnegative q-majorant on the projected physical cell, this theorem leaves
-- only
--
--   secondMomentFactor <= |xi|^2 * Q
--
-- as the frequency-gain obligation before radial integration.
------------------------------------------------------------------------

measureAwareTwoFactorCompilerClosed : Bool
measureAwareTwoFactorCompilerClosed = true

rawGramExpectedRadiusSquareFactors : BishopReal.ℝ
rawGramExpectedRadiusSquareFactors = BishopReal.1ℝ

remainingSecondMomentRadiusSquareFactors : BishopReal.ℝ
remainingSecondMomentRadiusSquareFactors = BishopReal.1ℝ

residualMustSupplyRadiusFourthAfterGram : Bool
residualMustSupplyRadiusFourthAfterGram = false

physicalSecondMomentRadiusSquareProducerClosedHere : Bool
physicalSecondMomentRadiusSquareProducerClosedHere = false

projectedGramMajorantClosedHere : Bool
projectedGramMajorantClosedHere = false

radialLebesgueSameObjectWeldClosedHere : Bool
radialLebesgueSameObjectWeldClosedHere = false

clayPromotion : Bool
clayPromotion = false

measureAwareTwoFactorCompilerClosedIsTrue :
  measureAwareTwoFactorCompilerClosed ≡ true
measureAwareTwoFactorCompilerClosedIsTrue = refl

residualMustSupplyRadiusFourthAfterGramIsFalse :
  residualMustSupplyRadiusFourthAfterGram ≡ false
residualMustSupplyRadiusFourthAfterGramIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
