module DASHI.Physics.Closure.NSTriadKNFixedShiftPhysicalCapacityLeafRound58 where

------------------------------------------------------------------------
-- Lightweight C-leaf.
--
-- The owner/flux and capacity statements are expressed over their literal
-- Nat-indexed rational observables.  Concrete nine-owner and Luo fixed-shift
-- records can be connected by an adapter, without making this analytic leaf
-- import the complete consumer graph.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

record PhysicalOwnerFluxBlockIdentification : Set₁ where
  field
    ownerRemainder integratedFluxCorrection blockCorrection : Nat → ℚ
    blockShiftCoefficient correctedShiftCoefficient : ℚ

    ownerToFlux : ∀ n → ownerRemainder n ≡ integratedFluxCorrection n
    physicalFluxCorrectionIsBlockCorrection :
      ∀ n → integratedFluxCorrection n ≡ blockCorrection n
    blockShiftCoefficientIsPhysical :
      blockShiftCoefficient ≡ correctedShiftCoefficient

open PhysicalOwnerFluxBlockIdentification public

ownerRemainderIsBlockCorrection :
  (identification : PhysicalOwnerFluxBlockIdentification) →
  ∀ n → ownerRemainder identification n ≡ blockCorrection identification n
ownerRemainderIsBlockCorrection identification n =
  trans
    (ownerToFlux identification n)
    (physicalFluxCorrectionIsBlockCorrection identification n)

correctionHeadroomAfterData :
  (correctionHeadroom dataRemainder : Nat → ℚ) → Nat → ℚ
correctionHeadroomAfterData correctionHeadroom dataRemainder n =
  correctionHeadroom n - dataRemainder n

record UniformFixedShiftProductCapacity
    (integralCritical correctionHeadroom dataRemainder : Nat → ℚ) : Set₁ where
  field
    uniformCoefficient : ℚ
    uniformCoefficientPositive : 0ℚ < uniformCoefficient
    criticalIntegralNonnegative : ∀ n → 0ℚ ≤ integralCritical n
    uniformProductFitsEveryBlock : ∀ n →
      uniformCoefficient * integralCritical n
      ≤ correctionHeadroomAfterData correctionHeadroom dataRemainder n

open UniformFixedShiftProductCapacity public

-- The positive uniform coefficient is still an analytic input.  In
-- particular, same-object transport does not manufacture it from the block
-- formula.  This explicit status is consumed by audit tooling and remains
-- false until one rational B_* is derived uniformly in n.
uniformPositiveCapacityDerived :
  {integralCritical correctionHeadroom dataRemainder : Nat → ℚ} → Bool
uniformPositiveCapacityDerived = false

uniformPositiveCapacityDerivedIsFalse :
  {integralCritical correctionHeadroom dataRemainder : Nat → ℚ} →
  uniformPositiveCapacityDerived {integralCritical = integralCritical}
    {correctionHeadroom = correctionHeadroom}
    {dataRemainder = dataRemainder} ≡ false
uniformPositiveCapacityDerivedIsFalse = refl

smallerNonnegativeCoefficientFitsEveryBlock :
  ∀ {integralCritical correctionHeadroom dataRemainder}
    {capacity : UniformFixedShiftProductCapacity
      integralCritical correctionHeadroom dataRemainder} →
  (coefficient : ℚ) →
  0ℚ ≤ coefficient →
  coefficient ≤ uniformCoefficient capacity →
  ∀ n →
  coefficient * integralCritical n
  ≤ correctionHeadroomAfterData correctionHeadroom dataRemainder n
smallerNonnegativeCoefficientFitsEveryBlock
    {integralCritical = integralCritical}
    {correctionHeadroom = correctionHeadroom}
    {dataRemainder = dataRemainder}
    {capacity = capacity} coefficient coefficientNN coefficientBelow n =
  let
    critical = integralCritical _
    scaled :
      coefficient * critical
      ≤ uniformCoefficient capacity * critical
    scaled =
      let instance criticalNN = nonNegative (criticalIntegralNonnegative capacity n)
      in ℚP.*-monoʳ-≤-nonNeg critical coefficientBelow
  in
  ℚP.≤-trans scaled (uniformProductFitsEveryBlock capacity n)
