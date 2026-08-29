{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUniformPotentialToFirstVariationConvergenceRound108Exact where

------------------------------------------------------------------------
-- ROUND108: NORMALIZED CAUCHY TRANSFER
--
-- CMP116 already supplies the source fact that finite derivatives are obtained
-- by Cauchy formula on a common analytic domain.  After absorbing the fixed
-- inverse-radius factor into a normalized potential error, the derivative error
-- is bounded by that potential error.  Therefore any explicit convergence
-- modulus for the potentials is automatically a convergence modulus for the
-- first variations.
--
-- This does NOT prove uniform convergence of the Balaban effective potentials,
-- nor the literal Cauchy estimate on the physical family.  It removes the
-- duplicate downstream task "prove derivative convergence separately".
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record NormalizedCauchyDerivativeConvergence : Set where
  field
    potentialError : Nat → ℚ
    firstVariationError : Nat → ℚ

    potentialErrorNonnegative : ∀ n → 0ℚ ≤ potentialError n
    firstVariationErrorNonnegative : ∀ n → 0ℚ ≤ firstVariationError n

    -- The physical Cauchy estimate after normalising by the common radius.
    firstVariationErrorBelowPotentialError : ∀ n →
      firstVariationError n ≤ potentialError n

    -- Explicit modulus of uniform potential convergence.
    potentialConvergenceModulus : ℚ → Nat
    potentialEventuallyBelow : ∀ tolerance →
      0ℚ < tolerance →
      ∀ n → potentialConvergenceModulus tolerance ≤ n →
      potentialError n < tolerance

open NormalizedCauchyDerivativeConvergence public

firstVariationConvergenceModulus :
  NormalizedCauchyDerivativeConvergence → ℚ → Nat
firstVariationConvergenceModulus dataSet = potentialConvergenceModulus dataSet

firstVariationEventuallyBelow :
  (dataSet : NormalizedCauchyDerivativeConvergence) →
  ∀ tolerance →
  0ℚ < tolerance →
  ∀ n → firstVariationConvergenceModulus dataSet tolerance ≤ n →
  firstVariationError dataSet n < tolerance
firstVariationEventuallyBelow dataSet tolerance tolerancePositive n modulusReached =
  ℚP.≤-<-trans
    (firstVariationErrorBelowPotentialError dataSet n)
    (potentialEventuallyBelow dataSet tolerance tolerancePositive n modulusReached)

record Round108Boundary : Set where
  constructor round108Boundary
  field
    differentiatedLocalizationAloneProvesPotentialConvergence : Bool
    differentiatedLocalizationAloneProvesPotentialConvergenceIsFalse :
      differentiatedLocalizationAloneProvesPotentialConvergence ≡ false

    potentialConvergenceAloneProvesDerivativeConvergenceWithoutCauchyControl : Bool
    potentialConvergenceAloneProvesDerivativeConvergenceWithoutCauchyControlIsFalse :
      potentialConvergenceAloneProvesDerivativeConvergenceWithoutCauchyControl ≡ false

    normalizedCauchyBoundTransfersPotentialModulusToFirstVariation : Bool
    normalizedCauchyBoundTransfersPotentialModulusToFirstVariationIsTrue :
      normalizedCauchyBoundTransfersPotentialModulusToFirstVariation ≡ true

canonicalRound108Boundary : Round108Boundary
canonicalRound108Boundary =
  round108Boundary false refl false refl true refl

normalizedCauchyDerivativeConvergenceCompilerLevel : ProofLevel
normalizedCauchyDerivativeConvergenceCompilerLevel = machineChecked

literalBalabanUniformPotentialConvergenceLevel : ProofLevel
literalBalabanUniformPotentialConvergenceLevel = conditional

literalBalabanNormalizedCauchyFirstVariationBoundLevel : ProofLevel
literalBalabanNormalizedCauchyFirstVariationBoundLevel = conditional
