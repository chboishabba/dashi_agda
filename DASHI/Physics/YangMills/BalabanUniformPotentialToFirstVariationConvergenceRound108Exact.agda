{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUniformPotentialToFirstVariationConvergenceRound108Exact where

------------------------------------------------------------------------
-- ROUND108: NORMALIZED CAUCHY TRANSFER
--
-- CMP116 Sect.1 supplies differentiated localization through Cauchy formula on
-- a common analytic domain.  Round104 supplies a canonical positive common
-- radius from the finite normalized CMP116 demands.  After absorbing the fixed
-- inverse-radius Cauchy cost into a normalized potential error, the derivative
-- error is bounded by that potential error.  Hence the same convergence modulus
-- transfers mechanically from potentials to first variations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon

record NormalizedCauchyDerivativeConvergence : Set where
  field
    potentialError : Nat → ℚ
    firstVariationError : Nat → ℚ

    potentialErrorNonnegative : ∀ n → 0ℚ ≤ potentialError n
    firstVariationErrorNonnegative : ∀ n → 0ℚ ≤ firstVariationError n

    firstVariationErrorBelowPotentialError : ∀ n →
      firstVariationError n ≤ potentialError n

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

    canonicalPositiveRadiusAloneProvesPotentialConvergence : Bool
    canonicalPositiveRadiusAloneProvesPotentialConvergenceIsFalse :
      canonicalPositiveRadiusAloneProvesPotentialConvergence ≡ false

    potentialConvergenceAloneProvesDerivativeConvergenceWithoutCauchyControl : Bool
    potentialConvergenceAloneProvesDerivativeConvergenceWithoutCauchyControlIsFalse :
      potentialConvergenceAloneProvesDerivativeConvergenceWithoutCauchyControl ≡ false

    normalizedCauchyBoundTransfersPotentialModulusToFirstVariation : Bool
    normalizedCauchyBoundTransfersPotentialModulusToFirstVariationIsTrue :
      normalizedCauchyBoundTransfersPotentialModulusToFirstVariation ≡ true

canonicalRound108Boundary : Round108Boundary
canonicalRound108Boundary =
  round108Boundary false refl false refl false refl true refl

-- Provenance: differentiated localization/Cauchy control is source-owned; the
-- canonical-radius arithmetic is already machine checked.  What remains is the
-- literal binding of the potential-error sequence to the physical Balaban
-- continuum family and its uniform convergence modulus.
cmp116DifferentiatedLocalizationSourceLevel : ProofLevel
cmp116DifferentiatedLocalizationSourceLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

cmp116CanonicalCommonRadiusCompilerRound108Level : ProofLevel
cmp116CanonicalCommonRadiusCompilerRound108Level =
  Canon.cmp116CanonicalCommonRadiusCompilerLevel

normalizedCauchyDerivativeConvergenceCompilerLevel : ProofLevel
normalizedCauchyDerivativeConvergenceCompilerLevel = machineChecked

literalBalabanUniformPotentialConvergenceLevel : ProofLevel
literalBalabanUniformPotentialConvergenceLevel = conditional

literalBalabanNormalizedCauchyFirstVariationBoundLevel : ProofLevel
literalBalabanNormalizedCauchyFirstVariationBoundLevel = conditional
