module DASHI.Mathematics.NumberTheory.FinitePositiveScaledReciprocalExact where

------------------------------------------------------------------------
-- POSITIVE SCALE / RECIPROCAL ARITHMETIC
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Nat.Base using (NonZero)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; _+_; _*_; _≤_; _≃_; *≤*; *≡*)

open import DASHI.Physics.YangMills.CompactLieProofLevel

productPrecision : Nat → Nat → Nat
productPrecision scale precision = 2 * scale * precision

scaleRational : Nat → ℚᵘ
scaleRational scale = + scale / 1

productPrecisionReciprocal :
  (scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  ℚᵘ
productPrecisionReciprocal scale precision =
  + 1 / productPrecision scale precision

doubleScaledReciprocalEquivalent :
  (scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  ((scaleRational scale ℚ.* productPrecisionReciprocal scale precision)
    ℚ.+
   (scaleRational scale ℚ.* productPrecisionReciprocal scale precision))
  ℚ.≃
  (+ 1 / precision)
doubleScaledReciprocalEquivalent scale precision =
  ℚ.*≡*
    (solve 2
      (λ s n →
        (((s :* (con (+ 2) :* s :* n))
          :+ (s :* (con (+ 2) :* s :* n))) :* n)
        :=
        (con (+ 1) :*
          ((con (+ 2) :* s :* n) :* (con (+ 2) :* s :* n))))
      refl
      (+ scale)
      (+ precision))

oneOverPlusOneOverEquivalentTwoOver :
  (precision : Nat) → .{{_ : NonZero precision}} →
  ((+ 1 / precision) ℚ.+ (+ 1 / precision))
  ℚ.≃
  (+ 2 / precision)
oneOverPlusOneOverEquivalentTwoOver precision =
  ℚ.*≡*
    (solve 1
      (λ n →
        ((con (+ 1) :* n :+ con (+ 1) :* n) :* n)
        :=
        (con (+ 2) :* (n :* n)))
      refl
      (+ precision))

precisionBelowProductPrecision :
  (scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  precision ≤ productPrecision scale precision
precisionBelowProductPrecision scale precision =
  NatP.m≤n*m precision (2 * scale)

precisionBelowProductPrecisionSquare :
  (scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  precision ≤
    productPrecision scale precision * productPrecision scale precision
precisionBelowProductPrecisionSquare scale precision =
  NatP.≤-trans
    (precisionBelowProductPrecision scale precision)
    (NatP.m≤m*n
      (productPrecision scale precision)
      (productPrecision scale precision))

reciprocalSquareBelowOneOverPrecision :
  (scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  (productPrecisionReciprocal scale precision
    ℚ.* productPrecisionReciprocal scale precision)
  ℚ.≤ (+ 1 / precision)
reciprocalSquareBelowOneOverPrecision scale precision =
  ℚ.*≤*
    (ℤ.+≤+
      (precisionBelowProductPrecisionSquare scale precision))

positiveScaledReciprocalLevel : ProofLevel
positiveScaledReciprocalLevel = machineChecked
