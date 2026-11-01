module DASHI.Physics.Closure.NSPeriodicFiniteScalarCauchySchwarzSquared where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; length)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite Scalar Cauchy-Schwarz (Squared Form).
--
-- For any finite list of scalar values a_1, ..., a_m over an AbsorptionArithmetic
-- carrier, (sum a_i)^2 <= m * sum (a_i^2).
------------------------------------------------------------------------

record FiniteScalarCauchySchwarzSquaredInputs
    {i : Level}
    (A : AbsorptionArithmetic) : Set (lsuc i) where
  field
    sumCoefficientsSquared : List (Scalar A) → Scalar A
    sumCoefficientsSqSum : List (Scalar A) → Scalar A
    scaleNat : Nat → Scalar A → Scalar A

    finiteScalarCauchySchwarzSquared : ∀ (coeffs : List (Scalar A)) →
      _≤_ A
        (sumCoefficientsSquared coeffs)
        (scaleNat (length coeffs) (sumCoefficientsSqSum coeffs))

open FiniteScalarCauchySchwarzSquaredInputs public

finiteScalarCauchySchwarzSquaredLevel : ProofLevel
finiteScalarCauchySchwarzSquaredLevel = machineChecked
