module DASHI.Physics.Closure.NSPeriodicInfinityShellCoefficientBernsteinSquared where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.List.Base using (List; length)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount as Count
open import DASHI.Physics.Closure.NSPeriodicFiniteScalarCauchySchwarzSquared
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Dyadic Coefficient Bernstein (Squared Form).
--
-- Combines finite scalar Cauchy-Schwarz (sum a_k)^2 <= |S_n| sum (a_k^2)
-- with the literal cube cardinality majorant |S_n| <= 27 * 2^(3n) to obtain:
--
--   (sum a_k)^2 <= 27 * 2^(3n) * sum (a_k^2).
------------------------------------------------------------------------

record InfinityShellCoefficientBernsteinSquaredInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (State : Set i) : Set (lsuc i) where
  field
    shellCoefficients : Nat → State → List (Scalar A)
    sumCoefficientsSquared : List (Scalar A) → Scalar A
    sumCoefficientsSqSum : List (Scalar A) → Scalar A
    scaleNat : Nat → Scalar A → Scalar A

    finiteCS : ∀ (coeffs : List (Scalar A)) →
      _≤_ A
        (sumCoefficientsSquared coeffs)
        (scaleNat (length coeffs) (sumCoefficientsSqSum coeffs))

    shellCoefficientsLengthBound : ∀ n state →
      length (shellCoefficients n state) Cube.≤ᴺ Count.infinityCubeModeCount n

    scaleNatMonotoneLength : ∀ {m n : Nat} (s : Scalar A) →
      m Cube.≤ᴺ n →
      _≤_ A (scaleNat m s) (scaleNat n s)

open InfinityShellCoefficientBernsteinSquaredInputs public

infinityShellCoefficientBernsteinSquared :
  ∀ {i} {A : AbsorptionArithmetic} {State : Set i} →
  (I : InfinityShellCoefficientBernsteinSquaredInputs A State) →
  ∀ n state →
  _≤_ A
    (sumCoefficientsSquared I (shellCoefficients I n state))
    (scaleNat I
      (27 * (Count.pow2 n * (Count.pow2 n * Count.pow2 n)))
      (sumCoefficientsSqSum I (shellCoefficients I n state)))
infinityShellCoefficientBernsteinSquared {A = A} I n state =
  ≤-trans A
    (finiteCS I (shellCoefficients I n state))
    (scaleNatMonotoneLength I
      (sumCoefficientsSqSum I (shellCoefficients I n state))
      (Cube.≤ᴺ-trans
        (shellCoefficientsLengthBound I n state)
        (Count.coarseTwentySevenTimesDyadicCubeBound n)))

coefficientBernsteinSquaredLevel : ProofLevel
coefficientBernsteinSquaredLevel = machineChecked
