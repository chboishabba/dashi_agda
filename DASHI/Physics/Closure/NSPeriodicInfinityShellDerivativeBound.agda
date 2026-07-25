module DASHI.Physics.Closure.NSPeriodicInfinityShellDerivativeBound where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Direct derivative reduction on |k|_infinity <= 2^n.
--
-- The elementary modewise fact is |k|_2^2 <= 3 * 2^(2n).  The record keeps
-- that finite Fourier-sum theorem separate from Parseval and from the final
-- square-root presentation, so the factor sqrt(3) is not silently imported.
------------------------------------------------------------------------

record InfinityShellDerivativeInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (State : Set i) : Set (lsuc i) where
  field
    ShellSupported : Nat → State → Set i

    coefficientL2 gradientL2 : Nat → State → Scalar A
    cubeDerivativeMajorant : Nat → State → Scalar A

    dyadicDerivativeFactor : Nat → Scalar A
    scale : Scalar A → Scalar A → Scalar A

    finiteCubeDerivativeEstimate : ∀ n state →
      ShellSupported n state →
      _≤_ A
        (gradientL2 n state)
        (cubeDerivativeMajorant n state)

    cubeDerivativeMajorantMeaning : ∀ n state →
      cubeDerivativeMajorant n state
      ≡ scale (dyadicDerivativeFactor n) (coefficientL2 n state)

open InfinityShellDerivativeInputs public

infinityShellDerivativeBound :
  ∀ {i} {A : AbsorptionArithmetic} {State : Set i} →
  (I : InfinityShellDerivativeInputs A State) →
  ∀ n state → ShellSupported I n state →
  _≤_ A
    (gradientL2 I n state)
    (scale I (dyadicDerivativeFactor I n) (coefficientL2 I n state))
infinityShellDerivativeBound {A = A} I n state supported =
  subst
    (λ upper → _≤_ A (gradientL2 I n state) upper)
    (cubeDerivativeMajorantMeaning I n state)
    (finiteCubeDerivativeEstimate I n state supported)

infinityShellDerivativeReductionLevel : ProofLevel
infinityShellDerivativeReductionLevel = machineChecked

literalCubeModewiseDerivativeEstimateLevel : ProofLevel
literalCubeModewiseDerivativeEstimateLevel = conditional

sqrtThreeDyadicDerivativeFactorLevel : ProofLevel
sqrtThreeDyadicDerivativeFactorLevel = conditional
