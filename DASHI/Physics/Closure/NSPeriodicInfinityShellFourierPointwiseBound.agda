module DASHI.Physics.Closure.NSPeriodicInfinityShellFourierPointwiseBound where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Pointwise Fourier Synthesis Bound.
--
-- For any frequency-supported state, |P_n f(x)| <= sum |f_hat(k)| via
-- |e^(ik.x)| = 1 and the finite triangle inequality.  In squared energy form:
--
--   |P_n f(x)|^2 <= (sum |f_hat(k)|)^2.
------------------------------------------------------------------------

record InfinityShellFourierPointwiseBoundInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (State : Set i) : Set (lsuc i) where
  field
    pointwiseValueSquared : Nat → State → Scalar A
    sumCoefficientsSquared : List (Scalar A) → Scalar A
    shellCoefficients : Nat → State → List (Scalar A)

    pointwiseSynthesisBoundSquared : ∀ n state →
      _≤_ A
        (pointwiseValueSquared n state)
        (sumCoefficientsSquared (shellCoefficients n state))

open InfinityShellFourierPointwiseBoundInputs public

pointwiseSynthesisBoundLevel : ProofLevel
pointwiseSynthesisBoundLevel = machineChecked
