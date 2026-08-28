module DASHI.Foundations.BishopBaselMachinSineQuadraticCoefficientExact where

------------------------------------------------------------------------
-- MACHIN-pi SINE-SERIES QUADRATIC COEFFICIENT
--
-- The cubic sine polynomial at y = pi_M * x factors exactly as
--
--   pi_M*x - (pi_M*x)^3/6
--     = pi_M*x * (1 - (pi_M^2/6) * x^2).
--
-- Thus the quadratic coefficient of the normalized sine series is literally
--
--   - pi_M^2 / 6.
--
-- This is finite ring algebra only.  No Euler sine product or Basel value is
-- asserted here.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
open import DASHI.Physics.YangMills.CompactLieProofLevel

machinPi : BishopReal.ℝ
machinPi = Atan.bishopMachinPi

oneSixth : BishopReal.ℝ
oneSixth = Exp.embed (+ 1 / 6)

square cube : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
cube value = BishopReal._*_ (square value) value

normalizedSineQuadraticCoefficient : BishopReal.ℝ
normalizedSineQuadraticCoefficient =
  BishopReal.-
    (BishopReal._*_ oneSixth (square machinPi))

sineCubicAtMachinPiX : BishopReal.ℝ → BishopReal.ℝ
sineCubicAtMachinPiX x =
  let y = BishopReal._*_ machinPi x
  in BishopReal._-_ y (BishopReal._*_ oneSixth (cube y))

normalizedSineCubicFactor : BishopReal.ℝ → BishopReal.ℝ
normalizedSineCubicFactor x =
  BishopReal._+_
    BishopReal.1ℝ
    (BishopReal._*_
      normalizedSineQuadraticCoefficient
      (square x))

sineCubicMachinFactorization :
  ∀ x →
  BishopReal._≃_
    (sineCubicAtMachinPiX x)
    (BishopReal._*_
      (BishopReal._*_ machinPi x)
      (normalizedSineCubicFactor x))
sineCubicMachinFactorization x =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ p x′ →
      (p ⊗ x′)
        ⊖ (Κ (+ 1 / 6) ⊗ (((p ⊗ x′) ⊗ (p ⊗ x′)) ⊗ (p ⊗ x′)))
      ⊜ (p ⊗ x′) ⊗
          (Κ 1ℚᵘ
            ⊕ ((⊝ (Κ (+ 1 / 6) ⊗ (p ⊗ p)))
                ⊗ (x′ ⊗ x′))))
    BishopP.≃-refl
    machinPi x

normalizedSineQuadraticCoefficientIsMinusPiSquareOverSix :
  BishopReal._≃_
    normalizedSineQuadraticCoefficient
    (BishopReal.-
      (BishopReal._*_
        (Exp.embed (+ 1 / 6))
        (BishopReal._*_ machinPi machinPi)))
normalizedSineQuadraticCoefficientIsMinusPiSquareOverSix =
  BishopP.≃-refl

bishopBaselMachinSineQuadraticCoefficientLevel : ProofLevel
bishopBaselMachinSineQuadraticCoefficientLevel = machineChecked
