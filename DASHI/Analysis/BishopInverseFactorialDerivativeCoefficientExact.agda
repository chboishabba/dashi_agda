module DASHI.Analysis.BishopInverseFactorialDerivativeCoefficientExact where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Reciprocal

------------------------------------------------------------------------
-- EXACT DERIVATIVE COEFFICIENT CANCELLATION
--
--   (n+1) * 1/(n+1)!  ~=  1/n!
--
-- on the literal Bishop real carrier.  The proof reuses:
--   * the exact recursive/embedded natural-scale bridge;
--   * inverseFactorial(n+1) = (1/(n+1)) inverseFactorial(n);
--   * embedded (1/(n+1)) * embedded (n+1) = 1.
------------------------------------------------------------------------

scaledInverseFactorialSuccessor :
  ∀ n →
  Bishop._≃_
    (Power.natScale
      (suc n)
      (Exp.embed (Exp.inverseFactorial (suc n))))
    (Exp.embed (Exp.inverseFactorial n))
scaledInverseFactorialSuccessor n =
  let
    natural = NatReal.natReal (suc n)
    reciprocal = Exp.embed (+ 1 / suc n)
    oldCoefficient = Exp.embed (Exp.inverseFactorial n)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (Scale.recursiveScaleIsEmbeddedNaturalMultiply
      (suc n)
      (Exp.embed (Exp.inverseFactorial (suc n))))
    (BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        (Exp.embeddedInverseFactorialSuccessor n))
      (BishopP.≃-trans
        (solve 3
          (λ natural′ reciprocal′ old′ →
            natural′ ⊗ (reciprocal′ ⊗ old′)
            ⊜ (reciprocal′ ⊗ natural′) ⊗ old′)
          BishopP.≃-refl
          natural reciprocal oldCoefficient)
        (BishopP.≃-trans
          (BishopP.*-cong
            (Reciprocal.embeddedReciprocalNatCancels n)
            BishopP.≃-refl)
          (BishopP.*-identityˡ oldCoefficient))))
