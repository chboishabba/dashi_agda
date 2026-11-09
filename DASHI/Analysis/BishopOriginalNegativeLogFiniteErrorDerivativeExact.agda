module DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact where

------------------------------------------------------------------------
-- K04d P0: genuine ORIGINAL target-error derivative.
--
-- E_N(x) = exp_B(-L_N(x)) - (1-x).
--
-- Source factorization, not a new derivative notion:
--   E_N(x+h)-E_N(x) ~= h (q_F(N,x,h)+1).
--
-- Its quotient converges on every original Bishop null sequence to
--   F_N'(x)+1 = 1 - F_N(x) P_N(x).
--
-- Crucially the same q_F+1 is the quotient defect appearing in the
-- previously proved mesh endpoint identity. This eliminates a
-- representation gap between the derivative and mesh work.
--
-- The exact ODE error identity follows:
--   (1-x)E_N'(x) + E_N(x) ~= x^N F_N(x).
--
-- No extra boundedness or FTC hypothesis is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpDerivativeResidualExact as Residual
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpInitialValueExact as Initial
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo

originalFiniteLogExpError : Nat → R.ℝ → R.ℝ
originalFiniteLogExpError n x =
  R._-_
    (Finite.originalNegativeLogFiniteExponential x n)
    (R._-_ R.1ℝ x)

originalFiniteLogExpErrorSlope : Nat → R.ℝ → R.ℝ
originalFiniteLogExpErrorSlope n x =
  R._+_
    (R._*_
      (Finite.originalNegativeLogFiniteExponential x n)
      (R.-_ (Geo.negativeLogDerivativePolynomial x n)))
    R.1ℝ

-- A division-free source receipt with the exact error quotient
-- already used by BishopOriginalNegativeLogFiniteExpMeshEndpointExact.
originalFiniteLogExpErrorDerivative :
  (n : Nat) (x : R.ℝ) →
  Factor.BishopFactorDerivativeAt
    (originalFiniteLogExpError n)
    x
    (originalFiniteLogExpErrorSlope n x)
originalFiniteLogExpErrorDerivative n x =
  let
    D = Residual.originalFiniteNegativeLogExpDerivative x n
    p = Geo.negativeLogDerivativePolynomial x n
    f = Finite.originalNegativeLogFiniteExponential x n
    slope = R._*_ f (R.-_ p)
    open RP.ℝ-Solver
  in
  record
    { Factor.quotient = λ h →
        R._+_ (Factor.quotient D h) R.1ℝ
    ; Factor.incrementFactorisation = λ h →
        RP.≃-trans
          (solve 4
            (λ fn fh xx hh →
              (fh ⊖ (Κ 1ℚᵘ ⊖ (xx ⊕ hh)))
                ⊖ (fn ⊖ (Κ 1ℚᵘ ⊖ xx))
              ⊜ (fh ⊖ fn) ⊕ hh)
            RP.≃-refl
            (Finite.originalNegativeLogFiniteExponential x n)
            (Finite.originalNegativeLogFiniteExponential (R._+_ x h) n)
            x h)
          (RP.≃-trans
            (RP.+-cong
              (Factor.incrementFactorisation D h)
              RP.≃-refl)
            (solve 2
              (λ hh q →
                (hh ⊗ q) ⊕ hh
                  ⊜ hh ⊗ (q ⊕ Κ 1ℚᵘ))
              RP.≃-refl
              h (Factor.quotient D h)))
    ; Factor.quotientConvergesOnNullSequences =
        λ {perturbation} perturbationConverges →
          Seq.xₙ+yₙ→x₀+y₀
            (slope ,
              Factor.quotientConvergesOnNullSequences
                D perturbationConverges)
            (R.1ℝ , Power.constantConverges R.1ℝ)
    }

-- Literal source error at zero; this is also the zero initial value
-- used in the mesh endpoint proof, rather than a separate chosen
-- initial condition record.
originalFiniteLogExpErrorAtZero :
  (n : Nat) →
  R._≃_ (originalFiniteLogExpError n R.0ℝ) R.0ℝ
originalFiniteLogExpErrorAtZero n =
  RP.≃-trans
    (RP.+-cong
      (Initial.originalFiniteNegativeLogExpAtZero n)
      RP.≃-refl)
    (let open RP.ℝ-Solver in
     solve 0
       (Κ 1ℚᵘ ⊖ (Κ 1ℚᵘ ⊖ Κ 0ℚᵘ)
          ⊜ Κ 0ℚᵘ)
       RP.≃-refl)

-- Source ODE stability equation for the TARGET ERROR E_N, with
-- its actual derivative slope, not a generic or selected function.
originalFiniteLogExpErrorODE :
  (n : Nat) (x : R.ℝ) →
  R._≃_
    (R._+_
      (R._*_
        (R._-_ R.1ℝ x)
        (originalFiniteLogExpErrorSlope n x))
      (originalFiniteLogExpError n x))
    (R._*_
      (Finite.originalNegativeLogFiniteExponential x n)
      (R.pow x n))
originalFiniteLogExpErrorODE n x =
  let
    f = Finite.originalNegativeLogFiniteExponential x n
    p = Geo.negativeLogDerivativePolynomial x n
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 3
      (λ ff pp xx →
        ((Κ 1ℚᵘ ⊖ xx) ⊗
          ((ff ⊗ (⊝ pp)) ⊕ Κ 1ℚᵘ))
          ⊕ (ff ⊖ (Κ 1ℚᵘ ⊖ xx))
        ⊜ ((Κ 1ℚᵘ ⊖ xx) ⊗
          (ff ⊗ (⊝ pp))) ⊕ ff)
      RP.≃-refl f p x)
    (Residual.originalFiniteNegativeLogExpODEResidual x n)
