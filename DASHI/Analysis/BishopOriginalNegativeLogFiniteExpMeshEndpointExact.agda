module DASHI.Analysis.BishopOriginalNegativeLogFiniteExpMeshEndpointExact where

------------------------------------------------------------------------
-- P0 / K04d: ACTUAL ORIGINAL FINITE LOG EXPONENTIAL ENDPOINT.
--
-- Reuse:
--   BishopOriginalFactorIncrementFiniteTelescopeExact
--   BishopOriginalNegativeLogFiniteExpDerivativeResidualExact
--   BishopOriginalNegativeLogFiniteExpInitialValueExact
--
-- At every fixed LOG stage N and every finite original Bishop walk
-- starting at zero, the actual value F_N(x_final)-1 is the finite
-- sum of step increments times source derivative factor quotients.
--
-- This is a genuine same-object finite endpoint identity. It does
-- NOT yet prove the required mesh-uniform convergence of the source
-- factor quotients or the continuous integral/stability bound.
--
-- Attribution: Bishop/Bridges, Murray/Csimma, DASHI finite
-- factor-derivative and original finite-log authors.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Telescope
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpDerivativeResidualExact as Residual
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpInitialValueExact as Initial
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geometric

sourceFiniteLogExpDerivativeAt :
  (stage : Nat) →
  (point : R.ℝ) →
  R.ℝ
sourceFiniteLogExpDerivativeAt stage point =
  R._*_
    (Finite.originalNegativeLogFiniteExponential point stage)
    (R.-_ (Geometric.negativeLogDerivativePolynomial point stage))

sourceFiniteLogExpMeshDerivative :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  Nat → R.ℝ
sourceFiniteLogExpMeshDerivative stage steps n =
  sourceFiniteLogExpDerivativeAt stage
    (Telescope.finiteWalk R.0ℝ steps n)

sourceFiniteLogExpMeshReceipt :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  (n : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ point → Finite.originalNegativeLogFiniteExponential point stage)
    (Telescope.finiteWalk R.0ℝ steps n)
    (sourceFiniteLogExpMeshDerivative stage steps n)
sourceFiniteLogExpMeshReceipt stage steps n =
  Residual.originalFiniteNegativeLogExpDerivative
    (Telescope.finiteWalk R.0ℝ steps n)
    stage

sourceFiniteLogExpMeshQuotient :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  Nat → R.ℝ
sourceFiniteLogExpMeshQuotient stage steps n =
  Factor.quotient
    (sourceFiniteLogExpMeshReceipt stage steps n)
    (steps n)

-- Exact value of the original finite exponential after traversing
-- arbitrary finitely many original Bishop mesh cells.
originalFiniteLogExpEndpointFromMesh :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  (cells : Nat) →
  R._≃_
    (R._-_
      (Finite.originalNegativeLogFiniteExponential
        (Telescope.finiteWalk R.0ℝ steps cells) stage)
      R.1ℝ)
    (Telescope.sumFinite
      (λ n → R._*_ (steps n)
        (sourceFiniteLogExpMeshQuotient stage steps n))
      cells)
originalFiniteLogExpEndpointFromMesh stage steps cells =
  RP.≃-trans
    (RP.+-cong RP.≃-refl
      (RP.-‿cong
        (RP.≃-symm
          (Initial.originalFiniteNegativeLogExpAtZero stage))))
    (Telescope.originalBishopFactorFiniteEndpointFTC
      (λ point → Finite.originalNegativeLogFiniteExponential point stage)
      R.0ℝ
      steps
      (sourceFiniteLogExpMeshDerivative stage steps)
      (sourceFiniteLogExpMeshReceipt stage steps)
      cells)
