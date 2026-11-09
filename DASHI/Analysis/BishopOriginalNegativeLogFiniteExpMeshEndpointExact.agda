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
open import Data.Rational.Unnormalised using (1ℚᵘ)

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

------------------------------------------------------------------------
-- EXACT ERROR EQUATION AGAINST THE TARGET 1-x ON EACH FINITE MESH.
-- This is a source theorem, not an analytic approximation claim.
------------------------------------------------------------------------

sourceFiniteMeshWalkIsStepSum :
  (steps : Nat → R.ℝ) →
  (cells : Nat) →
  R._≃_
    (Telescope.finiteWalk R.0ℝ steps cells)
    (Telescope.sumFinite steps cells)
sourceFiniteMeshWalkIsStepSum steps cells = RP.≃-refl

sourceFiniteMeshErrorSumDecomposition :
  (steps quotient : Nat → R.ℝ) →
  (cells : Nat) →
  R._≃_
    (Telescope.sumFinite
      (λ j → R._*_ (steps j)
        (R._+_ (quotient j) R.1ℝ))
      cells)
    (R._+_
      (Telescope.sumFinite
        (λ j → R._*_ (steps j) (quotient j))
        cells)
      (Telescope.sumFinite steps cells))
sourceFiniteMeshErrorSumDecomposition steps quotient zero =
  let open RP.ℝ-Solver in
  solve 0
    (Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ)
    RP.≃-refl
sourceFiniteMeshErrorSumDecomposition steps quotient (suc n) =
  RP.≃-trans
    (RP.+-cong
      (sourceFiniteMeshErrorSumDecomposition steps quotient n)
      RP.≃-refl)
    (let open RP.ℝ-Solver in
     solve 4
       (λ quotientSum stepSum increment q →
         ((quotientSum ⊕ stepSum)
           ⊕ (increment ⊗ (q ⊕ Κ 1ℚᵘ)))
         ⊜ ((quotientSum ⊕ (increment ⊗ q))
           ⊕ (stepSum ⊕ increment)))
       RP.≃-refl
       (Telescope.sumFinite
         (λ j → R._*_ (steps j) (quotient j)) n)
       (Telescope.sumFinite steps n)
       (steps n)
       (quotient n))

-- Original P0 terminal error from finite mesh quotient *defects*.
-- To turn this into an analytic bound, an explicit mesh-uniform
-- estimate on quotient+1 is still necessary; the existing residual
-- controls the derivative value and cannot be substituted for such a
-- factor-quotient bound without a continuity/FTC argument.
originalFiniteLogExpErrorFromMesh :
  (stage : Nat) →
  (steps : Nat → R.ℝ) →
  (cells : Nat) →
  let
    x = Telescope.finiteWalk R.0ℝ steps cells
    f = Finite.originalNegativeLogFiniteExponential x stage
  in
  R._≃_
    (R._-_ f (R._-_ R.1ℝ x))
    (Telescope.sumFinite
      (λ n → R._*_ (steps n)
        (R._+_
          (sourceFiniteLogExpMeshQuotient stage steps n)
          R.1ℝ))
      cells)
originalFiniteLogExpErrorFromMesh stage steps cells =
  let
    x = Telescope.finiteWalk R.0ℝ steps cells
    f = Finite.originalNegativeLogFiniteExponential x stage
    q = sourceFiniteLogExpMeshQuotient stage steps
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 2
      (λ value endpoint →
        value ⊖ (Κ 1ℚᵘ ⊖ endpoint)
        ⊜ (value ⊖ Κ 1ℚᵘ) ⊕ endpoint)
      RP.≃-refl f x)
    (RP.≃-trans
      (RP.+-cong
        (originalFiniteLogExpEndpointFromMesh stage steps cells)
        (sourceFiniteMeshWalkIsStepSum steps cells))
      (RP.≃-symm
        (sourceFiniteMeshErrorSumDecomposition steps q cells)))
