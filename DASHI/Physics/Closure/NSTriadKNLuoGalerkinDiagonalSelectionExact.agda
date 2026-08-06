module DASHI.Physics.Closure.NSTriadKNLuoGalerkinDiagonalSelectionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: John G. Heywood.
-- Title: "An Error Estimate Uniform in Time for Spectral Galerkin
-- Approximations of the Navier-Stokes Problem".
-- Pacific Journal of Mathematics 98 (1982), 333--345.
-- DOI: 10.2140/pjm.1982.98.333.
--
-- Classical PDE reference:
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Close the order-theoretic diagonal-selection step that is required when the
-- shell q and Galerkin cutoff N both tend to infinity. Fixed-q convergence
-- alone does not provide one cutoff uniform in all q. Instead choose, for
-- every q, a positive tolerance tau_q and a cutoff N(q) at which
--
--   error(q,N(q)) <= tau_q.
--
-- If tau_q tends to zero, the selected diagonal error also tends to zero.
-- The theorem constructs N(q) from the pointwise convergence witnesses; no
-- uniform convergence or compactness is silently assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Properties as ℕₚ
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record PointwiseGalerkinErrorData : Set where
  constructor pointwise-galerkin-error-data
  field
    approximationError : Nat → Nat → ℚ
    pointwiseErrorTendsToZero :
      (shell : Nat) →
      Limit.TendsToZero (approximationError shell)

    tolerance : Nat → ℚ
    tolerancePositive :
      (shell : Nat) →
      0ℚ < tolerance shell
    toleranceTendsToZero :
      Limit.TendsToZero tolerance

open PointwiseGalerkinErrorData public

selectedCutoff : PointwiseGalerkinErrorData → Nat → Nat
selectedCutoff dataSet shell =
  Limit.cutoff
    (Limit.eventuallySmall
      (pointwiseErrorTendsToZero dataSet shell)
      (tolerance dataSet shell)
      (tolerancePositive dataSet shell))

diagonalError : PointwiseGalerkinErrorData → Nat → ℚ
diagonalError dataSet shell =
  approximationError dataSet shell (selectedCutoff dataSet shell)

diagonalErrorBelowTolerance :
  (dataSet : PointwiseGalerkinErrorData) →
  (shell : Nat) →
  diagonalError dataSet shell ≤ tolerance dataSet shell
diagonalErrorBelowTolerance dataSet shell =
  let
    witness =
      Limit.eventuallySmall
        (pointwiseErrorTendsToZero dataSet shell)
        (tolerance dataSet shell)
        (tolerancePositive dataSet shell)
  in
  Limit.tailBound witness
    (Limit.cutoff witness)
    ℕₚ.≤-refl

diagonalErrorTendsToZero :
  (dataSet : PointwiseGalerkinErrorData) →
  Limit.TendsToZero (diagonalError dataSet)
diagonalErrorTendsToZero dataSet =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (diagonalError dataSet)
      (tolerance dataSet)
      (diagonalErrorBelowTolerance dataSet))
    (toleranceTendsToZero dataSet)
