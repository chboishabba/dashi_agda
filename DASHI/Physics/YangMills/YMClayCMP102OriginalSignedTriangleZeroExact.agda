module DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact where

------------------------------------------------------------------------
-- Original all-degree CMP102 finite *polynomial evaluation* triangle.
-- The source is the EXISTING original signed Cauchy coefficient:
--    oddPart n - evenPart n = 0, every n (including n=0).
-- Unlike a declaration about an abstract row this theorem multiplies
-- the native source row by the ACTUAL Bishop power X^n and sums over
-- its native Sequence.SeriesOf COUNT prefix.
--
-- All n, all signed Bishop real X, all prefix counts; no new formal
-- power-series carrier, no endpoint exception and no convergence.
-- Pending native Agda 2.9 typecheck.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as Original

originalSignedCoefficientAt : R.ℝ → Nat → R.ℝ
originalSignedCoefficientAt X n =
  R._*_ (Original.shiftedNativeBracketCoefficient n) (R.pow X n)

originalSignedCoefficientAtZero : ∀ X n →
  R._≃_ (originalSignedCoefficientAt X n) R.0ℝ
originalSignedCoefficientAtZero X n =
  P.≃-trans
    (P.*-congʳ (Original.shiftedNativeBracketCoefficientZero n))
    (let open P.ℝ-Solver
     in solve 1
          (λ p → Κ 0ℚᵘ ⊗ p ⊜ Κ 0ℚᵘ)
          P.≃-refl (R.pow X n))

originalSignedTriangle : R.ℝ → Nat → R.ℝ
originalSignedTriangle X count =
  Seq.SeriesOf (originalSignedCoefficientAt X) count

-- This is the finite original native signed-row zero certificate
-- at every N. The only next algebraic step is identifying G_N
-- with the *same source* signed triangle plus its Cauchy wings;
-- see originalFiniteCauchyWingBoundsExact.
originalSignedTriangleZero : ∀ X count →
  R._≃_ (originalSignedTriangle X count) R.0ℝ
originalSignedTriangleZero X zero = P.≃-refl
originalSignedTriangleZero X (suc count) =
  P.≃-trans
    (P.+-cong
      (originalSignedTriangleZero X count)
      (originalSignedCoefficientAtZero X count))
    (let open P.ℝ-Solver
     in solve 0
          (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
          P.≃-refl)
