module DASHI.Moonshine.AbelBishopLogFiniteGeometricDerivativeExact where

------------------------------------------------------------------------
-- FINITE POLYNOMIAL IDENTITY ON THE ORIGINAL BISHOP REAL CARRIER.
--
-- Write P_N(w) = 1 - w + w^2 - ... + (-w)^(N-1).
-- This is the derivative polynomial of the truncated local log series.
--
-- For EVERY N (not a finite numerical regression):
--
--   (1 + w) P_N(w) ~= 1 - (-w)^N.
--
-- The proof is finite, elementary, and uses only Bishop-real ring laws.
-- It is the algebraic producer needed for showing that the *actual*
-- local log series has derivative 1/(1+w), after source-native
-- differentiation and uniform-limit transfer.
--
-- It does NOT prove the derivative of the infinite series, does NOT
-- construct a complex reciprocal, and does NOT identify principal Log.
-- No new analytic authority, postulate, or trust escape is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as Bishop
import RealProperties as BishopP

geometricDerivativePrefix : Bishop.ℝ → Nat → Bishop.ℝ
geometricDerivativePrefix w zero = Bishop.0ℝ
geometricDerivativePrefix w (suc n) =
  Bishop._+_
    (geometricDerivativePrefix w n)
    (Bishop.pow (Bishop.- w) n)

geometricDerivativePrefixZero :
  ∀ w →
  Bishop._≃_
    (geometricDerivativePrefix w zero)
    Bishop.0ℝ
geometricDerivativePrefixZero w = BishopP.≃-refl

geometricDerivativePrefixSuccessor :
  ∀ w n →
  Bishop._≃_
    (geometricDerivativePrefix w (suc n))
    (Bishop._+_
      (geometricDerivativePrefix w n)
      (Bishop.pow (Bishop.- w) n))
geometricDerivativePrefixSuccessor w n = BishopP.≃-refl

originalBishopFiniteLogDerivativeGeometricIdentity :
  ∀ w n →
  Bishop._≃_
    (Bishop._*_
      (Bishop._+_ Bishop.1ℝ w)
      (geometricDerivativePrefix w n))
    (Bishop._-_ Bishop.1ℝ (Bishop.pow (Bishop.- w) n))
originalBishopFiniteLogDerivativeGeometricIdentity w zero =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x →
      ((Κ 1ℚᵘ ⊕ x) ⊗ Κ 0ℚᵘ)
      ⊜ (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ))
    BishopP.≃-refl w
originalBishopFiniteLogDerivativeGeometricIdentity w (suc n) =
  BishopP.≃-trans expanded
    (BishopP.≃-trans
      (BishopP.+-cong
        (originalBishopFiniteLogDerivativeGeometricIdentity w n)
        BishopP.≃-refl)
      remainder)
  where
    prefix = geometricDerivativePrefix w n
    power = Bishop.pow (Bishop.- w) n

    expanded :
      Bishop._≃_
        (Bishop._*_
          (Bishop._+_ Bishop.1ℝ w)
          (Bishop._+_ prefix power))
        (Bishop._+_
          (Bishop._*_
            (Bishop._+_ Bishop.1ℝ w) prefix)
          (Bishop._*_
            (Bishop._+_ Bishop.1ℝ w) power))
    expanded =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ x p a →
          (Κ 1ℚᵘ ⊕ x) ⊗ (p ⊕ a)
          ⊜
          ((Κ 1ℚᵘ ⊕ x) ⊗ p)
          ⊕ ((Κ 1ℚᵘ ⊕ x) ⊗ a))
        BishopP.≃-refl w prefix power

    remainder :
      Bishop._≃_
        (Bishop._+_
          (Bishop._-_ Bishop.1ℝ power)
          (Bishop._*_ (Bishop._+_ Bishop.1ℝ w) power))
        (Bishop._-_
          Bishop.1ℝ
          (Bishop.pow (Bishop.- w) (suc n)))
    remainder =
      let open BishopP.ℝ-Solver
      in solve 2
        (λ x a →
          (Κ 1ℚᵘ ⊖ a)
          ⊕ ((Κ 1ℚᵘ ⊕ x) ⊗ a)
          ⊜ (Κ 1ℚᵘ ⊖ (a ⊗ (⊝ x))))
        BishopP.≃-refl w power
