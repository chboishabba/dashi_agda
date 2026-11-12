module DASHI.Moonshine.AbelBishopComplexPowerDifferenceExact where

------------------------------------------------------------------------
-- SAME-SOURCE BISHOP COMPLEX FINITE POWER-DIFFERENCE IDENTITY
--
-- For all source x,h and Nat n:
--
--   (x+h)^n - x^n = h * Q_n(x,h),
--
--   Q_0(x,h)   = 0
--   Q_(n+1)    = Q_n(x,h)*(x+h) + x^n.
--
-- This is the exact finite algebra needed for a direct constructive
-- Lipschitz proof of the ORIGINAL log(1+u) power series:
--
--   u^k-v^k = (u-v) Q_k(v,u-v).
--
-- No complex derivative, division, or series limit is used here.
-- Reuses the original Bishop complex pair, real ring reflection
-- solver, and already-owned commutative semiring setoid laws.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws

open Algebra using (_+C_; _-C_; _*C_; powC)

originalComplexPowerDifferenceQuotient :
  Complex.BishopComplex → Complex.BishopComplex → Nat →
  Complex.BishopComplex
originalComplexPowerDifferenceQuotient x h zero =
  Algebra.zeroC
originalComplexPowerDifferenceQuotient x h (suc n) =
  (originalComplexPowerDifferenceQuotient x h n *C (x +C h))
    +C powC x n

-- The 8-coordinate computation is simply the identity
-- (y*Yn-x*Xn)=((Yn-Xn)*y)+(Xn*h), y=x+h.
originalComplexPowerDifferenceStep :
  ∀ x h xn yn →
  Complex._≈C_
    (((x +C h) *C yn) -C (x *C xn))
    (((yn -C xn) *C (x +C h)) +C (xn *C h))
originalComplexPowerDifferenceStep
  (Complex.complex a b)
  (Complex.complex c d)
  (Complex.complex e f)
  (Complex.complex g j) =
  (let open BishopP.ℝ-Solver in
    solve 8
      (λ a′ b′ c′ d′ e′ f′ g′ j′ →
        (((a′ ⊕ c′) ⊗ g′) ⊖ ((b′ ⊕ d′) ⊗ j′))
          ⊖ ((a′ ⊗ e′) ⊖ (b′ ⊗ f′))
        ⊜
        ((((g′ ⊖ e′) ⊗ (a′ ⊕ c′))
            ⊖ ((j′ ⊖ f′) ⊗ (b′ ⊕ d′)))
          ⊕ ((e′ ⊗ c′) ⊖ (f′ ⊗ d′))))
      BishopP.≃-refl a b c d e f g j)
  ,
  (let open BishopP.ℝ-Solver in
    solve 8
      (λ a′ b′ c′ d′ e′ f′ g′ j′ →
        (((a′ ⊕ c′) ⊗ j′) ⊕ ((b′ ⊕ d′) ⊗ g′))
          ⊖ ((a′ ⊗ f′) ⊕ (b′ ⊗ e′))
        ⊜
        ((((g′ ⊖ e′) ⊗ (b′ ⊕ d′))
            ⊕ ((j′ ⊖ f′) ⊗ (a′ ⊕ c′)))
          ⊕ ((e′ ⊗ d′) ⊕ (f′ ⊗ c′))))
      BishopP.≃-refl a b c d e f g j)

originalComplexPowerDifferenceZero :
  ∀ h →
  Complex._≈C_
    (Algebra.oneC -C Algebra.oneC)
    (h *C Algebra.zeroC)
originalComplexPowerDifferenceZero (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
    solve 2
      (λ x y →
        (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ)
        ⊜ (x ⊗ Κ 0ℚᵘ) ⊖ (y ⊗ Κ 0ℚᵘ))
      BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
    solve 2
      (λ x y →
        (Κ 0ℚᵘ ⊖ Κ 0ℚᵘ)
        ⊜ (x ⊗ Κ 0ℚᵘ) ⊕ (y ⊗ Κ 0ℚᵘ))
      BishopP.≃-refl a b)

originalComplexPowerDifferenceFactorisation :
  ∀ x h n →
  Complex._≈C_
    (powC (x +C h) n -C powC x n)
    (h *C originalComplexPowerDifferenceQuotient x h n)
originalComplexPowerDifferenceFactorisation x h zero =
  originalComplexPowerDifferenceZero h
originalComplexPowerDifferenceFactorisation x h (suc n) =
  let
    y = x +C h
    Q = originalComplexPowerDifferenceQuotient x h n
    xn = powC x n
    yn = powC y n
    induction = originalComplexPowerDifferenceFactorisation x h n
  in
  Complex.≈C-trans
    (originalComplexPowerDifferenceStep x h xn yn)
    (Complex.≈C-trans
      (Algebra.addCCongruent
        (Algebra.mulCCongruent induction (Complex.≈C-refl y))
        (Complex.≈C-refl (xn *C h)))
      (Complex.≈C-trans
        (Algebra.addCCongruent
          (Laws.complexMultiplyAssociative h Q y)
          (Laws.complexMultiplyCommutative xn h))
        (Complex.≈C-sym
          (Laws.complexMultiplyDistributesLeft
            h (Q *C y) xn))))
