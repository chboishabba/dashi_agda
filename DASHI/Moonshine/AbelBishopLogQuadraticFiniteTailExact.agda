module DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG(1+u): EXACT FINITE QUADRATIC TAIL SPLIT.
--
-- On the LITERAL existing coefficient stream
--   a_k(u) = (-1)^k * u^(k+1)/(k+1),
--
-- the k=0 term is exactly u in Bishop complex SETOID equality,
-- and for every n:
--
--   sum_{k<1+n} a_k(u)
--     ~= u + sum_{k<n} a_(k+1)(u).
--
-- Thus R_2 is the actual shifted source series with only powers
-- u^(k+2). This is the finite algebraic owner for the original
-- logarithmic remainder; no new log or analytic derivative assumed.
--
-- Still OPEN: quantitative upper bound for the shifted series,
-- its uniform convergence and identified principal-branch germ.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log

originalBishopLogFirstSourceTermIsArgument :
  ∀ w →
  Complex._≈C_ (Log.originalBishopLogOnePlusTerm w zero) w
originalBishopLogFirstSourceTermIsArgument
  (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
    solve 2
      (λ x y →
        Κ 1ℚᵘ ⊗
          ((x ⊗ Κ 1ℚᵘ) ⊖ (y ⊗ Κ 0ℚᵘ))
        ⊜ x)
      BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
    solve 2
      (λ x y →
        Κ 1ℚᵘ ⊗
          ((x ⊗ Κ 0ℚᵘ) ⊕ (y ⊗ Κ 1ℚᵘ))
        ⊜ y)
      BishopP.≃-refl a b)

-- This finite reindexing holds for ANY original Bishop real stream,
-- avoiding arbitrary equality of independent log coefficient lists.
originalBishopScalarFirstPlusShift :
  (terms : Nat → BishopReal.ℝ) →
  ∀ n →
  BishopReal._≃_
    (BishopSequence.SeriesOf terms (suc n))
    (BishopReal._+_
      (terms zero)
      (BishopSequence.SeriesOf (λ k → terms (suc k)) n))
originalBishopScalarFirstPlusShift terms zero =
  BishopP.≃-trans
    (BishopP.+-identityˡ (terms zero))
    (BishopP.≃-symm (BishopP.+-identityʳ (terms zero)))
originalBishopScalarFirstPlusShift terms (suc n) =
  BishopP.≃-trans
    (BishopP.+-cong
      (originalBishopScalarFirstPlusShift terms n)
      BishopP.≃-refl)
    (BishopP.+-assoc
      (terms zero)
      (BishopSequence.SeriesOf (λ k → terms (suc k)) n)
      (terms (suc n)))

originalBishopLogQuadraticTailPrefix :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopLogQuadraticTailPrefix w n =
  Complex.complex
    (BishopSequence.SeriesOf
      (λ k → Complex.re (Log.originalBishopLogOnePlusTerm w (suc k)))
      n)
    (BishopSequence.SeriesOf
      (λ k → Complex.im (Log.originalBishopLogOnePlusTerm w (suc k)))
      n)

originalBishopLogFinitePrefix :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopLogFinitePrefix w n =
  Complex.complex
    (BishopSequence.SeriesOf
      (Complex.realTerms (Log.originalBishopLogOnePlusTerm w))
      n)
    (BishopSequence.SeriesOf
      (Complex.imagTerms (Log.originalBishopLogOnePlusTerm w))
      n)

originalBishopLogFiniteQuadraticDecomposition :
  ∀ w n →
  Complex._≈C_
    (originalBishopLogFinitePrefix w (suc n))
    (Algebra._+C_ w (originalBishopLogQuadraticTailPrefix w n))
originalBishopLogFiniteQuadraticDecomposition w n =
  (BishopP.≃-trans
    (originalBishopScalarFirstPlusShift
      (Complex.realTerms (Log.originalBishopLogOnePlusTerm w))
      n)
    (BishopP.+-cong
      (proj₁ (originalBishopLogFirstSourceTermIsArgument w))
      BishopP.≃-refl))
  ,
  (BishopP.≃-trans
    (originalBishopScalarFirstPlusShift
      (Complex.imagTerms (Log.originalBishopLogOnePlusTerm w))
      n)
    (BishopP.+-cong
      (proj₂ (originalBishopLogFirstSourceTermIsArgument w))
      BishopP.≃-refl))
