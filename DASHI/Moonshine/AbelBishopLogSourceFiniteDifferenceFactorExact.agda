module DASHI.Moonshine.AbelBishopLogSourceFiniteDifferenceFactorExact where

------------------------------------------------------------------------
-- LITERAL LOG(1+u) TERMS: EXACT FINITE DIFFERENCE FACTORIZATION.
--
-- a_n(w) = (-1)^n w^(n+1)/(n+1) belongs to the original
-- AbelBishopLogOnePlusOriginalSeriesExact source.
--
-- For all Bishop complex v,h, Nat n:
--
--   a_n(v+h)-a_n(v)
--      ~= coeff(n) * [h * Q_(n+1)(v,h)]
--
-- where Q_(n+1) is the SAME finite complex power-difference
-- polynomial from AbelBishopComplexPowerDifferenceExact.
--
-- This is the exact combinatorial base of the constructive estimate
--
--   |log(1+u)-log(1+v)| <= |u-v|/(1-max(|u|,|v|)).
--
-- All statements here are finite setoid algebra, independent
-- of unproved infinite-limit/holomorphic differentiation theorems.
------------------------------------------------------------------------

open import Data.Product.Base using (_,_)
open import Agda.Builtin.Nat using (suc)

import Real as BishopReal
import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Moonshine.AbelBishopComplexPowerDifferenceExact as Difference

open Algebra using (_+C_; _-C_; _*C_; powC)

originalBishopComplexScaleSubtract :
  ∀ scalar x y →
  Complex._≈C_
    ((Algebra.scaleC scalar x) -C (Algebra.scaleC scalar y))
    (Algebra.scaleC scalar (x -C y))
originalBishopComplexScaleSubtract
  scalar (Complex.complex a b) (Complex.complex c d) =
  (let open BishopP.ℝ-Solver in
    solve 3
      (λ s x y →
        (s ⊗ x) ⊖ (s ⊗ y)
        ⊜ s ⊗ (x ⊖ y))
      BishopP.≃-refl scalar a c)
  ,
  (let open BishopP.ℝ-Solver in
    solve 3
      (λ s x y →
        (s ⊗ x) ⊖ (s ⊗ y)
        ⊜ s ⊗ (x ⊖ y))
      BishopP.≃-refl scalar b d)

originalBishopLogActualTermDifferenceFactor :
  ∀ v h n →
  Complex._≈C_
    ((Log.originalBishopLogOnePlusTerm (v +C h) n)
      -C (Log.originalBishopLogOnePlusTerm v n))
    (Algebra.scaleC
      (Log.logCoefficient n)
      (h *C
        (Difference.originalComplexPowerDifferenceQuotient
          v h (suc n))))
originalBishopLogActualTermDifferenceFactor v h n =
  Difference.complexTrans
    (originalBishopComplexScaleSubtract
      (Log.logCoefficient n)
      (powC (v +C h) (suc n))
      (powC v (suc n)))
    (Algebra.scaleCCongruent
      (Difference.originalComplexPowerDifferenceFactorisation
        v h (suc n))
      (Log.logCoefficient n))
