module DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundExact where

------------------------------------------------------------------------
-- FINITE BISHOP SERIES TRIANGLE INEQUALITY
--
-- DASHI CONTRIBUTION
--
-- For every finite prefix,
--
--   | sum_{j<n} a_j | <= sum_{j<n} |a_j|.
--
-- This is the finite algebraic inequality needed by Cauchy-product wing
-- estimates.  It uses only the scalar Bishop absolute-value triangle law and
-- monotonicity of addition; no convergence or rearrangement theorem enters.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

finiteSeriesAbsoluteBound :
  (terms : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣ BishopSequence.SeriesOf terms count ∣)
    (BishopSequence.SeriesOf
      (λ index → BishopReal.∣ terms index ∣)
      count)
finiteSeriesAbsoluteBound terms zero =
  BishopP.≤-respˡ-≃
    (BishopP.nonNegx⇒∣x∣≃x BishopP.nonNeg0)
    BishopP.≤-refl
finiteSeriesAbsoluteBound terms (suc count) =
  BishopP.≤-trans
    (BishopP.∣x+y∣≤∣x∣+∣y∣
      (BishopSequence.SeriesOf terms count)
      (terms count))
    (BishopP.+-mono-≤
      (finiteSeriesAbsoluteBound terms count)
      BishopP.≤-refl)
