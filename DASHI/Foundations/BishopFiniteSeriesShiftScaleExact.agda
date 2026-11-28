module DASHI.Foundations.BishopFiniteSeriesShiftScaleExact where

------------------------------------------------------------------------
-- Original Bishop SeriesOf finite SCALE and HEAD-SHIFT receipts.
-- Both are uniform in count, including count=0. These are needed
-- to move the original CMP102 even/odd row prefixes across the
-- literal odd/even Cauchy degree shift, not merely assert a bridge.
--
-- Reuses original BishopReal.ℝ and Sequence.SeriesOf, plus
-- Row.finSumHead on the original Fin-indexed constructor.
-- No new sequence convergence, external analytic source or axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum

-- Multiplication by a single Bishop real distributes through the
-- ORIGINAL count-indexed SeriesOf, for every signed X.
finiteSeriesScale : ∀ x (term : Nat → R.ℝ) count →
  R._≃_
    (Seq.SeriesOf (λ k → R._*_ x (term k)) count)
    (R._*_ x (Seq.SeriesOf term count))
finiteSeriesScale x term zero =
  let open P.ℝ-Solver
  in solve 1
      (λ q → Κ 0ℚᵘ ⊜ q ⊗ Κ 0ℚᵘ)
      P.≃-refl x
finiteSeriesScale x term (suc count) =
  P.≃-trans
    (P.+-cong
      (finiteSeriesScale x term count)
      P.≃-refl)
    (P.≃-symm
      (P.*-distribˡ-+
        x (Seq.SeriesOf term count) (term count)))

-- Original first term and remaining shifted term family, in the
-- native Fin-sum-head exact equality: no subtraction or excluded
-- endpoint convention is needed for the degree-zero singleton.
finiteSeriesHeadShift : ∀ (term : Nat → R.ℝ) count →
  R._≃_
    (Seq.SeriesOf term (suc count))
    (R._+_ (term zero)
      (Seq.SeriesOf (Row.shift term) count))
finiteSeriesHeadShift term count =
  P.≃-trans
    (P.≃-symm (FinSum.finSumIsSeriesOf term (suc count)))
    (P.≃-trans
      (Row.finSumHead term count)
      (P.+-congʳ
        (term zero)
        (FinSum.finSumIsSeriesOf (Row.shift term) count)))

-- A complete exact one-line BIDI for the source finite scale after
-- the head shift, including all count boundary cases.
finiteSeriesScaledHeadShift : ∀ x (term : Nat → R.ℝ) count →
  R._≃_
    (Seq.SeriesOf (λ k → R._*_ x (term k)) (suc count))
    (R._*_ x
      (R._+_ (term zero)
        (Seq.SeriesOf (Row.shift term) count)))
finiteSeriesScaledHeadShift x term count =
  P.≃-trans
    (finiteSeriesScale x term (suc count))
    (P.*-congˡ (finiteSeriesHeadShift term count))
