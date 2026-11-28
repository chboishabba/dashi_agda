module DASHI.Foundations.BishopFiniteCauchyShiftedWingAbsoluteExact where

------------------------------------------------------------------------
-- Finite Bishop Cauchy wing at ONE/TWO EARLIER TRIANGLE CUTS.
--
-- The existing native absolute wing bound controls Rect_c-Tri_c.
-- Original CMP102 actually needs Rect_c-Tri_(c-1) for A,
-- and Rect_c-Tri_(c-2) for B. The difference is EXACTLY one
-- or two original native Cauchy coefficient rows; it is NOT
-- legitimate to apply the old unshifted wing bound directly.
--
-- This module produces the correct shifted algebra and absolute
-- order bounds by consuming the existing unshifted donor plus
-- finite triangle successor and the original absolute triangle.
-- No new convergence or positive material/source assumption.
-- Native pinned Agda 2.9 kernel remains to be run.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Real as R
import RealProperties as P
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ)

-- All rectangles and rows use the ORIGINAL arbitrary coefficient
-- streams; in particular no positive/or otherwise altered polynomial.
originalRectangle : (Nat → R.ℝ) → (Nat → R.ℝ) → Nat → R.ℝ
originalRectangle a b height =
  Rectangle.rectangleSum a b height height

originalFullWing : (Nat → R.ℝ) → (Nat → R.ℝ) →
  Nat → Nat → R.ℝ
originalFullWing a b height count =
  R._-_ (originalRectangle a b height)
    (Row.trianglePartial a b count)

-- EXACT identity when the triangle is missing ONE last row.
originalWingOneEarlier :
  ∀ a b height count →
  R._≃_
    (originalFullWing a b height count)
    (R._+_ (originalFullWing a b height (suc count))
      (Row.cauchyCoefficient a b count))
originalWingOneEarlier a b height count =
  let
    rectangle = originalRectangle a b height
    triangle = Row.trianglePartial a b count
    row = Row.cauchyCoefficient a b count
    open P.ℝ-Solver
  in
  P.≃-trans
    (solve 3
      (λ r t c →
        r ⊖ t ⊜ (r ⊖ (t ⊕ c)) ⊕ c)
      P.≃-refl rectangle triangle row)
    (P.+-cong
      (P.+-cong
        P.≃-refl
        (P.-‿cong
          (P.≃-symm
            (FinSum.finSumSuccessor
              (Row.cauchyCoefficient a b) count))))
      P.≃-refl)

-- EXACT identity when the triangle is missing TWO last rows.
originalWingTwoEarlier :
  ∀ a b height count →
  R._≃_
    (originalFullWing a b height count)
    (R._+_
      (R._+_
        (originalFullWing a b height (suc (suc count)))
        (Row.cauchyCoefficient a b count))
      (Row.cauchyCoefficient a b (suc count)))
originalWingTwoEarlier a b height count =
  let
    full = originalFullWing a b height (suc (suc count))
    first = Row.cauchyCoefficient a b count
    second = Row.cauchyCoefficient a b (suc count)
    open P.ℝ-Solver
  in
  P.≃-trans
    (originalWingOneEarlier a b height count)
    (P.≃-trans
      (P.+-cong
        (originalWingOneEarlier a b height (suc count))
        P.≃-refl)
      (solve 3
        (λ f c d →
          (f ⊕ d) ⊕ c ⊜ (f ⊕ c) ⊕ d)
        P.≃-refl full first second))

-- A: shifted cutoff c-1. Positive triangle tail starts at c,
-- plus ABSOLUTE of exactly the omitted original row c-1.
originalWingOneEarlierAbsolute :
  ∀ a b n →
  R._≤_
    (R.∣ originalFullWing a b (suc n) n ∣)
    (R._+_
      (R._-_
        (Row.trianglePartial
          (Wing.absoluteTerms a) (Wing.absoluteTerms b)
          ((suc n) + (suc n)))
        (Row.trianglePartial
          (Wing.absoluteTerms a) (Wing.absoluteTerms b)
          (suc n)))
      (R.∣ Row.cauchyCoefficient a b n ∣))
originalWingOneEarlierAbsolute a b n =
  let
    full = originalFullWing a b (suc n) (suc n)
    row = Row.cauchyCoefficient a b n
    hbase = Wing.finiteCauchyWingAbsoluteBound a b (suc n)
  in
  P.≤-respˡ-≃
    (P.∣-∣-cong (originalWingOneEarlier a b (suc n) n))
    (P.≤-trans
      (P.∣x+y∣≤∣x∣+∣y∣ full row)
      (P.+-mono-≤ hbase P.≤-refl))

-- B: shifted cutoff c-2, for c>=2. The two exact original
-- endpoint rows are separately retained and charged.
originalWingTwoEarlierAbsolute :
  ∀ a b n →
  R._≤_
    (R.∣ originalFullWing a b (suc (suc n)) n ∣)
    (R._+_
      (R._+_
        (R._-_
          (Row.trianglePartial
            (Wing.absoluteTerms a) (Wing.absoluteTerms b)
            ((suc (suc n)) + (suc (suc n))))
          (Row.trianglePartial
            (Wing.absoluteTerms a) (Wing.absoluteTerms b)
            (suc (suc n))))
        (R.∣ Row.cauchyCoefficient a b n ∣))
      (R.∣ Row.cauchyCoefficient a b (suc n) ∣))
originalWingTwoEarlierAbsolute a b n =
  let
    height = suc (suc n)
    full = originalFullWing a b height height
    first = Row.cauchyCoefficient a b n
    second = Row.cauchyCoefficient a b (suc n)
    hbase = Wing.finiteCauchyWingAbsoluteBound a b height
    hfirst =
      P.≤-trans
        (P.∣x+y∣≤∣x∣+∣y∣ full first)
        (P.+-mono-≤ hbase P.≤-refl)
  in
  P.≤-respˡ-≃
    (P.∣-∣-cong (originalWingTwoEarlier a b height n))
    (P.≤-trans
      (P.∣x+y∣≤∣x∣+∣y∣ (R._+_ full first) second)
      (P.+-mono-≤ hfirst P.≤-refl))
