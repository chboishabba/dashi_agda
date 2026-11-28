module DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact where

------------------------------------------------------------------------
-- ORIGINAL CMP102/109 finite analytic positive/negative wings.
--
-- The same actual CMP109 coefficient history, native Bishop real,
-- original Sequence.SeriesOf count and existing proved finite
-- Cauchy rectangle-minus-triangle domination.
--
-- This is a real all-count original-source inequality, not a new
-- tail/limit postulate or a redefined A/B analytic function.
-- Still needs pinned native Agda acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
import Real as R
import RealProperties as P

import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP109
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

import DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundExact as FiniteAbsolute
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import Sequence as Seq

-- These are definitionally the original finite CMP109 terms and
-- therefore their SeriesOf prefixes ARE Original.aPrefix/bPrefix.
aTerm bTerm : R.ℝ → Nat → R.ℝ
aTerm X = CMP109.term CMP102.aCoefficient X
bTerm X = CMP109.term CMP102.bCoefficient X

-- True signed-input finite-prefix absolute bounds, including X<0.
-- No infinite Cauchy rearrangement or radius smaller than 1/4.
originalAPrefixAbsoluteBound : ∀ X count →
  R._≤_ (R.∣ Original.aPrefix X count ∣)
    (Seq.SeriesOf (λ k → R.∣ aTerm X k ∣) count)
originalAPrefixAbsoluteBound X count =
  FiniteAbsolute.finiteSeriesAbsoluteBound (aTerm X) count

originalBPrefixAbsoluteBound : ∀ X count →
  R._≤_ (R.∣ Original.bPrefix X count ∣)
    (Seq.SeriesOf (λ k → R.∣ bTerm X k ∣) count)
originalBPrefixAbsoluteBound X count =
  FiniteAbsolute.finiteSeriesAbsoluteBound (bTerm X) count

-- All-count SAME-source A(X)^2 finite rectangle vs Cauchy triangle:
-- positive wing is only the existing original Bishop absolute
-- coefficient triangle tail, not an invented absolute product.
originalASquareCauchyWingFiniteBound : ∀ X count →
  R._≤_
    (R.∣ R._-_
      (Rectangle.rectangleSum (aTerm X) (aTerm X) count count)
      (Row.trianglePartial (aTerm X) (aTerm X) count) ∣)
    (R._-_
      (Row.trianglePartial (Wing.absoluteTerms (aTerm X))
        (Wing.absoluteTerms (aTerm X)) (count + count))
      (Row.trianglePartial (Wing.absoluteTerms (aTerm X))
        (Wing.absoluteTerms (aTerm X)) count))
originalASquareCauchyWingFiniteBound X count =
  Wing.finiteCauchyWingAbsoluteBound (aTerm X) (aTerm X) count

originalBSquareCauchyWingFiniteBound : ∀ X count →
  R._≤_
    (R.∣ R._-_
      (Rectangle.rectangleSum (bTerm X) (bTerm X) count count)
      (Row.trianglePartial (bTerm X) (bTerm X) count) ∣)
    (R._-_
      (Row.trianglePartial (Wing.absoluteTerms (bTerm X))
        (Wing.absoluteTerms (bTerm X)) (count + count))
      (Row.trianglePartial (Wing.absoluteTerms (bTerm X))
        (Wing.absoluteTerms (bTerm X)) count))
originalBSquareCauchyWingFiniteBound X count =
  Wing.finiteCauchyWingAbsoluteBound (bTerm X) (bTerm X) count

-- Original square terms in G_count are EXACTLY the original finite
-- Bishop Cauchy rectangles: this consumes the existing source
-- rectangleProduct proof, not a formal power-series equality.
originalASquareIsOriginalRectangle : ∀ X count →
  R._≃_
    (R._*_ (Original.aPrefix X count)
           (Original.aPrefix X count))
    (Rectangle.rectangleSum (aTerm X) (aTerm X) count count)
originalASquareIsOriginalRectangle X count =
  P.≃-symm (Rectangle.rectangleProduct (aTerm X) (aTerm X) count count)

originalBSquareIsOriginalRectangle : ∀ X count →
  R._≃_
    (R._*_ (Original.bPrefix X count)
           (Original.bPrefix X count))
    (Rectangle.rectangleSum (bTerm X) (bTerm X) count count)
originalBSquareIsOriginalRectangle X count =
  P.≃-symm (Rectangle.rectangleProduct (bTerm X) (bTerm X) count count)
