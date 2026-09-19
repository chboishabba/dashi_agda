module DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact where

------------------------------------------------------------------------
-- FINITE CAUCHY WING ABSOLUTE BOUND
--
-- DASHI CONTRIBUTION
--
-- For arbitrary Bishop-real sequences a,b and every N,
--
--   | R_N(a,b) - T_N(a,b) |
--     <=
--   T_(2N)(|a|,|b|) - T_N(|a|,|b|),
--
-- where R_N is the N x N Cauchy rectangle and T_N is the first N
-- Cauchy-product coefficients.
--
-- This is the exact finite estimate needed by the Bishop Mertens/Cauchy
-- product argument.  No infinite rearrangement theorem or convergence
-- authority is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundExact as AbsSum
import DASHI.Foundations.BishopFiniteSeriesTailAbsoluteBoundExact as TailAbs
import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as Difference
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as RectInside
import DASHI.Foundations.BishopFiniteCauchyTriangleInsideRectangleExact as TriInside
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row

absoluteTerms : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
absoluteTerms terms index = BishopReal.∣ terms index ∣

------------------------------------------------------------------------
-- Fin-prefix version of the previously-owned SeriesOf tail inequality.
------------------------------------------------------------------------

finPrefixTailAbsoluteBound :
  (terms : Nat → BishopReal.ℝ) →
  ∀ count index →
  index Nat.< count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (FinSum.finSum terms count)
        (FinSum.finSum terms (count Nat.∸ index))
    ∣)
    (BishopReal._-_
      (FinSum.finSum (absoluteTerms terms) count)
      (FinSum.finSum (absoluteTerms terms) (count Nat.∸ index)))
finPrefixTailAbsoluteBound terms count index index<count =
  let
    index≤count = NatP.<⇒≤ index<count
    decompose : (count Nat.∸ index) + index ≡ count
    decompose = NatP.m∸n+n≡m index≤count

    raw =
      TailAbs.finiteTailAbsoluteBound
        terms
        (count Nat.∸ index)
        index

    signedEnd :
      BishopReal._≃_
        (BishopSequence.SeriesOf terms ((count Nat.∸ index) + index))
        (BishopSequence.SeriesOf terms count)
    signedEnd =
      BishopP.≃-refl₂
        (cong (BishopSequence.SeriesOf terms) decompose)

    absEnd :
      BishopReal._≃_
        (BishopSequence.SeriesOf
          (absoluteTerms terms)
          ((count Nat.∸ index) + index))
        (BishopSequence.SeriesOf
          (absoluteTerms terms)
          count)
    absEnd =
      BishopP.≃-refl₂
        (cong
          (BishopSequence.SeriesOf (absoluteTerms terms))
          decompose)

    signedPrefixBridge :
      BishopReal._≃_
        (BishopReal._-_
          (FinSum.finSum terms count)
          (FinSum.finSum terms (count Nat.∸ index)))
        (BishopReal._-_
          (BishopSequence.SeriesOf terms count)
          (BishopSequence.SeriesOf terms (count Nat.∸ index)))
    signedPrefixBridge =
      BishopP.+-cong
        (FinSum.finSumIsSeriesOf terms count)
        (BishopP.-‿cong
          (FinSum.finSumIsSeriesOf terms (count Nat.∸ index)))

    absPrefixBridge :
      BishopReal._≃_
        (BishopReal._-_
          (FinSum.finSum (absoluteTerms terms) count)
          (FinSum.finSum (absoluteTerms terms) (count Nat.∸ index)))
        (BishopReal._-_
          (BishopSequence.SeriesOf (absoluteTerms terms) count)
          (BishopSequence.SeriesOf
            (absoluteTerms terms)
            (count Nat.∸ index)))
    absPrefixBridge =
      BishopP.+-cong
        (FinSum.finSumIsSeriesOf (absoluteTerms terms) count)
        (BishopP.-‿cong
          (FinSum.finSumIsSeriesOf
            (absoluteTerms terms)
            (count Nat.∸ index)))
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm absPrefixBridge)
    (BishopP.≤-respˡ-≃
      (BishopP.∣-∣-cong signedPrefixBridge)
      (BishopP.≤-respʳ-≃
        (BishopP.+-cong
          absEnd
          (BishopP.-‿cong BishopP.≃-refl))
        (BishopP.≤-respˡ-≃
          (BishopP.∣-∣-cong
            (BishopP.+-cong
              signedEnd
              (BishopP.-‿cong BishopP.≃-refl)))
          raw)))

------------------------------------------------------------------------
-- Row-local signed wing <= row-local positive wing.
------------------------------------------------------------------------

signedWingRow :
  (left right : Nat → BishopReal.ℝ) →
  Nat → Nat → BishopReal.ℝ
signedWingRow left right count index =
  BishopReal._-_
    (BishopReal._*_
      (left index)
      (FinSum.finSum right count))
    (BishopReal._*_
      (left index)
      (FinSum.finSum right (count Nat.∸ index)))

positiveWingRow :
  (left right : Nat → BishopReal.ℝ) →
  Nat → Nat → BishopReal.ℝ
positiveWingRow left right count index =
  BishopReal._-_
    (BishopReal._*_
      (BishopReal.∣ left index ∣)
      (FinSum.finSum
        (absoluteTerms right)
        count))
    (BishopReal._*_
      (BishopReal.∣ left index ∣)
      (FinSum.finSum
        (absoluteTerms right)
        (count Nat.∸ index)))

signedWingRowAbsoluteBound :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count index →
  index Nat.< count →
  BishopReal._≤_
    (BishopReal.∣ signedWingRow left right count index ∣)
    (positiveWingRow left right count index)
signedWingRowAbsoluteBound left right count index index<count =
  let
    factor =
      BishopReal._-_
        (FinSum.finSum right count)
        (FinSum.finSum right (count Nat.∸ index))

    positiveFactor =
      BishopReal._-_
        (FinSum.finSum (absoluteTerms right) count)
        (FinSum.finSum
          (absoluteTerms right)
          (count Nat.∸ index))

    factorBound :
      BishopReal._≤_ (BishopReal.∣ factor ∣) positiveFactor
    factorBound =
      finPrefixTailAbsoluteBound
        right count index index<count

    factorNonnegative :
      BishopReal.NonNegative positiveFactor
    factorNonnegative =
      BishopP.0≤x⇒nonNegx
        (BishopP.≤-trans
          (BishopP.nonNegx⇒0≤x
            (BishopP.nonNeg∣x∣ factor))
          factorBound)

    rowFactorization :
      BishopReal._≃_
        (signedWingRow left right count index)
        (BishopReal._*_ (left index) factor)
    rowFactorization =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ a whole prefix →
          (a ⊗ whole) ⊖ (a ⊗ prefix)
          ⊜ a ⊗ (whole ⊖ prefix))
        BishopP.≃-refl
        (left index)
        (FinSum.finSum right count)
        (FinSum.finSum right (count Nat.∸ index))

    positiveFactorization :
      BishopReal._≃_
        (positiveWingRow left right count index)
        (BishopReal._*_
          (BishopReal.∣ left index ∣)
          positiveFactor)
    positiveFactorization =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ a whole prefix →
          (a ⊗ whole) ⊖ (a ⊗ prefix)
          ⊜ a ⊗ (whole ⊖ prefix))
        BishopP.≃-refl
        (BishopReal.∣ left index ∣)
        (FinSum.finSum (absoluteTerms right) count)
        (FinSum.finSum
          (absoluteTerms right)
          (count Nat.∸ index))
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm positiveFactorization)
    (BishopP.≤-respˡ-≃
      (BishopP.≃-trans
        (BishopP.∣-∣-cong rowFactorization)
        (BishopP.∣x*y∣≃∣x∣*∣y∣
          (left index)
          factor))
      (BishopP.*-monoˡ-≤-nonNeg
        factorBound
        (BishopP.nonNeg∣x∣ (left index))))

------------------------------------------------------------------------
-- Signed rectangle-minus-triangle wing <= positive rectangle-minus-triangle.
------------------------------------------------------------------------

signedWingIsRowSeries :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._-_
      (RectInside.rectangleNativeRows left right count count)
      (BishopSequence.SeriesOf
        (RectInside.triangleRow left right count)
        count))
    (BishopSequence.SeriesOf
      (signedWingRow left right count)
      count)
signedWingIsRowSeries left right count =
  Difference.finiteSeriesDifference
    (λ index →
      BishopReal._*_
        (left index)
        (FinSum.finSum right count))
    (RectInside.triangleRow left right count)
    count

positiveWingIsRowSeries :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._-_
      (RectInside.rectangleNativeRows
        (absoluteTerms left)
        (absoluteTerms right)
        count count)
      (BishopSequence.SeriesOf
        (RectInside.triangleRow
          (absoluteTerms left)
          (absoluteTerms right)
          count)
        count))
    (BishopSequence.SeriesOf
      (positiveWingRow left right count)
      count)
positiveWingIsRowSeries left right count =
  Difference.finiteSeriesDifference
    (λ index →
      BishopReal._*_
        (BishopReal.∣ left index ∣)
        (FinSum.finSum (absoluteTerms right) count))
    (RectInside.triangleRow
      (absoluteTerms left)
      (absoluteTerms right)
      count)
    count

signedWingBelowPositiveWing :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (RectInside.rectangleNativeRows left right count count)
        (BishopSequence.SeriesOf
          (RectInside.triangleRow left right count)
          count)
    ∣)
    (BishopReal._-_
      (RectInside.rectangleNativeRows
        (absoluteTerms left)
        (absoluteTerms right)
        count count)
      (BishopSequence.SeriesOf
        (RectInside.triangleRow
          (absoluteTerms left)
          (absoluteTerms right)
          count)
        count))
signedWingBelowPositiveWing left right count =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (positiveWingIsRowSeries left right count))
    (BishopP.≤-respˡ-≃
      (BishopP.∣-∣-cong
        (signedWingIsRowSeries left right count))
      (BishopP.≤-trans
        (AbsSum.finiteSeriesAbsoluteBound
          (signedWingRow left right count)
          count)
        (RectInside.finitePointwiseBound count
          (λ index index<count →
            signedWingRowAbsoluteBound
              left right count index index<count))))

------------------------------------------------------------------------
-- Positive square wing <= positive Cauchy triangle tail.
------------------------------------------------------------------------

positiveWingBelowTriangleTail :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≤_
    (BishopReal._-_
      (Rectangle.rectangleSum
        (absoluteTerms left)
        (absoluteTerms right)
        count count)
      (Row.trianglePartial
        (absoluteTerms left)
        (absoluteTerms right)
        count))
    (BishopReal._-_
      (Row.trianglePartial
        (absoluteTerms left)
        (absoluteTerms right)
        (count + count))
      (Row.trianglePartial
        (absoluteTerms left)
        (absoluteTerms right)
        count))
positiveWingBelowTriangleTail left right count =
  BishopP.+-mono-≤
    (RectInside.rectangleInsideTriangle
      (λ index → BishopP.nonNeg∣x∣ (left index))
      (λ index → BishopP.nonNeg∣x∣ (right index))
      count count)
    BishopP.≤-refl

------------------------------------------------------------------------
-- Final finite Mertens wing estimate.
------------------------------------------------------------------------

finiteCauchyWingAbsoluteBound :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (Rectangle.rectangleSum left right count count)
        (Row.trianglePartial left right count)
    ∣)
    (BishopReal._-_
      (Row.trianglePartial
        (absoluteTerms left)
        (absoluteTerms right)
        (count + count))
      (Row.trianglePartial
        (absoluteTerms left)
        (absoluteTerms right)
        count))
finiteCauchyWingAbsoluteBound left right count =
  let
    signedToRows :
      BishopReal._≃_
        (BishopReal._-_
          (Rectangle.rectangleSum left right count count)
          (Row.trianglePartial left right count))
        (BishopReal._-_
          (RectInside.rectangleNativeRows left right count count)
          (BishopSequence.SeriesOf
            (RectInside.triangleRow left right count)
            count))
    signedToRows =
      BishopP.+-cong
        (RectInside.rectangleSumIsNativeRows
          left right count count)
        (BishopP.-‿cong
          (BishopP.≃-trans
            (Row.triangleIsMertensRow left right count)
            (BishopP.≃-symm
              (RectInside.allRowsIsMertensRow
                left right count))))

    positiveRowsToStandard :
      BishopReal._≃_
        (BishopReal._-_
          (RectInside.rectangleNativeRows
            (absoluteTerms left)
            (absoluteTerms right)
            count count)
          (BishopSequence.SeriesOf
            (RectInside.triangleRow
              (absoluteTerms left)
              (absoluteTerms right)
              count)
            count))
        (BishopReal._-_
          (Rectangle.rectangleSum
            (absoluteTerms left)
            (absoluteTerms right)
            count count)
          (Row.trianglePartial
            (absoluteTerms left)
            (absoluteTerms right)
            count))
    positiveRowsToStandard =
      BishopP.+-cong
        (BishopP.≃-symm
          (RectInside.rectangleSumIsNativeRows
            (absoluteTerms left)
            (absoluteTerms right)
            count count))
        (BishopP.-‿cong
          (BishopP.≃-trans
            (RectInside.allRowsIsMertensRow
              (absoluteTerms left)
              (absoluteTerms right)
              count)
            (BishopP.≃-symm
              (Row.triangleIsMertensRow
                (absoluteTerms left)
                (absoluteTerms right)
                count))))
  in
  BishopP.≤-trans
    (BishopP.≤-respˡ-≃
      (BishopP.∣-∣-cong signedToRows)
      (BishopP.≤-respʳ-≃
        positiveRowsToStandard
        (signedWingBelowPositiveWing left right count)))
    (positiveWingBelowTriangleTail left right count)
