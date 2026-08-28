module DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact where

------------------------------------------------------------------------
-- NONNEGATIVE RECTANGLES SIT INSIDE A LARGER CAUCHY TRIANGLE
--
-- If a_i,b_j >= 0, then for all H,W,
--
--   (sum_{i<H} a_i) (sum_{j<W} b_j)
--       <= sum_{n<H+W} sum_{k<=n} a_k b_{n-k}.
--
-- The proof is row-wise.  For i<H the triangle row has right-prefix length
-- (H+W)-i >= W.  Nonnegative partial sums are monotone, and the remaining
-- triangle rows are nonnegative.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as NatP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
open import DASHI.Physics.YangMills.CompactLieProofLevel

rightBelowLeftPlus : ∀ left right → right ℕ.≤ left + right
rightBelowLeftPlus zero right = NatP.≤-refl
rightBelowLeftPlus (suc left) right =
  NatP.≤-step (rightBelowLeftPlus left right)

widthFitsTriangleRow :
  ∀ {height index} width →
  index ℕ.< height →
  width ℕ.≤ (height + width) ℕ.∸ index
widthFitsTriangleRow {zero} width ()
widthFitsTriangleRow {suc height} {zero} width index<height =
  rightBelowLeftPlus (suc height) width
widthFitsTriangleRow {suc height} {suc index} width (ℕ.s≤s index<height) =
  widthFitsTriangleRow {height} {index} width index<height

finitePointwiseBound :
  ∀ {left right : Nat → BishopReal.ℝ} →
  ∀ count →
  (∀ index → index ℕ.< count →
    BishopReal._≤_ (left index) (right index)) →
  BishopReal._≤_
    (BishopSequence.SeriesOf left count)
    (BishopSequence.SeriesOf right count)
finitePointwiseBound zero bound = BishopP.≤-refl
finitePointwiseBound {left} {right} (suc count) bound =
  BishopP.+-mono-≤
    (finitePointwiseBound count
      (λ index index<count →
        bound index (NatP.<-trans index<count (NatP.n<1+n count))))
    (bound count NatP.n<1+n)

finiteSumNonnegative :
  ∀ {terms : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal.NonNegative (terms index)) →
  ∀ count →
  BishopReal.NonNegative (BishopSequence.SeriesOf terms count)
finiteSumNonnegative termNonnegative zero = BishopP.nonNeg-refl
finiteSumNonnegative termNonnegative (suc count) =
  BishopP.nonNegx,y⇒nonNegx+y
    (finiteSumNonnegative termNonnegative count)
    (termNonnegative count)

partialSumsIncreasing :
  ∀ {terms : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal.NonNegative (terms index)) →
  BishopSequence._isIncreasing (BishopSequence.SeriesOf terms)
partialSumsIncreasing {terms} termNonnegative count =
  let partial = BishopSequence.SeriesOf terms count in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (BishopP.+-identityʳ partial))
    (BishopP.+-monoʳ-≤ partial
      (BishopP.nonNegx⇒0≤x (termNonnegative count)))

finPrefixNonnegative :
  ∀ {terms : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal.NonNegative (terms index)) →
  ∀ count →
  BishopReal.NonNegative (FinSum.finSum terms count)
finPrefixNonnegative termNonnegative count =
  BishopP.nonNeg-cong
    (BishopP.≃-symm (FinSum.finSumIsSeriesOf _ count))
    (finiteSumNonnegative termNonnegative count)

finPrefixMonotone :
  ∀ {terms : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal.NonNegative (terms index)) →
  ∀ {small large} → small ℕ.≤ large →
  BishopReal._≤_
    (FinSum.finSum terms small)
    (FinSum.finSum terms large)
finPrefixMonotone {terms} termNonnegative {small} {large} small≤large =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm (FinSum.finSumIsSeriesOf terms large))
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm (FinSum.finSumIsSeriesOf terms small))
      (BishopSequence.isIncreasing⇒isIncreasing₂
        (partialSumsIncreasing termNonnegative)
        large small small≤large))

rectangleNativeRows :
  (left right : Nat → BishopReal.ℝ) →
  Nat → Nat → BishopReal.ℝ
rectangleNativeRows left right height width =
  BishopSequence.SeriesOf
    (λ index →
      BishopReal._*_
        (left index)
        (FinSum.finSum right width))
    height

rectangleSumIsNativeRows :
  ∀ left right height width →
  BishopReal._≃_
    (Rectangle.rectangleSum left right height width)
    (rectangleNativeRows left right height width)
rectangleSumIsNativeRows left right height width =
  Ext.finiteSumCongruent
    (λ index →
      BishopP.*-congˡ
        (BishopP.≃-symm
          (FinSum.finSumIsSeriesOf right width)))
    height

triangleRow :
  (left right : Nat → BishopReal.ℝ) →
  Nat → Nat → BishopReal.ℝ
triangleRow left right total index =
  BishopReal._*_
    (left index)
    (FinSum.finSum right (total ℕ.∸ index))

rectangleRowsBelowTriangleRows :
  ∀ {left right} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ height width →
  BishopReal._≤_
    (rectangleNativeRows left right height width)
    (BishopSequence.SeriesOf
      (triangleRow left right (height + width)) height)
rectangleRowsBelowTriangleRows
    {left} {right} leftNonnegative rightNonnegative height width =
  finitePointwiseBound height
    (λ index index<height →
      BishopP.*-monoˡ-≤-nonNeg
        (finPrefixMonotone rightNonnegative
          (widthFitsTriangleRow width index<height))
        (leftNonnegative index))

triangleRowNonnegative :
  ∀ {left right} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ total index →
  BishopReal.NonNegative (triangleRow left right total index)
triangleRowNonnegative leftNonnegative rightNonnegative total index =
  BishopP.nonNegx,y⇒nonNegx*y
    (leftNonnegative index)
    (finPrefixNonnegative rightNonnegative (total ℕ.∸ index))

firstRowsBelowAllRows :
  ∀ {left right} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ height width →
  BishopReal._≤_
    (BishopSequence.SeriesOf
      (triangleRow left right (height + width)) height)
    (BishopSequence.SeriesOf
      (triangleRow left right (height + width)) (height + width))
firstRowsBelowAllRows leftNonnegative rightNonnegative height width =
  BishopSequence.isIncreasing⇒isIncreasing₂
    (partialSumsIncreasing
      (triangleRowNonnegative
        leftNonnegative rightNonnegative (height + width)))
    (height + width) height
    (NatP.m≤m+n height width)

allRowsIsMertensRow :
  ∀ left right total →
  BishopReal._≃_
    (BishopSequence.SeriesOf (triangleRow left right total) total)
    (Row.mertensRowPartial left right total)
allRowsIsMertensRow left right total =
  BishopP.≃-symm
    (FinSum.finSumIsSeriesOf
      (triangleRow left right total) total)

rectangleInsideTriangle :
  ∀ {left right} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ height width →
  BishopReal._≤_
    (Rectangle.rectangleSum left right height width)
    (Row.trianglePartial left right (height + width))
rectangleInsideTriangle
    {left} {right} leftNonnegative rightNonnegative height width =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (Row.triangleIsMertensRow left right (height + width)))
    (BishopP.≤-respʳ-≃
      (allRowsIsMertensRow left right (height + width))
      (BishopP.≤-trans
        (BishopP.≤-respˡ-≃
          (BishopP.≃-symm
            (rectangleSumIsNativeRows left right height width))
          (rectangleRowsBelowTriangleRows
            leftNonnegative rightNonnegative height width))
        (firstRowsBelowAllRows
          leftNonnegative rightNonnegative height width)))

rectangleProductInsideTriangle :
  ∀ {left right} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ height width →
  BishopReal._≤_
    (BishopReal._*_
      (BishopSequence.SeriesOf left height)
      (BishopSequence.SeriesOf right width))
    (Row.trianglePartial left right (height + width))
rectangleProductInsideTriangle
    {left} {right} leftNonnegative rightNonnegative height width =
  BishopP.≤-respˡ-≃
    (Rectangle.rectangleProduct left right height width)
    (rectangleInsideTriangle
      leftNonnegative rightNonnegative height width)

bishopFiniteRectangleInsideCauchyTriangleLevel : ProofLevel
bishopFiniteRectangleInsideCauchyTriangleLevel = machineChecked
