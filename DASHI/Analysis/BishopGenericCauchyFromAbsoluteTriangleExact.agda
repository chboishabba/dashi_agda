{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopGenericCauchyFromAbsoluteTriangleExact where

------------------------------------------------------------------------
-- K05-PRODUCT: GENERIC BISHOP REAL CAUCHY-PRODUCT CLOSURE.
--
-- Reuses the ORIGINAL Bishop rectangle product, signed finite wing,
-- and convergent-double-tail/vanishing-difference proofs. It is not
-- an extra Cauchy-product authority, not a second real carrier, and
-- not a finite-test extrapolation.
--
-- A triangle of ABSOLUTE coefficient products with a genuine Bishop
-- convergence proof suffices, with ordinary convergence of each
-- source series, to conclude the SIGNED Cauchy triangle converges
-- to the product of the two ORIGINAL Bishop-real limits.
--
-- The Round11 complex application runs this theorem four times
-- (cos/cos, sin/sin, cos/sin and sin/cos); paying the four absolute
-- triangle convergences is still a separate, factorial-specific
-- obligation. The source's signed parity/binomial coefficient
-- identity is likewise separate.
--
-- Cauchy, Bishop and Bridges; Zachary Murray and Viktor Csimma;
-- original DASHI finite wing and Bishop exponential authors.
-- Source-written, kernel pending. No declared postulates or holes.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpProduct
import DASHI.Analysis.BishopConvergentDoubleTailExact as Double
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish

absoluteTriangle :
  (left right : Nat → R.ℝ) → Nat → R.ℝ
absoluteTriangle left right =
  Row.trianglePartial
    (Wing.absoluteTerms left)
    (Wing.absoluteTerms right)

positiveWing :
  (left right : Nat → R.ℝ) → Nat → R.ℝ
positiveWing left right count =
  R._-_
    (absoluteTriangle left right (count + count))
    (absoluteTriangle left right count)

positiveDoubleTail :
  (left right : Nat → R.ℝ) → Nat → R.ℝ
positiveDoubleTail left right count =
  R._-_
    (absoluteTriangle left right (Double.double count))
    (absoluteTriangle left right count)

doubleTailIsWing :
  (left right : Nat → R.ℝ) →
  (count : Nat) →
  R._≃_
    (positiveDoubleTail left right count)
    (positiveWing left right count)
doubleTailIsWing left right count =
  RP.+-cong
    (RP.≃-refl₂
      (cong (absoluteTriangle left right)
        (ExpProduct.doubleIsAddSelf count)))
    RP.≃-refl

positiveWingConvergesZero :
  (left right : Nat → R.ℝ) →
  (limit : R.ℝ) →
  Seq._ConvergesTo_ (absoluteTriangle left right) limit →
  Seq._ConvergesTo_ (positiveWing left right) R.0ℝ
positiveWingConvergesZero left right limit converges =
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      doubleTailIsWing left right (suc count)})
    (R.0ℝ , Double.doubleTailConvergesZero converges)

rectangleConvergesToProduct :
  (left right : Nat → R.ℝ) →
  (leftLimit rightLimit : R.ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf left) leftLimit →
  Seq._ConvergesTo_ (Seq.SeriesOf right) rightLimit →
  Seq._ConvergesTo_
    (λ count → Rect.rectangleSum left right count count)
    (R._*_ leftLimit rightLimit)
rectangleConvergesToProduct
    left right leftLimit rightLimit leftConv rightConv =
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      RP.≃-symm (Rect.rectangleProduct
        left right (suc count) (suc count))})
    (R._*_ leftLimit rightLimit ,
      Seq.xₙyₙ→x₀y₀
        (leftLimit , leftConv)
        (rightLimit , rightConv))

subtractionReversal :
  (x y : R.ℝ) →
  R._≃_ (R._-_ x y) (R.-_ (R._-_ y x))
subtractionReversal x y =
  let open RP.ℝ-Solver
  in solve 2
    (λ a b → a ⊖ b ⊜ ⊝ (b ⊖ a))
    RP.≃-refl x y

reverseFiniteWingBound :
  (left right : Nat → R.ℝ) →
  (count : Nat) →
  R._≤_
    (R.∣ R._-_
      (Row.trianglePartial left right count)
      (Rect.rectangleSum left right count count) ∣)
    (R.∣ positiveWing left right count ∣)
reverseFiniteWingBound left right count =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.≃-trans
        (RP.∣-∣-cong
          (subtractionReversal
            (Row.trianglePartial left right count)
            (Rect.rectangleSum left right count count)))
        RP.∣-x∣≃∣x∣))
    (RP.≤-trans
      (Wing.finiteCauchyWingAbsoluteBound left right count)
      (RP.x≤∣x∣ {x = positiveWing left right count}))

-- The generic analytic step is genuinely discharged by the already
-- proved Bishop signed-wing and convergence machinery. The absolute
-- triangle premise is the exact single remaining source-specific
-- analytic input, not an opaque "CauchyProductAuthority" record.
cauchyTriangleConvergesToActualProduct :
  (left right : Nat → R.ℝ) →
  (leftLimit rightLimit absoluteLimit : R.ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf left) leftLimit →
  Seq._ConvergesTo_ (Seq.SeriesOf right) rightLimit →
  Seq._ConvergesTo_ (absoluteTriangle left right) absoluteLimit →
  Seq._ConvergesTo_
    (Row.trianglePartial left right)
    (R._*_ leftLimit rightLimit)
cauchyTriangleConvergesToActualProduct
    left right leftLimit rightLimit absoluteLimit
    leftConv rightConv absoluteConv =
  Vanish.vanishingDifferenceConvergence
    (rectangleConvergesToProduct
      left right leftLimit rightLimit leftConv rightConv)
    (positiveWingConvergesZero
      left right absoluteLimit absoluteConv)
    (reverseFiniteWingBound left right)
