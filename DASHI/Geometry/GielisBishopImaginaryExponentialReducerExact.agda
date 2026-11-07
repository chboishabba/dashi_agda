{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisBishopImaginaryExponentialReducerExact where

------------------------------------------------------------------------
-- One genuine analytic producer replaces multiple Bishop trig assumptions.
--
-- The ACTUAL Bishop trig sine/cosine comes from
-- Round11.dataSet P, already backed by factorial power-series convergence.
-- Its imaginary-axis exponential value is (cos_B x,sin_B x) in the
-- ORIGINAL BishopSetoidComplexExact algebra.
--
-- A SINGLE same-object multiplicativity input
--   E(i(2x)) ~ E(ix)*E(ix)
-- is enough to derive native cos(2x) and sin(2x) identities.
-- Applying this again at 2x and transporting 4x = 2(2x)
-- yields the Gielis quadruple-angle formula via the original
-- Bishop polynomial and Pythagorean seam.
--
-- Existing BishopExponentialCauchyProductExact.bishopExpAdd is a
-- REAL exponential theorem, a donor but NOT an automatic proof of the
-- complex imaginary-axis input. The genuinely complex series
-- product/series identification is the sole remaining analytic root.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Round11
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as Shared
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Trig
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Foundations.BishopExponentialCauchyProductExact as RealExp
import DASHI.Geometry.GielisBishopPolynomialExact as Gielis

imaginaryAxisTrigExp :
  (dataSet : Trig.BishopElementaryPowerSeriesData) →
  Bishop.ℝ → Complex.BishopComplex
imaginaryAxisTrigExp dataSet angle =
  Complex.complex
    (Trig.bishopCos dataSet angle)
    (Trig.bishopSin dataSet angle)

record ImaginaryAxisSameSourceExponentialDoubling
    (P : Round11.Round11FactorInterchangeProblem) : Set₁ where
  field
    -- A FUNCTIONAL analytic same-object claim, not merely a supplied
    -- syntactic exponential label.
    twiceIsProduct :
      ∀ angle →
      Complex._≈C_
        (imaginaryAxisTrigExp
          (Round11.dataSet P)
          (Bishop._*_ Gielis.two angle))
        (Complex._*C_
          (imaginaryAxisTrigExp (Round11.dataSet P) angle)
          (imaginaryAxisTrigExp (Round11.dataSet P) angle))

open ImaginaryAxisSameSourceExponentialDoubling public

sineProductEqualsDouble :
  ∀ c s →
  Bishop._≃_
    (Bishop._+_
      (Bishop._*_ c s)
      (Bishop._*_ s c))
    (Gielis.bishopSineDoublePolynomial c s)
sineProductEqualsDouble c s =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ a b →
       (((a ⊗ b) ⊕ (b ⊗ a))
       ⊜
       (Κ (+ 2 / 1) ⊗ (a ⊗ b))))
    BishopP.≃-refl c s

cosineDoubleFromImaginaryExponential :
  ∀ P →
  ImaginaryAxisSameSourceExponentialDoubling P →
  ∀ angle →
  Bishop._≃_
    (Trig.bishopCos (Round11.dataSet P)
      (Bishop._*_ Gielis.two angle))
    (Gielis.bishopCosineDoublePolynomial
      (Trig.bishopCos (Round11.dataSet P) angle)
      (Trig.bishopSin (Round11.dataSet P) angle))
cosineDoubleFromImaginaryExponential P W angle =
  Complex.reEquivalent (twiceIsProduct W angle)

sineDoubleFromImaginaryExponential :
  ∀ P →
  ImaginaryAxisSameSourceExponentialDoubling P →
  ∀ angle →
  Bishop._≃_
    (Trig.bishopSin (Round11.dataSet P)
      (Bishop._*_ Gielis.two angle))
    (Gielis.bishopSineDoublePolynomial
      (Trig.bishopCos (Round11.dataSet P) angle)
      (Trig.bishopSin (Round11.dataSet P) angle))
sineDoubleFromImaginaryExponential P W angle =
  BishopP.≃-trans
    (Complex.imEquivalent (twiceIsProduct W angle))
    (sineProductEqualsDouble
      (Trig.bishopCos (Round11.dataSet P) angle)
      (Trig.bishopSin (Round11.dataSet P) angle))

fourIsTwiceTwice :
  ∀ angle →
  Bishop._≃_
    (Bishop._*_ Gielis.four angle)
    (Bishop._*_ Gielis.two
      (Bishop._*_ Gielis.two angle))
fourIsTwiceTwice angle =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x →
      ((Κ (+ 4 / 1) ⊗ x)
       ⊜ (Κ (+ 2 / 1) ⊗ (Κ (+ 2 / 1) ⊗ x))))
    BishopP.≃-refl angle

concreteDoubleAngleInputsFromImaginaryExp :
  ∀ P angle →
  ImaginaryAxisSameSourceExponentialDoubling P →
  Gielis.BishopConcreteDoubleAngleInputs
    (Round11.dataSet P) angle
concreteDoubleAngleInputsFromImaginaryExp P angle W = record
  { Gielis.BishopConcreteDoubleAngleInputs.cosineAtDouble =
      cosineDoubleFromImaginaryExponential P W angle
  ; Gielis.BishopConcreteDoubleAngleInputs.sineAtDouble =
      sineDoubleFromImaginaryExponential P W angle
  ; Gielis.BishopConcreteDoubleAngleInputs.cosineAtFourFromTwo =
      BishopP.≃-trans
        (TrigCong.bishopCosCongruent
          (Round11.termIdentification P)
          (fourIsTwiceTwice angle))
        (cosineDoubleFromImaginaryExponential P W
          (Bishop._*_ Gielis.two angle))
  }

gielisRound11FromOneImaginaryExponentialLaw :
  ∀ (P : Round11.Round11FactorInterchangeProblem) →
  Shared.Round11ClassicalTrigObjectWeld P →
  ImaginaryAxisSameSourceExponentialDoubling P →
  ∀ angle →
  Bishop._≃_
    (Bishop._*_ Gielis.four
      (Gielis.gielisFourthSum
        (Trig.bishopCos (Round11.dataSet P) angle)
        (Trig.bishopSin (Round11.dataSet P) angle)))
    (Bishop._+_ Gielis.three
      (Trig.bishopCos (Round11.dataSet P)
        (Bishop._*_ Gielis.four angle)))
gielisRound11FromOneImaginaryExponentialLaw P trigWeld expWeld angle =
  Gielis.bishopGielisFromPythagoreanAndTwoDoubleAngles
    (Round11.dataSet P) angle
    (Gielis.bishopGielisPythagoreanFromSharedWeld P trigWeld angle)
    (concreteDoubleAngleInputsFromImaginaryExp P angle expWeld)

-- Explicit donor evidence, not an invalid promotion to complex exp:
realBishopExpAddAlreadyProved :
  ∀ left right →
  Bishop._≃_
    (DASHI.Foundations.BishopExponentialSeriesConvergenceExact.bishopExp
      (Bishop._+_ left right))
    (Bishop._*_
      (DASHI.Foundations.BishopExponentialSeriesConvergenceExact.bishopExp left)
      (DASHI.Foundations.BishopExponentialSeriesConvergenceExact.bishopExp right))
realBishopExpAddAlreadyProved = RealExp.bishopExpAdd
