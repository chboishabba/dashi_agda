module DASHI.Moonshine.AbelBishopNewtonSelectedSinePositiveExact where

------------------------------------------------------------------------
-- SELECTED NEWTON SINE: PAY THE LEAF USING EXISTING TWO-BALL OWNER.
--
-- Original mathematical owner:
--  BalabanBishopSineTwoBallCubicLowerExact.sineCubicLowerTwoBall
-- proves the ACTUAL Bishop sine bound x-x^3/6 <= sine_B(x) for
-- every nonnegative |x|<=2, from the pinned concrete factorial
-- coefficient identification and constructive alternating interlacing.
--
-- This file does not rebuild that 300-line proof.  It verifies that
-- y0=133724/100000 is inside the existing ORIGINAL radius-two chart,
-- that its cubic lower polynomial is strictly positive by exact
-- rational evaluation, then constructs the native complex reciprocal
-- of expC(31813/100000+i*y0)-1 via existing norm-square positivity.
--
-- Source written; local Agda acceptance must be checked separately.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
import Data.Nat.Properties as ℕP
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as NatFraction
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _*_; _-_)
import Data.Rational.Unnormalised.Properties as RatP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as TwoBall
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Taylor
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonCenterDenominatorExact as Center

selectedSineRational : ℚᵘ
selectedSineRational = + 133724 / 100000

selectedSineCubicLowerRational : ℚᵘ
selectedSineCubicLowerRational =
  selectedSineRational -
    (((selectedSineRational * selectedSineRational) *
      selectedSineRational) * (+ 1 / 6))

selectedSineRationalNonnegative :
  BishopReal.NonNegative Center.bishopNewtonCenterImag
selectedSineRationalNonnegative =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (BishopP.p<q⇒p⋆<q⋆
        0ℚᵘ selectedSineRational
        (RatP.positive⁻¹ selectedSineRational)))

selectedSineAbsIsSelf :
  BishopReal._≃_
    (BishopReal.∣_∣ Center.bishopNewtonCenterImag)
    Center.bishopNewtonCenterImag
selectedSineAbsIsSelf =
  BishopP.nonNegx⇒∣x∣≃x selectedSineRationalNonnegative

selectedSineRationalBelowTwo :
  BishopReal._≤_
    Center.bishopNewtonCenterImag TwoBall.bishopTwo
selectedSineRationalBelowTwo =
  BishopP.p≤q⇒p⋆≤q⋆
    selectedSineRational TwoBall.two
    (NatFraction.natFractionLe (ℕP.≤ᵇ⇒≤ tt))

selectedSineInsideTwoBall :
  BishopReal._≤_
    (BishopReal.∣_∣ Center.bishopNewtonCenterImag)
    TwoBall.bishopTwo
selectedSineInsideTwoBall =
  BishopP.≤-respˡ-≃
    selectedSineAbsIsSelf selectedSineRationalBelowTwo

selectedOriginalSineTwoBall :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  TwoBall.ConcreteTwoBallSineInputs
    (Cartesian.dataSet T) Center.bishopNewtonCenterImag
selectedOriginalSineTwoBall T = record
  { TwoBall.termIdentification = Cartesian.trigIdentification T
  ; TwoBall.valueNonnegative = selectedSineRationalNonnegative
  ; TwoBall.insideTwo = selectedSineInsideTwoBall
  }

selectedSineCubicLowerEquivalentRational :
  BishopReal._≃_
    (BishopReal._-_
      Center.bishopNewtonCenterImag
      (Taylor.sineCubicTerm Center.bishopNewtonCenterImag))
    (BishopReal._⋆ selectedSineCubicLowerRational)
selectedSineCubicLowerEquivalentRational =
  let open BishopP.ℝ-Solver in
  solve 0
    ((Κ selectedSineRational) ⊖
      (Κ (+ 1 / 6) ⊗
        (((Κ selectedSineRational) ⊗ (Κ selectedSineRational))
          ⊗ (Κ selectedSineRational)))
      ⊜ Κ selectedSineCubicLowerRational)
    BishopP.≃-refl

selectedSineCubicStrictPositive :
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._-_
      Center.bishopNewtonCenterImag
      (Taylor.sineCubicTerm Center.bishopNewtonCenterImag))
selectedSineCubicStrictPositive =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm selectedSineCubicLowerEquivalentRational)
    (BishopP.p<q⇒p⋆<q⋆
      0ℚᵘ selectedSineCubicLowerRational
      (RatP.positive⁻¹ selectedSineCubicLowerRational))

selectedOriginalBishopSineAtNewtonCenterPositive :
  ∀ T →
  BishopReal._<_ BishopReal.0ℝ
    (Elementary.bishopSin
      (Cartesian.dataSet T)
      Center.bishopNewtonCenterImag)
selectedOriginalBishopSineAtNewtonCenterPositive T =
  BishopP.<-≤-trans
    selectedSineCubicStrictPositive
    (TwoBall.sineCubicLowerTwoBall
      (selectedOriginalSineTwoBall T))

originalBishopNewtonDenominatorNonzeroFromSource :
  ∀ T →
  Reciprocal.BishopComplexNonzero
    (Newton.originalBishopNewtonDenominator T)
originalBishopNewtonDenominatorNonzeroFromSource T =
  Center.bishopNewtonDenominatorNonzeroFromOriginalSine
    T (selectedOriginalBishopSineAtNewtonCenterPositive T)
