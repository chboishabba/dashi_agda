module DASHI.Moonshine.AbelBishopNewtonSelectedSinePositiveExact where

------------------------------------------------------------------------
-- SELECTED BISHOP SIN(133724/100000) POSITIVE: LITERAL SOURCE TERMS.
--
-- The existing general sine interlacing theorem in the YM/Bishop lane
-- accepts nonnegative magnitudes decreasing in Nat, with original
-- factorial terms identified by ConcreteSineCosineTermIdentification.
-- Its old half-radius SPECIALIZATION is insufficient for 1.33724.
--
-- At this exact rational y0, (|y0|^2)/6 < 1/3, hence the original
-- factorial recurrence proves decreasing magnitudes for ALL Nat.
-- The original alternating bracket then gives
--
--     y0 - y0^3/6 <= bishopSin(dataSet,y0).
--
-- The explicit rational cubic lower polynomial is strictly positive,
-- providing the actual Newton denominator nonzero certificate
-- on the SAME Bishop setoid carrier, no derivative axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base as ℤ using (+_)
import Data.Nat.Properties as ℕP
open import Data.Rational.Unnormalised as ℚ using
  (0ℚᵘ; 1ℚᵘ; _/_; _*_; _-_)
import Data.Rational.Unnormalised.Properties as RatP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact as Ratios
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopConcreteFactorialCoefficientDischargeExact as Factorial
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Brackets
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Taylor
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonCenterDenominatorExact as Center

selectedSineRational : ℚ.ℚᵘ
selectedSineRational = + 133724 / 100000

selectedSineRatioRational : ℚ.ℚᵘ
selectedSineRatioRational =
  (selectedSineRational * selectedSineRational) * (+ 1 / 6)

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

selectedSineSourceRatioIsRational :
  BishopReal._≃_
    (Ratios.bishopSineSuccessiveMagnitudeRatio
      Center.bishopNewtonCenterImag)
    (BishopReal._⋆ selectedSineRatioRational)
selectedSineSourceRatioIsRational =
  let
    y = Center.bishopNewtonCenterImag
    squareIsRaw =
      BishopP.≃-trans
        (BishopP.*-cong
          selectedSineAbsIsSelf selectedSineAbsIsSelf)
        (BishopP.≃-symm
          (BishopP.⋆-distrib-*
            selectedSineRational selectedSineRational))
  in
  BishopP.≃-trans
    (BishopP.*-cong squareIsRaw BishopP.≃-refl)
    (BishopP.≃-symm
      (BishopP.⋆-distrib-*
        (selectedSineRational * selectedSineRational)
        (+ 1 / 6)))

selectedSineSourceRatioStrictlyBelowOne :
  BishopReal._<_
    (Ratios.bishopSineSuccessiveMagnitudeRatio
      Center.bishopNewtonCenterImag)
    BishopReal.1ℝ
selectedSineSourceRatioStrictlyBelowOne =
  BishopP.<-respˡ-≃
    selectedSineSourceRatioIsRational
    (BishopP.p<q⇒p⋆<q⋆
      selectedSineRatioRational 1ℚᵘ
      (ℚ.*<* (ℤ.+<+ (ℕP.≤ᵇ⇒≤ tt))))

selectedSineSourceRatioBelowOne :
  BishopReal._≤_
    (Ratios.bishopSineSuccessiveMagnitudeRatio
      Center.bishopNewtonCenterImag)
    BishopReal.1ℝ
selectedSineSourceRatioBelowOne =
  BishopP.<⇒≤ selectedSineSourceRatioStrictlyBelowOne

selectedSineMagnitudeDecreases :
  ∀ n →
  BishopReal._≤_
    (Recurrence.sineMagnitudeTerm
      Center.bishopNewtonCenterImag (suc n))
    (Recurrence.sineMagnitudeTerm
      Center.bishopNewtonCenterImag n)
selectedSineMagnitudeDecreases n =
  let
    y = Center.bishopNewtonCenterImag
    m = Recurrence.sineMagnitudeTerm y n
  in
  BishopP.≤-trans
    (Recurrence.sineSuccessorBelowCoarseRatio
      Factorial.concreteFactorialCoefficientStepBounds y n)
    (BishopP.≤-respʳ-≃
      (BishopP.*-identityˡ m)
      (BishopP.*-monoʳ-≤-nonNeg
        selectedSineSourceRatioBelowOne
        (Recurrence.sineMagnitudeTermNonnegative y n)))

selectedSineAlternatingSource :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  Alternating.AlternatingDecreasingSeriesData
selectedSineAlternatingSource T =
  let
    dataSet = Cartesian.dataSet T
    y = Center.bishopNewtonCenterImag
  in
  record
    { term = Elementary.sineTerm dataSet y
    ; magnitude = Recurrence.sineMagnitudeTerm y
    ; representedLimit = Elementary.bishopSin dataSet y
    ; magnitudeNonnegative = Recurrence.sineMagnitudeTermNonnegative y
    ; magnitudeDecreasing = selectedSineMagnitudeDecreases
    ; evenTermIsPositiveMagnitude = λ index →
        BishopP.≃-trans
          (Terms.sineTermIsConcrete
            (Cartesian.trigIdentification T)
            y (Alternating.double index))
          (Concrete.sineSignedEvenIsMagnitude
            y selectedSineRationalNonnegative index)
    ; oddTermIsNegativeMagnitude = λ index →
        BishopP.≃-trans
          (Terms.sineTermIsConcrete
            (Cartesian.trigIdentification T)
            y (suc (Alternating.double index)))
          (Concrete.sineSignedOddIsNegativeMagnitude
            y selectedSineRationalNonnegative index)
    ; seriesConvergesToRepresentedLimit =
        Elementary.bishopSinConvergence dataSet y
    }

selectedSineInterlacing :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  Brackets.BishopAlternatingInterlacingData
selectedSineInterlacing T =
  Alternating.alternatingInterlacingData
    (selectedSineAlternatingSource T)

selectedSineSourceTermZeroIsY :
  ∀ T →
  BishopReal._≃_
    (Elementary.sineTerm (Cartesian.dataSet T)
      Center.bishopNewtonCenterImag zero)
    Center.bishopNewtonCenterImag
selectedSineSourceTermZeroIsY T =
  let y = Center.bishopNewtonCenterImag in
  BishopP.≃-trans
    (Terms.sineTermIsConcrete
      (Cartesian.trigIdentification T) y zero)
    (BishopP.≃-trans
      (Concrete.sineSignedEvenIsMagnitude
        y selectedSineRationalNonnegative zero)
      (Taylor.sineMagnitudeZeroEquivalentValue
        y selectedSineRationalNonnegative))

selectedSineSourceTermOneIsNegativeCubic :
  ∀ T →
  BishopReal._≃_
    (Elementary.sineTerm (Cartesian.dataSet T)
      Center.bishopNewtonCenterImag (suc zero))
    (BishopReal.- (Taylor.sineCubicTerm
      Center.bishopNewtonCenterImag))
selectedSineSourceTermOneIsNegativeCubic T =
  let y = Center.bishopNewtonCenterImag in
  BishopP.≃-trans
    (Terms.sineTermIsConcrete
      (Cartesian.trigIdentification T) y (suc zero))
    (BishopP.≃-trans
      (Concrete.sineSignedOddIsNegativeMagnitude
        y selectedSineRationalNonnegative zero)
      (BishopP.-‿cong
        (Taylor.sineMagnitudeOneEquivalentCubic
          y selectedSineRationalNonnegative)))

selectedSineLowerPartialIsCubic :
  ∀ T →
  BishopReal._≃_
    (Brackets.nextLowerPartial (selectedSineInterlacing T) zero)
    (BishopReal._-_
      Center.bishopNewtonCenterImag
      (Taylor.sineCubicTerm Center.bishopNewtonCenterImag))
selectedSineLowerPartialIsCubic T =
  let
    y = Center.bishopNewtonCenterImag
    c = Taylor.sineCubicTerm y
    first = selectedSineSourceTermZeroIsY T
    second = selectedSineSourceTermOneIsNegativeCubic T
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.+-cong BishopP.≃-refl first)
      second)
    (let open BishopP.ℝ-Solver in
     solve 2
       (λ x cube → (Κ 0ℚᵘ ⊕ x) ⊕ (⊝ cube)
         ⊜ x ⊖ cube)
       BishopP.≃-refl y c)

selectedSineLowerPolynomialFactorization :
  BishopReal._≃_
    (BishopReal._-_
      Center.bishopNewtonCenterImag
      (Taylor.sineCubicTerm Center.bishopNewtonCenterImag))
    (BishopReal._*_
      Center.bishopNewtonCenterImag
      (BishopReal._-_
        BishopReal.1ℝ
        (Ratios.bishopSineSuccessiveMagnitudeRatio
          Center.bishopNewtonCenterImag)))
selectedSineLowerPolynomialFactorization =
  let
    y = Center.bishopNewtonCenterImag
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 1
      (λ x →
        x ⊖ (Κ (+ 1 / 6) ⊗ ((x ⊗ x) ⊗ x))
        ⊜ x ⊗ (Κ 1ℚᵘ ⊖ ((x ⊗ x) ⊗ Κ (+ 1 / 6))))
      BishopP.≃-refl y)
    (BishopP.*-cong
      BishopP.≃-refl
      (BishopP.+-cong
        BishopP.≃-refl
        (BishopP.-‿cong
          (BishopP.*-cong
            (BishopP.*-cong
              (BishopP.≃-symm selectedSineAbsIsSelf)
              (BishopP.≃-symm selectedSineAbsIsSelf))
            BishopP.≃-refl))))

selectedSineCubicIsStrictlyPositive :
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._-_
      Center.bishopNewtonCenterImag
      (Taylor.sineCubicTerm Center.bishopNewtonCenterImag))
selectedSineCubicIsStrictlyPositive =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm selectedSineLowerPolynomialFactorization)
    (BishopP.posx⇒0<x
      (BishopP.posx,y⇒posx*y
        (BishopP.0<x⇒posx
          (BishopP.p<q⇒p⋆<q⋆
            0ℚᵘ selectedSineRational
            (RatP.positive⁻¹ selectedSineRational)))
        (BishopP.0<x⇒posx
          (BishopP.x<y⇒0<y-x
            (Ratios.bishopSineSuccessiveMagnitudeRatio
              Center.bishopNewtonCenterImag)
            BishopReal.1ℝ
            selectedSineSourceRatioStrictlyBelowOne))))

selectedOriginalBishopSineAtNewtonCenterPositive :
  ∀ T →
  BishopReal._<_ BishopReal.0ℝ
    (Elementary.bishopSin
      (Cartesian.dataSet T)
      Center.bishopNewtonCenterImag)
selectedOriginalBishopSineAtNewtonCenterPositive T =
  BishopP.<-≤-trans
    selectedSineCubicIsStrictlyPositive
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm
        (selectedSineLowerPartialIsCubic T))
      (Brackets.nextLowerPartialBelowRepresentedLimit
        (selectedSineInterlacing T) zero))

originalBishopNewtonDenominatorNonzeroFromSource :
  ∀ T →
  Reciprocal.BishopComplexNonzero
    (Newton.originalBishopNewtonDenominator T)
originalBishopNewtonDenominatorNonzeroFromSource T =
  Center.bishopNewtonDenominatorNonzeroFromOriginalSine
    T
    (selectedOriginalBishopSineAtNewtonCenterPositive T)
