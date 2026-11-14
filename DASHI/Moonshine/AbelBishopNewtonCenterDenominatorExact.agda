module DASHI.Moonshine.AbelBishopNewtonCenterDenominatorExact where

------------------------------------------------------------------------
-- SAME BISHOP EXPONENTIAL: NEWTON DENOMINATOR NONZERO FROM SINE.
--
-- At c=31813/100000+i*133724/100000,
--    Im(expC(c)-1)=exp_B(31813/100000)*sin_B(133724/100000).
--
-- The original constructive Bishop exponential is already known
-- positive at positive inputs (BishopExponentialPositiveOrderExact);
-- an actual positive original sine value at this specific rational
-- argument therefore proves that expC(c)-1 has POSITIVE imaginary
-- coordinate and hence POSITIVE normSq. Reuse the original
-- BishopComplexNonzeroFromComponentExact, not a new inverse package.
--
-- ONE genuinely unpaid source leaf: positivity of literal Bishop sin
-- at rational 133724/100000 for the selected concrete dataSet.
-- The Python Fraction Taylor certificate is evidence for that leaf,
-- not its Agda proof.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as RatP
open import Data.Sum.Base using (inj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as Nonzero
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton

bishopNewtonCenterReal : BishopReal.ℝ
bishopNewtonCenterReal =
  BishopReal._⋆ (+ 31813 / 100000)

bishopNewtonCenterImag : BishopReal.ℝ
bishopNewtonCenterImag =
  BishopReal._⋆ (+ 133724 / 100000)

bishopNewtonCenterRealPositive :
  BishopReal._<_ BishopReal.0ℝ bishopNewtonCenterReal
bishopNewtonCenterRealPositive =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ (+ 31813 / 100000)
    (RatP.positive⁻¹ (+ 31813 / 100000))

bishopNewtonOnePositive :
  BishopReal._<_ BishopReal.0ℝ BishopReal.1ℝ
bishopNewtonOnePositive =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ 1ℚᵘ
    (RatP.positive⁻¹ 1ℚᵘ)

bishopNewtonCenterExpPositive :
  BishopReal._<_ BishopReal.0ℝ
    (Exp.bishopExp bishopNewtonCenterReal)
bishopNewtonCenterExpPositive =
  BishopP.<-≤-trans
    bishopNewtonOnePositive
    (ExpOrder.bishopExpAtLeastOneOnNonnegative
      (BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx bishopNewtonCenterRealPositive)))

bishopNewtonDenominatorImagIsExpTimesSine :
  ∀ T →
  BishopReal._≃_
    (Complex.im (Newton.originalBishopNewtonDenominator T))
    (BishopReal._*_
      (Exp.bishopExp bishopNewtonCenterReal)
      (Elementary.bishopSin
        (Cartesian.dataSet T)
        bishopNewtonCenterImag))
bishopNewtonDenominatorImagIsExpTimesSine T =
  let
    product =
      BishopReal._*_
        (Exp.bishopExp bishopNewtonCenterReal)
        (Elementary.bishopSin
          (Cartesian.dataSet T)
          bishopNewtonCenterImag)
    open BishopP.ℝ-Solver
  in
  solve 1
    (λ value → value ⊖ Κ 0ℚᵘ ⊜ value)
    BishopP.≃-refl
    product

bishopNewtonDenominatorImagPositiveFromSine :
  ∀ T →
  BishopReal._<_ BishopReal.0ℝ
    (Elementary.bishopSin
      (Cartesian.dataSet T) bishopNewtonCenterImag) →
  BishopReal._<_ BishopReal.0ℝ
    (Complex.im (Newton.originalBishopNewtonDenominator T))
bishopNewtonDenominatorImagPositiveFromSine T sinePositive =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm
      (bishopNewtonDenominatorImagIsExpTimesSine T))
    (BishopP.posx⇒0<x
      (BishopP.posx,y⇒posx*y
        (BishopP.0<x⇒posx bishopNewtonCenterExpPositive)
        (BishopP.0<x⇒posx sinePositive)))

bishopNewtonDenominatorNonzeroFromOriginalSine :
  ∀ T →
  BishopReal._<_ BishopReal.0ℝ
    (Elementary.bishopSin
      (Cartesian.dataSet T) bishopNewtonCenterImag) →
  Reciprocal.BishopComplexNonzero
    (Newton.originalBishopNewtonDenominator T)
bishopNewtonDenominatorNonzeroFromOriginalSine T sinePositive =
  Nonzero.complexNonzeroFromImagApart
    (inj₂
      (bishopNewtonDenominatorImagPositiveFromSine
        T sinePositive))
