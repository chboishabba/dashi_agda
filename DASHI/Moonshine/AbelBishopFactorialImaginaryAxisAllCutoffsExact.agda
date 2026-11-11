module DASHI.Moonshine.AbelBishopFactorialImaginaryAxisAllCutoffsExact where

------------------------------------------------------------------------
-- P1: EVERY NATURAL CUTOFF OF THE ORIGINAL BISHOP COMPLEX
-- FACTORIAL SERIES ON THE IMAGINARY AXIS.
--
-- The finite factorial identities from the existing imaginary-axis
-- modules give both even-cutoff and odd-cutoff convergence to the
-- SAME configured Bishop cosine/sine limits. The generic two-parity
-- convergence theorem proves full sequence convergence, not merely
-- existence of convergent subsequences.
--
-- The native expC on the imaginary axis is identified by the pinned
-- Bishop real exp(0) = 1 theorem, reusing the EXISTING carrier weld.
--
-- None of these claims is kernel-accepted until the local Agda 2.9
-- --safe checker runs on the exact head.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopEvenOddFullSequenceConvergenceExact as Full
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Terms
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisFiniteReindexExact as Even
import DASHI.Moonshine.AbelBishopFactorialOddCutoffFiniteExact as Odd

originalBishopImaginaryFactorialRealAllCutoffs :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Even.factorialImaginaryRealTerm y))
    (Elementary.bishopCos (Cartesian.dataSet T) y)
originalBishopImaginaryFactorialRealAllCutoffs T y =
  Full.originalBishopEvenOddLimitsGiveAllCutoffs
    (BishopSequence.SeriesOf (Even.factorialImaginaryRealTerm y))
    (Elementary.bishopCos (Cartesian.dataSet T) y)
    (Even.originalBishopImaginaryAxisRealEvenPrefixConvergesToCosine T y)
    (Odd.originalBishopImaginaryAxisOddRealPrefixConverges T y)

originalBishopImaginaryFactorialImagAllCutoffs :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Even.factorialImaginaryImagTerm y))
    (Elementary.bishopSin (Cartesian.dataSet T) y)
originalBishopImaginaryFactorialImagAllCutoffs T y =
  Full.originalBishopEvenOddLimitsGiveAllCutoffs
    (BishopSequence.SeriesOf (Even.factorialImaginaryImagTerm y))
    (Elementary.bishopSin (Cartesian.dataSet T) y)
    (Even.originalBishopImaginaryAxisImagEvenPrefixConvergesToSine T y)
    (Odd.originalBishopImaginaryAxisOddImagPrefixConverges T y)

originalBishopImaginaryFactorialComplexAllCutoffs :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  Complex.ComplexSeriesConvergesTo
    (Terms.originalBishopFactorialComplexTerm (Axis.imaginaryAxis y))
    (Complex.complex
      (Elementary.bishopCos (Cartesian.dataSet T) y)
      (Elementary.bishopSin (Cartesian.dataSet T) y))
originalBishopImaginaryFactorialComplexAllCutoffs T y =
  Complex.complex-series-converges-to
    (originalBishopImaginaryFactorialRealAllCutoffs T y)
    (originalBishopImaginaryFactorialImagAllCutoffs T y)

originalBishopNativeExpImaginaryAxisIsEuler :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  Complex._≈C_
    (Weld.originalBishopExpOnSeries T (Axis.imaginaryAxis y))
    (Complex.complex
      (Elementary.bishopCos (Cartesian.dataSet T) y)
      (Elementary.bishopSin (Cartesian.dataSet T) y))
originalBishopNativeExpImaginaryAxisIsEuler T y =
  (BishopP.≃-trans
    (BishopP.*-congʳ ExpOrder.bishopExpZero)
    (let open BishopP.ℝ-Solver in
     solve 1 (λ c → Κ 1ℚᵘ ⊗ c ⊜ c)
       BishopP.≃-refl
       (Elementary.bishopCos (Cartesian.dataSet T) y)))
  ,
  (BishopP.≃-trans
    (BishopP.*-congʳ ExpOrder.bishopExpZero)
    (let open BishopP.ℝ-Solver in
     solve 1 (λ s → Κ 1ℚᵘ ⊗ s ⊜ s)
       BishopP.≃-refl
       (Elementary.bishopSin (Cartesian.dataSet T) y)))

originalBishopImaginaryFactorialIsNativeExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  Complex.ComplexSeriesConvergesTo
    (Terms.originalBishopFactorialComplexTerm (Axis.imaginaryAxis y))
    (Weld.originalBishopExpOnSeries T (Axis.imaginaryAxis y))
originalBishopImaginaryFactorialIsNativeExp T y =
  Complex.complex-series-converges-to
    (BishopSequence.xₙ→x∧x≃y⇒xₙ→y
      (originalBishopImaginaryFactorialRealAllCutoffs T y)
      (BishopP.≃-symm
        (proj₁ (originalBishopNativeExpImaginaryAxisIsEuler T y))))
    (BishopSequence.xₙ→x∧x≃y⇒xₙ→y
      (originalBishopImaginaryFactorialImagAllCutoffs T y)
      (BishopP.≃-symm
        (proj₂ (originalBishopNativeExpImaginaryAxisIsEuler T y))))
