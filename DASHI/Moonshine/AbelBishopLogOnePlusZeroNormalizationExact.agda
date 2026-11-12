module DASHI.Moonshine.AbelBishopLogOnePlusZeroNormalizationExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE BISHOP LOCAL LOG SERIES NORMALIZATION AT w=0.
--
-- For every n, the literal selected source coefficient
--   (-1)^n * 0^(n+1)/(n+1)  is exactly zero (componentwise).
-- Consequently its absolute coordinate series genuinely converge
-- (to zero) on the pinned Bishop carrier; the *canonical* absolute
-- series limit at the zero displacement equals zero:
--
--            LogOnePlusSeries(0) ≈C 0.
--
-- No local radius, log branch inverse, classical differentiation,
-- or postulate is introduced. This is only the exact log(1)=0
-- normalization, not exp(log(z))=z.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisFiniteReindexExact as Zero
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log

originalBishopZeroLogPositivePower :
  ∀ n →
  Complex._≈C_ (Algebra.powC Algebra.zeroC (suc n))
    Algebra.zeroC
originalBishopZeroLogPositivePower n =
  Laws.complexMultiplyLeftZero (Algebra.powC Algebra.zeroC n)

originalBishopComplexScaleZero :
  ∀ coefficient →
  Complex._≈C_
    (Algebra.scaleC coefficient Algebra.zeroC)
    Algebra.zeroC
originalBishopComplexScaleZero coefficient =
  (let open BishopP.ℝ-Solver in
   solve 1
     (λ x → x ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl coefficient)
  ,
  (let open BishopP.ℝ-Solver in
   solve 1
     (λ x → x ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
     BishopP.≃-refl coefficient)

originalBishopLogOnePlusZeroTerm :
  ∀ n →
  Complex._≈C_
    (Log.originalBishopLogOnePlusTerm Algebra.zeroC n)
    Algebra.zeroC
originalBishopLogOnePlusZeroTerm n =
  let first =
        Algebra.scaleCCongruent
          (originalBishopZeroLogPositivePower n)
          (Log.logCoefficient n)
      second =
        originalBishopComplexScaleZero (Log.logCoefficient n)
  in
  (BishopP.≃-trans (proj₁ first) (proj₁ second))
  ,
  (BishopP.≃-trans (proj₂ first) (proj₂ second))

originalBishopLogZeroPartial :
  ∀ count →
  Complex._≈C_
    (Complex.complex
      (BishopSequence.SeriesOf
        (Complex.realTerms (Log.originalBishopLogOnePlusTerm Algebra.zeroC))
        count)
      (BishopSequence.SeriesOf
        (Complex.imagTerms (Log.originalBishopLogOnePlusTerm Algebra.zeroC))
        count))
    Algebra.zeroC
originalBishopLogZeroPartial count =
  (BishopP.≃-trans
    (Ext.seriesPartialSumsCongruent
      (λ n → proj₁ (originalBishopLogOnePlusZeroTerm n))
      count)
    (Zero.originalBishopFiniteZeroSum count))
  ,
  (BishopP.≃-trans
    (Ext.seriesPartialSumsCongruent
      (λ n → proj₂ (originalBishopLogOnePlusZeroTerm n))
      count)
    (Zero.originalBishopFiniteZeroSum count))

originalBishopLogZeroAbsoluteComponentPartial :
  (coordinate : Complex.BishopComplex → BishopReal.ℝ) →
  (∀ n →
    BishopReal._≃_
      (coordinate (Log.originalBishopLogOnePlusTerm Algebra.zeroC n))
      BishopReal.0ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopSequence.SeriesOf
      (λ n →
        BishopReal.∣ coordinate
          (Log.originalBishopLogOnePlusTerm Algebra.zeroC n) ∣)
      count)
    BishopReal.0ℝ
originalBishopLogZeroAbsoluteComponentPartial coordinate termZero count =
  BishopP.≃-trans
    (Ext.seriesPartialSumsCongruent
      (λ n →
        BishopP.≃-trans
          (BishopP.∣-∣-cong (termZero n))
          (BishopP.0≤x⇒∣x∣≃x BishopP.≤-refl))
      count)
    (Zero.originalBishopFiniteZeroSum count)

originalBishopLogZeroAbsolute :
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (Log.originalBishopLogOnePlusTerm Algebra.zeroC)
originalBishopLogZeroAbsolute =
  Complex.componentwise-absolute-series-convergent
    (BishopReal.0ℝ ,
      BishopSequence.xₙ≃c⇒xₙ→c
        (λ n →
          originalBishopLogZeroAbsoluteComponentPartial
            Complex.re
            (λ k → proj₁ (originalBishopLogOnePlusZeroTerm k))
            n))
    (BishopReal.0ℝ ,
      BishopSequence.xₙ≃c⇒xₙ→c
        (λ n →
          originalBishopLogZeroAbsoluteComponentPartial
            Complex.im
            (λ k → proj₂ (originalBishopLogOnePlusZeroTerm k))
            n))

originalBishopLogZeroSeriesConverges :
  Complex.ComplexSeriesConvergesTo
    (Log.originalBishopLogOnePlusTerm Algebra.zeroC)
    Algebra.zeroC
originalBishopLogZeroSeriesConverges =
  Complex.complex-series-converges-to
    (BishopSequence.xₙ≃c⇒xₙ→c
      (λ n → proj₁ (originalBishopLogZeroPartial n)))
    (BishopSequence.xₙ≃c⇒xₙ→c
      (λ n → proj₂ (originalBishopLogZeroPartial n)))

originalBishopCanonicalLogOneIsZero :
  Complex._≈C_
    (Log.originalBishopLogOnePlusSeriesValue
      Algebra.zeroC
      originalBishopLogZeroAbsolute)
    Algebra.zeroC
originalBishopCanonicalLogOneIsZero =
  Log.originalBishopLogOnePlusSeriesLimitUnique
    Algebra.zeroC
    originalBishopLogZeroAbsolute
    Algebra.zeroC
    originalBishopLogZeroSeriesConverges
