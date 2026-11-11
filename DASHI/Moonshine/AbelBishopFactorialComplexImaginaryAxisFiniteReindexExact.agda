module DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisFiniteReindexExact where

------------------------------------------------------------------------
-- ALL-N FINITE 2N-PREFIX IMAGINARY AXIS SIN/COS FACTORIAL WELD.
--
-- Actual Bishop complex terms: (iy)^n/n!.
-- The first 2N terms match the first N configured cosine terms in
-- the real coordinate, and the first N configured sine terms in the
-- imaginary coordinate. Generic finite even/odd reindexing was
-- paid in BishopFiniteEvenOddSeriesReindexExact.
--
-- No infinite series reindexing or expC addition is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)

import Real as BishopReal
import Sequence as BishopSequence
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteEvenOddSeriesReindexExact as EvenOdd
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Terms
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisSignedTermsExact as Signed

factorialImaginaryRealTerm :
  BishopReal.ℝ → Nat → BishopReal.ℝ
factorialImaginaryRealTerm y n =
  Complex.re
    (Terms.originalBishopFactorialComplexTerm (Axis.imaginaryAxis y) n)

factorialImaginaryImagTerm :
  BishopReal.ℝ → Nat → BishopReal.ℝ
factorialImaginaryImagTerm y n =
  Complex.im
    (Terms.originalBishopFactorialComplexTerm (Axis.imaginaryAxis y) n)

zeroTerms : Nat → BishopReal.ℝ
zeroTerms _ = BishopReal.0ℝ

originalBishopFiniteZeroSum :
  ∀ count →
  BishopReal._≃_
    (BishopReal.∑₀ zeroTerms count)
    BishopReal.0ℝ
originalBishopFiniteZeroSum zero = BishopP.≃-refl
originalBishopFiniteZeroSum (suc n) =
  BishopP.≃-trans
    (BishopP.+-cong
      (originalBishopFiniteZeroSum n)
      BishopP.≃-refl)
    (BishopP.+-identityʳ BishopReal.0ℝ)

originalBishopImaginaryOddRealSumZero :
  ∀ y count →
  BishopReal._≃_
    (BishopReal.∑₀
      (EvenOdd.oddTerms (factorialImaginaryRealTerm y))
      count)
    BishopReal.0ℝ
originalBishopImaginaryOddRealSumZero y count =
  BishopP.≃-trans
    (Ext.finiteSumCongruent
      (λ n → proj₁
        (Axis.originalBishopImaginaryAxisFactorialOddTerm y n))
      count)
    (originalBishopFiniteZeroSum count)

originalBishopImaginaryEvenImagSumZero :
  ∀ y count →
  BishopReal._≃_
    (BishopReal.∑₀
      (EvenOdd.evenTerms (factorialImaginaryImagTerm y))
      count)
    BishopReal.0ℝ
originalBishopImaginaryEvenImagSumZero y count =
  BishopP.≃-trans
    (Ext.finiteSumCongruent
      (λ n → proj₂
        (Axis.originalBishopImaginaryAxisFactorialEvenTerm y n))
      count)
    (originalBishopFiniteZeroSum count)

originalBishopImaginaryAxisRealPrefix2NIsCosine :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (BishopReal.∑₀
      (factorialImaginaryRealTerm y)
      (Estimates.evenExponent n))
    (BishopReal.∑₀
      (Elementary.cosineTerm (Cartesian.dataSet T) y)
      n)
originalBishopImaginaryAxisRealPrefix2NIsCosine T y n =
  let
    cosinePrefix =
      BishopReal.∑₀
        (Elementary.cosineTerm (Cartesian.dataSet T) y)
        n
  in
  BishopP.≃-trans
    (EvenOdd.originalBishopFiniteEvenOddSumReindex
      (factorialImaginaryRealTerm y) n)
    (BishopP.≃-trans
      (BishopP.+-cong
        (Signed.originalBishopImaginaryAxisCosinePartialSameConfigured
          T y n)
        (originalBishopImaginaryOddRealSumZero y n))
      (BishopP.+-identityʳ cosinePrefix))

originalBishopImaginaryAxisImagPrefix2NIsSine :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (BishopReal.∑₀
      (factorialImaginaryImagTerm y)
      (Estimates.evenExponent n))
    (BishopReal.∑₀
      (Elementary.sineTerm (Cartesian.dataSet T) y)
      n)
originalBishopImaginaryAxisImagPrefix2NIsSine T y n =
  let
    sinePrefix =
      BishopReal.∑₀
        (Elementary.sineTerm (Cartesian.dataSet T) y)
        n
  in
  BishopP.≃-trans
    (EvenOdd.originalBishopFiniteEvenOddSumReindex
      (factorialImaginaryImagTerm y) n)
    (BishopP.≃-trans
      (BishopP.+-cong
        (originalBishopImaginaryEvenImagSumZero y n)
        (Signed.originalBishopImaginaryAxisSinePartialSameConfigured
          T y n))
      (BishopP.+-identityˡ sinePrefix))


------------------------------------------------------------------------
-- CONTIGUOUS FULL FACTORIAL SERIES PREFIXES AT EVEN CUTOFFS.
-- This is not merely convergence of parity-selected subseries.
------------------------------------------------------------------------

originalBishopImaginaryAxisRealEvenPrefixConvergesToCosine :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  BishopSequence._ConvergesTo_
    (λ n →
      BishopReal.∑₀ (factorialImaginaryRealTerm y)
        (Estimates.evenExponent n))
    (Elementary.bishopCos (Cartesian.dataSet T) y)
originalBishopImaginaryAxisRealEvenPrefixConvergesToCosine T y =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (originalBishopImaginaryAxisRealPrefix2NIsCosine
          T y (suc count-1))})
    ( Elementary.bishopCos (Cartesian.dataSet T) y
    , Elementary.bishopCosConvergence (Cartesian.dataSet T) y
    )

originalBishopImaginaryAxisImagEvenPrefixConvergesToSine :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  BishopSequence._ConvergesTo_
    (λ n →
      BishopReal.∑₀ (factorialImaginaryImagTerm y)
        (Estimates.evenExponent n))
    (Elementary.bishopSin (Cartesian.dataSet T) y)
originalBishopImaginaryAxisImagEvenPrefixConvergesToSine T y =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (originalBishopImaginaryAxisImagPrefix2NIsSine
          T y (suc count-1))})
    ( Elementary.bishopSin (Cartesian.dataSet T) y
    , Elementary.bishopSinConvergence (Cartesian.dataSet T) y
    )
