module DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisSignedTermsExact where

------------------------------------------------------------------------
-- EXACT, SAME-SOURCE IMAGINARY-AXIS SINE/COSINE FINITE TERMS.
--
-- On the original Bishop complex pair, powers of (0,y) at the
-- repo's actual even/odd indices give respectively the signed
-- cosine/sine factorial terms owned by
-- BalabanBishopConcreteSineCosineTermParityExact.
--
-- This file pays FINITE coefficient identity only. Infinite series
-- parity-subsequence convergence and identification with configured
-- BishopSetoidComplexExact.expC remain separate P1 obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as BishopReal
import Sequence as BishopSequence
import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as NegExp
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Terms
import DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact as Factorial
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Power
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Signed

square : BishopReal.ℝ → BishopReal.ℝ
square y = BishopReal._*_ y y

originalBishopSquarePowerEven :
  ∀ y n →
  BishopReal._≃_
    (BishopReal.pow (square y) n)
    (BishopReal.pow y (Estimates.evenExponent n))
originalBishopSquarePowerEven y zero = BishopP.≃-refl
originalBishopSquarePowerEven y (suc n) =
  BishopP.≃-trans
    (BishopP.*-congʳ (originalBishopSquarePowerEven y n))
    (BishopP.≃-symm
      (Power.powTwoStep y (Estimates.evenExponent n)))

originalBishopSquarePowerOdd :
  ∀ y n →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal.pow (square y) n) y)
    (BishopReal.pow y (Estimates.oddExponent n))
originalBishopSquarePowerOdd y zero = BishopP.≃-refl
originalBishopSquarePowerOdd y (suc n) =
  let
    p = BishopReal.pow (square y) n
    reordered :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ p (square y)) y)
        (BishopReal._*_
          (BishopReal._*_ p y)
          (square y))
    reordered =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ p′ y′ →
          (p′ ⊗ (y′ ⊗ y′)) ⊗ y′
          ⊜ (p′ ⊗ y′) ⊗ (y′ ⊗ y′))
        BishopP.≃-refl p y
  in
  BishopP.≃-trans reordered
    (BishopP.≃-trans
      (BishopP.*-congʳ (originalBishopSquarePowerOdd y n))
      (BishopP.≃-symm
        (Power.powTwoStep y (Estimates.oddExponent n))))

originalBishopNegativeSquarePowerSignedEven :
  ∀ y n →
  BishopReal._≃_
    (BishopReal.pow (Axis.negativeSquare y) n)
    (BishopReal._*_
      (Signed.alternatingSign n)
      (BishopReal.pow y (Estimates.evenExponent n)))
originalBishopNegativeSquarePowerSignedEven y n =
  BishopP.≃-trans
    (NegExp.powNegativeByAlternatingSign (square y) n)
    (BishopP.*-congˡ (originalBishopSquarePowerEven y n))

originalBishopNegativeSquarePowerSignedOdd :
  ∀ y n →
  BishopReal._≃_
    (BishopReal._*_
      y (BishopReal.pow (Axis.negativeSquare y) n))
    (BishopReal._*_
      (Signed.alternatingSign n)
      (BishopReal.pow y (Estimates.oddExponent n)))
originalBishopNegativeSquarePowerSignedOdd y n =
  let
    s = Signed.alternatingSign n
    p = BishopReal.pow (square y) n
    rearrange :
      BishopReal._≃_
        (BishopReal._*_ y (BishopReal._*_ s p))
        (BishopReal._*_ s (BishopReal._*_ p y))
    rearrange =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ y′ s′ p′ →
          y′ ⊗ (s′ ⊗ p′)
          ⊜ s′ ⊗ (p′ ⊗ y′))
        BishopP.≃-refl y s p
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (NegExp.powNegativeByAlternatingSign (square y) n))
    (BishopP.≃-trans rearrange
      (BishopP.*-congˡ (originalBishopSquarePowerOdd y n)))

originalBishopImaginaryAxisCosineSignedTerm :
  ∀ y n →
  BishopReal._≃_
    (Complex.re
      (Terms.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y) (Estimates.evenExponent n)))
    (Signed.cosineSignedTerm y n)
originalBishopImaginaryAxisCosineSignedTerm y n =
  let
    c = Factorial.factorialCoefficient (Estimates.evenExponent n)
    s = Signed.alternatingSign n
    p = BishopReal.pow y (Estimates.evenExponent n)
    rearrange :
      BishopReal._≃_
        (BishopReal._*_ c (BishopReal._*_ s p))
        (BishopReal._*_ s (BishopReal._*_ c p))
    rearrange =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ c′ s′ p′ →
          c′ ⊗ (s′ ⊗ p′)
          ⊜ s′ ⊗ (c′ ⊗ p′))
        BishopP.≃-refl c s p
  in
  BishopP.≃-trans
    (proj₁ (Axis.originalBishopImaginaryAxisFactorialEvenTerm y n))
    (BishopP.≃-trans
      (BishopP.*-congˡ (originalBishopNegativeSquarePowerSignedEven y n))
      rearrange)

originalBishopImaginaryAxisSineSignedTerm :
  ∀ y n →
  BishopReal._≃_
    (Complex.im
      (Terms.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y) (Estimates.oddExponent n)))
    (Signed.sineSignedTerm y n)
originalBishopImaginaryAxisSineSignedTerm y n =
  let
    c = Factorial.factorialCoefficient (Estimates.oddExponent n)
    s = Signed.alternatingSign n
    p = BishopReal.pow y (Estimates.oddExponent n)
    rearrange :
      BishopReal._≃_
        (BishopReal._*_ c (BishopReal._*_ s p))
        (BishopReal._*_ s (BishopReal._*_ c p))
    rearrange =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ c′ s′ p′ →
          c′ ⊗ (s′ ⊗ p′)
          ⊜ s′ ⊗ (c′ ⊗ p′))
        BishopP.≃-refl c s p
  in
  BishopP.≃-trans
    (proj₂ (Axis.originalBishopImaginaryAxisFactorialOddTerm y n))
    (BishopP.≃-trans
      (BishopP.*-congˡ (originalBishopNegativeSquarePowerSignedOdd y n))
      rearrange)


------------------------------------------------------------------------
-- THE *CONFIGURED* BISHOP CARTESIAN SINE/COSINE DATA, NOT A SECOND
-- TRIGONOMETRIC SOURCE. Term-identification is explicitly carried
-- by the existing Cartesian.BishopSetoidComplexTranscendentals T.
------------------------------------------------------------------------

originalBishopImaginaryAxisCosineConfiguredTerm :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (Complex.re
      (Terms.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y) (Estimates.evenExponent n)))
    (Elementary.cosineTerm (Cartesian.dataSet T) y n)
originalBishopImaginaryAxisCosineConfiguredTerm T y n =
  BishopP.≃-trans
    (originalBishopImaginaryAxisCosineSignedTerm y n)
    (BishopP.≃-symm
      (Signed.cosineTermIsConcrete (Cartesian.trigIdentification T) y n))

originalBishopImaginaryAxisSineConfiguredTerm :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (Complex.im
      (Terms.originalBishopFactorialComplexTerm
        (Axis.imaginaryAxis y) (Estimates.oddExponent n)))
    (Elementary.sineTerm (Cartesian.dataSet T) y n)
originalBishopImaginaryAxisSineConfiguredTerm T y n =
  BishopP.≃-trans
    (originalBishopImaginaryAxisSineSignedTerm y n)
    (BishopP.≃-symm
      (Signed.sineTermIsConcrete (Cartesian.trigIdentification T) y n))

originalBishopImaginaryAxisCosinePartialSameConfigured :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y count →
  BishopReal._≃_
    (BishopReal.∑₀
      (λ n → Complex.re
        (Terms.originalBishopFactorialComplexTerm
          (Axis.imaginaryAxis y) (Estimates.evenExponent n)))
      count)
    (BishopReal.∑₀
      (Elementary.cosineTerm (Cartesian.dataSet T) y)
      count)
originalBishopImaginaryAxisCosinePartialSameConfigured T y count =
  SeriesExt.finiteSumCongruent
    (originalBishopImaginaryAxisCosineConfiguredTerm T y)
    count

originalBishopImaginaryAxisSinePartialSameConfigured :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y count →
  BishopReal._≃_
    (BishopReal.∑₀
      (λ n → Complex.im
        (Terms.originalBishopFactorialComplexTerm
          (Axis.imaginaryAxis y) (Estimates.oddExponent n)))
      count)
    (BishopReal.∑₀
      (Elementary.sineTerm (Cartesian.dataSet T) y)
      count)
originalBishopImaginaryAxisSinePartialSameConfigured T y count =
  SeriesExt.finiteSumCongruent
    (originalBishopImaginaryAxisSineConfiguredTerm T y)
    count


------------------------------------------------------------------------
-- INFINITE PARITY-SUBSERIES LIMIT IDENTIFICATION ON THE ORIGINAL
-- BISHOP REAL CARRIER. This is a genuine limit-transport theorem:
-- no new convergence input, no new cosine or sine value.
--
-- It does NOT yet prove interleaving of the two subseries into the
-- full factorial complex series or the cartesian exponential product.
------------------------------------------------------------------------

originalBishopImaginaryAxisCosineSubseriesConverges :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (λ n → Complex.re
        (Terms.originalBishopFactorialComplexTerm
          (Axis.imaginaryAxis y) (Estimates.evenExponent n))))
    (Elementary.bishopCos (Cartesian.dataSet T) y)
originalBishopImaginaryAxisCosineSubseriesConverges T y =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (originalBishopImaginaryAxisCosinePartialSameConfigured
          T y (suc count-1))})
    ( Elementary.bishopCos (Cartesian.dataSet T) y
    , Elementary.bishopCosConvergence (Cartesian.dataSet T) y
    )

originalBishopImaginaryAxisSineSubseriesConverges :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (λ n → Complex.im
        (Terms.originalBishopFactorialComplexTerm
          (Axis.imaginaryAxis y) (Estimates.oddExponent n))))
    (Elementary.bishopSin (Cartesian.dataSet T) y)
originalBishopImaginaryAxisSineSubseriesConverges T y =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (originalBishopImaginaryAxisSinePartialSameConfigured
          T y (suc count-1))})
    ( Elementary.bishopSin (Cartesian.dataSet T) y
    , Elementary.bishopSinConvergence (Cartesian.dataSet T) y
    )
