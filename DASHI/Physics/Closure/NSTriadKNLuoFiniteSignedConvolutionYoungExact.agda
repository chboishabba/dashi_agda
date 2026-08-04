module DASHI.Physics.Closure.NSTriadKNLuoFiniteSignedConvolutionYoungExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Prove the exact finite signed-sum step used by the periodic Young estimate.
-- The analytic kernel theorem only has to provide a nonnegative term
-- majorant and its finite L1 bound.  Once those are supplied, both sides of
--
--   |sum_i term_i| <= sum_i majorant_i <= C
--
-- are derived without introducing an additional absolute-value authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; -_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNRationalFiniteSignedMajorant as Signed

signedPrefixUpper :
  ∀ signed positive cutoff →
  (∀ index → signed index ≤ positive index) →
  Majorant.sumTo signed cutoff
  ≤ Majorant.sumTo positive cutoff
signedPrefixUpper signed positive cutoff pointwise =
  Majorant.sumToMonotone signed positive cutoff pointwise

signedPrefixLower :
  ∀ signed positive cutoff →
  (∀ index → - positive index ≤ signed index) →
  - Majorant.sumTo positive cutoff
  ≤ Majorant.sumTo signed cutoff
signedPrefixLower signed positive cutoff pointwise =
  subst
    (λ lower → lower ≤ Majorant.sumTo signed cutoff)
    (Signed.sumToNeg positive cutoff)
    (Majorant.sumToMonotone
      (λ index → - positive index)
      signed
      cutoff
      pointwise)

record FiniteSignedConvolutionYoungData : Set where
  constructor finite-young
  field
    signedTerm positiveTermMajorant : Nat → ℚ
    cutoff : Nat

    termUpper :
      ∀ index → signedTerm index ≤ positiveTermMajorant index

    termLower :
      ∀ index → - positiveTermMajorant index ≤ signedTerm index

    l1TimesSupBound : ℚ

    positiveMajorantPrefixBound :
      Majorant.sumTo positiveTermMajorant cutoff
      ≤ l1TimesSupBound

open FiniteSignedConvolutionYoungData public

finiteConvolutionUpper :
  (data : FiniteSignedConvolutionYoungData) →
  Majorant.sumTo (signedTerm data) (cutoff data)
  ≤ l1TimesSupBound data
finiteConvolutionUpper data =
  ℚₚ.≤-trans
    (signedPrefixUpper
      (signedTerm data)
      (positiveTermMajorant data)
      (cutoff data)
      (termUpper data))
    (positiveMajorantPrefixBound data)

finiteConvolutionLower :
  (data : FiniteSignedConvolutionYoungData) →
  - l1TimesSupBound data
  ≤ Majorant.sumTo (signedTerm data) (cutoff data)
finiteConvolutionLower data =
  ℚₚ.≤-trans
    (ℚₚ.neg-antimono-≤
      (positiveMajorantPrefixBound data))
    (signedPrefixLower
      (signedTerm data)
      (positiveTermMajorant data)
      (cutoff data)
      (termLower data))

record FiniteConvolutionTwoSidedBound
    (data : FiniteSignedConvolutionYoungData) : Set where
  constructor two-sided
  field
    lower :
      - l1TimesSupBound data
      ≤ Majorant.sumTo (signedTerm data) (cutoff data)

    upper :
      Majorant.sumTo (signedTerm data) (cutoff data)
      ≤ l1TimesSupBound data

open FiniteConvolutionTwoSidedBound public

finiteConvolutionTwoSidedBound :
  (data : FiniteSignedConvolutionYoungData) →
  FiniteConvolutionTwoSidedBound data
finiteConvolutionTwoSidedBound data =
  two-sided
    (finiteConvolutionLower data)
    (finiteConvolutionUpper data)

finiteSignedConvolutionSummationClosed : Bool
finiteSignedConvolutionSummationClosed = true

finiteYoungTwoSidedReducerClosed : Bool
finiteYoungTwoSidedReducerClosed = true

finiteSignedConvolutionSummationClosedIsTrue :
  finiteSignedConvolutionSummationClosed ≡ true
finiteSignedConvolutionSummationClosedIsTrue = refl

finiteYoungTwoSidedReducerClosedIsTrue :
  finiteYoungTwoSidedReducerClosed ≡ true
finiteYoungTwoSidedReducerClosedIsTrue = refl
