module DASHI.Physics.Closure.NSTriadKNSmallSpectrumWeakStretchingRound81Exact where

------------------------------------------------------------------------
-- ROUND81 / SMALL-SPECTRUM BRANCH CLOSURE
--
-- Round80 proved that for 3D trace-free strain the adjacent gaps determine the
-- whole spectrum.  This module turns that algebra into the actual pointwise
-- stretching consequence needed by the both-small branch.
--
-- If
--
--   0 <= g12 <= delta,
--   0 <= g23 <= delta,
--   lambda1 >= lambda2 >= lambda3,
--   lambda1 + lambda2 + lambda3 = 0,
--
-- then 3 lambda1 = 2 g12 + g23 <= 3 delta, hence lambda1 <= delta.
-- For nonnegative alignment weights alpha_i summing to one,
--
--   lambda1 alpha1 + lambda2 alpha2 + lambda3 alpha3 <= lambda1 <= delta.
--
-- Therefore the normalized vortex-stretching scalar is at most delta, and for
-- nonnegative enstrophy Omega the full stretching contribution is at most
-- Omega * delta.  No eigenvector derivative or reciprocal gap appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNTraceFreeGapSpectrumRound80Exact as Spectrum

_two three : ℚ
_two = (+ 2) / 1
three = (+ 3) / 1

threePositiveProof : 0ℚ < three
threePositiveProof = ℚP.positive⁻¹ three

instance
  threePositive : Positive three
  threePositive = ℚ.positive threePositiveProof

record SmallSpectrumStretchingDatum : Set where
  field
    traceFree : Spectrum.TraceFreeThreeSpectrum
    threshold : ℚ

    thresholdNonnegative : 0ℚ ≤ threshold
    gap12Nonnegative :
      0ℚ ≤ Spectrum.gap12 (Spectrum.spectrum traceFree)
    gap23Nonnegative :
      0ℚ ≤ Spectrum.gap23 (Spectrum.spectrum traceFree)
    gap12Small :
      Spectrum.gap12 (Spectrum.spectrum traceFree) ≤ threshold
    gap23Small :
      Spectrum.gap23 (Spectrum.spectrum traceFree) ≤ threshold

    alpha1 alpha2 alpha3 : ℚ
    alpha1Nonnegative : 0ℚ ≤ alpha1
    alpha2Nonnegative : 0ℚ ≤ alpha2
    alpha3Nonnegative : 0ℚ ≤ alpha3
    alphaSumOne : (alpha1 + alpha2) + alpha3 ≡ 1ℚ

    lambda2BelowLambda1 :
      Spectrum.lambda2 (Spectrum.spectrum traceFree)
      ≤ Spectrum.lambda1 (Spectrum.spectrum traceFree)
    lambda3BelowLambda1 :
      Spectrum.lambda3 (Spectrum.spectrum traceFree)
      ≤ Spectrum.lambda1 (Spectrum.spectrum traceFree)

open SmallSpectrumStretchingDatum public

normalizedStretching : SmallSpectrumStretchingDatum → ℚ
normalizedStretching datum =
  Spectrum.lambda1 (Spectrum.spectrum (traceFree datum)) * alpha1 datum
  + Spectrum.lambda2 (Spectrum.spectrum (traceFree datum)) * alpha2 datum
  + Spectrum.lambda3 (Spectrum.spectrum (traceFree datum)) * alpha3 datum

lambda1BelowThreshold :
  (datum : SmallSpectrumStretchingDatum) →
  Spectrum.lambda1 (Spectrum.spectrum (traceFree datum)) ≤ threshold datum
lambda1BelowThreshold datum =
  let
    s = Spectrum.spectrum (traceFree datum)
    a = Spectrum.gap12 s
    b = Spectrum.gap23 s

    twoNonnegative : 0ℚ ≤ _two
    twoNonnegative = ℚP.nonNegative⁻¹ _two

    scaledA : _two * a ≤ _two * threshold datum
    scaledA =
      let instance twoNN : NonNegative _two
          twoNN = ℚ.nonNegative twoNonnegative
      in ℚP.*-monoˡ-≤-nonNeg _two (gap12Small datum)

    summed : _two * a + b ≤ _two * threshold datum + threshold datum
    summed = ℚP.+-mono-≤ scaledA (gap23Small datum)

    scaledLambda :
      three * Spectrum.lambda1 s ≤ three * threshold datum
    scaledLambda =
      subst
        (λ left → left ≤ three * threshold datum)
        (sym (Spectrum.traceFreeLambda1FromGaps (traceFree datum)))
        (subst
          (λ right → _two * a + b ≤ right)
          (ℚRing.solve-∀ (threshold datum))
          summed)
  in
  ℚP.*-cancelˡ-≤-pos three scaledLambda

normalizedStretchingBelowLambda1 :
  (datum : SmallSpectrumStretchingDatum) →
  normalizedStretching datum
  ≤ Spectrum.lambda1 (Spectrum.spectrum (traceFree datum))
normalizedStretchingBelowLambda1 datum =
  let
    s = Spectrum.spectrum (traceFree datum)
    l1 = Spectrum.lambda1 s
    l2 = Spectrum.lambda2 s
    l3 = Spectrum.lambda3 s

    instance
      a1NN : NonNegative (alpha1 datum)
      a1NN = ℚ.nonNegative (alpha1Nonnegative datum)
      a2NN : NonNegative (alpha2 datum)
      a2NN = ℚ.nonNegative (alpha2Nonnegative datum)
      a3NN : NonNegative (alpha3 datum)
      a3NN = ℚ.nonNegative (alpha3Nonnegative datum)

    first : l1 * alpha1 datum ≤ l1 * alpha1 datum
    first = ℚP.≤-refl

    second : l2 * alpha2 datum ≤ l1 * alpha2 datum
    second = ℚP.*-monoʳ-≤-nonNeg (alpha2 datum) (lambda2BelowLambda1 datum)

    third : l3 * alpha3 datum ≤ l1 * alpha3 datum
    third = ℚP.*-monoʳ-≤-nonNeg (alpha3 datum) (lambda3BelowLambda1 datum)

    summed :
      normalizedStretching datum
      ≤ l1 * alpha1 datum + l1 * alpha2 datum + l1 * alpha3 datum
    summed = ℚP.+-mono-≤ (ℚP.+-mono-≤ first second) third

    endpoint :
      l1 * alpha1 datum + l1 * alpha2 datum + l1 * alpha3 datum ≡ l1
    endpoint = trans
      (ℚRing.solve-∀ l1 (alpha1 datum) (alpha2 datum) (alpha3 datum))
      (trans
        (cong
          (λ total → l1 * total)
          (alphaSumOne datum))
        (ℚP.*-identityʳ l1))
  in
  subst
    (λ upper → normalizedStretching datum ≤ upper)
    endpoint
    summed

smallSpectrumNormalizedStretchingBound :
  (datum : SmallSpectrumStretchingDatum) →
  normalizedStretching datum ≤ threshold datum
smallSpectrumNormalizedStretchingBound datum =
  ℚP.≤-trans
    (normalizedStretchingBelowLambda1 datum)
    (lambda1BelowThreshold datum)

fullStretching : ℚ → SmallSpectrumStretchingDatum → ℚ
fullStretching enstrophy datum = enstrophy * normalizedStretching datum

smallSpectrumFullStretchingBound :
  (enstrophy : ℚ) →
  0ℚ ≤ enstrophy →
  (datum : SmallSpectrumStretchingDatum) →
  fullStretching enstrophy datum ≤ enstrophy * threshold datum
smallSpectrumFullStretchingBound enstrophy enstrophyNonnegative datum =
  let instance omegaNN : NonNegative enstrophy
      omegaNN = ℚ.nonNegative enstrophyNonnegative
  in
  ℚP.*-monoˡ-≤-nonNeg enstrophy
    (smallSpectrumNormalizedStretchingBound datum)

round81BothSmallGapsGiveWeakStretchingBound : Bool
round81BothSmallGapsGiveWeakStretchingBound = true

round81BothSmallGapsGiveWeakStretchingBoundIsTrue :
  round81BothSmallGapsGiveWeakStretchingBound ≡ true
round81BothSmallGapsGiveWeakStretchingBoundIsTrue = refl
