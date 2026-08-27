module DASHI.Physics.Closure.NSTriadKNExternalHHSameHelicityGapProductRound127Exact where

------------------------------------------------------------------------
-- ROUND127 / SAME-HELICITY GAP TIMES RADIAL SUM
--
-- The HH Waleffe coefficient on one helicity branch is
--
--       lambda_q - lambda_p = s (m_q - m_p),    s in {+1,-1}.
--
-- The exact division-free bridge to Round125 is therefore
--
--   (lambda_q-lambda_p) (lambda_q+lambda_p)
--       = m_q^2 - m_p^2.
--
-- For the negative-helicity branch both lambda values are negated; the same
-- square gap survives.  This module proves that algebra over the repository's
-- generic RealField.  Combined with Round125's
--
--       |q|^2-|p|^2 = k . (q-p),
--
-- it isolates the remaining analytic operation exactly: divide/cancel by the
-- HIGH radial sum m_q+m_p in an ordered-real carrier.  No such cancellation is
-- smuggled into the weak algebraic field used by the finite Fourier core.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

realAdd :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
realAdd {F = F} = C3.add F

realSubtract :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
realSubtract {F = F} a b = C3.add F a (C3.negate F b)

realSquare :
  ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
realSquare {F = F} a = C3.multiply F a a

squareGap :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
squareGap {F = F} p q = realSubtract (realSquare q) (realSquare p)

differenceTimesSumIsSquareGap :
  ∀ {r} {F : C3.RealField r}
    (p q : C3.Carrier F) →
  C3.multiply F (realSubtract q p) (realAdd q p)
  ≡ squareGap p q
differenceTimesSumIsSquareGap {F = F} p q =
  R.solve 2
    (λ p q →
      ((q R.⊕ (R.⊝ p)) R.⊗ (q R.⊕ p))
      R.⊜ ((q R.⊗ q) R.⊕ (R.⊝ (p R.⊗ p))))
    refl p q
  where module R = Ring.Solver F

signedModeNorm :
  ∀ {r} {F : C3.RealField r} →
  Helical.HelicitySign → C3.Carrier F → C3.Carrier F
signedModeNorm Helical.plus m = m
signedModeNorm {F = F} Helical.minus m = C3.negate F m

sameHelicityGap :
  ∀ {r} {F : C3.RealField r} →
  Helical.HelicitySign →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
sameHelicityGap sign p q =
  realSubtract (signedModeNorm sign q) (signedModeNorm sign p)

sameHelicitySum :
  ∀ {r} {F : C3.RealField r} →
  Helical.HelicitySign →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
sameHelicitySum sign p q =
  realAdd (signedModeNorm sign q) (signedModeNorm sign p)

plusGapTimesSumIsSquareGap :
  ∀ {r} {F : C3.RealField r}
    (p q : C3.Carrier F) →
  C3.multiply F
    (sameHelicityGap Helical.plus p q)
    (sameHelicitySum Helical.plus p q)
  ≡ squareGap p q
plusGapTimesSumIsSquareGap = differenceTimesSumIsSquareGap

minusGapTimesSumIsSquareGap :
  ∀ {r} {F : C3.RealField r}
    (p q : C3.Carrier F) →
  C3.multiply F
    (sameHelicityGap Helical.minus p q)
    (sameHelicitySum Helical.minus p q)
  ≡ squareGap p q
minusGapTimesSumIsSquareGap {F = F} p q =
  R.solve 2
    (λ p q →
      ((((R.⊝ q) R.⊕ (R.⊝ (R.⊝ p)))
        R.⊗ ((R.⊝ q) R.⊕ (R.⊝ p))))
      R.⊜ ((q R.⊗ q) R.⊕ (R.⊝ (p R.⊗ p))))
    refl p q
  where module R = Ring.Solver F

-- Orientation-free statement: each helicity branch has the same square-gap
-- numerator; only the signs of the two linear factors change together.
sameHelicityGapTimesSumIsSquareGap :
  ∀ {r} {F : C3.RealField r}
    (sign : Helical.HelicitySign)
    (p q : C3.Carrier F) →
  C3.multiply F
    (sameHelicityGap sign p q)
    (sameHelicitySum sign p q)
  ≡ squareGap p q
sameHelicityGapTimesSumIsSquareGap Helical.plus =
  plusGapTimesSumIsSquareGap
sameHelicityGapTimesSumIsSquareGap Helical.minus =
  minusGapTimesSumIsSquareGap

round127SameHelicityGapProductFactorizationClosed : Bool
round127SameHelicityGapProductFactorizationClosed = true

round127BothHelicitySignsShareSquareGapNumerator : Bool
round127BothHelicitySignsShareSquareGapNumerator = true

round127OrderedPositiveRadialSumCancellationClosed : Bool
round127OrderedPositiveRadialSumCancellationClosed = false

round127SameHelicityGapProductFactorizationClosedIsTrue :
  round127SameHelicityGapProductFactorizationClosed ≡ true
round127SameHelicityGapProductFactorizationClosedIsTrue = refl

round127BothHelicitySignsShareSquareGapNumeratorIsTrue :
  round127BothHelicitySignsShareSquareGapNumerator ≡ true
round127BothHelicitySignsShareSquareGapNumeratorIsTrue = refl

round127OrderedPositiveRadialSumCancellationClosedIsFalse :
  round127OrderedPositiveRadialSumCancellationClosed ≡ false
round127OrderedPositiveRadialSumCancellationClosedIsFalse = refl
