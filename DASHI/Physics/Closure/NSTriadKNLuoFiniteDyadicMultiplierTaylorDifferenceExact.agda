module DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Marin Mišur.
-- Title: "Global L^p Second Commutation Lemma".
-- arXiv:2608.01216v1.
-- arXiv DOI: 10.48550/arXiv.2608.01216.
--
-- PURPOSE
-- Give the exact finite Taylor algebra behind the multiplier-difference lane.
-- A one-sided difference retains its linear symbol derivative.  Pairing the
-- opposite displacement cancels that linear term and leaves the two genuine
-- second-order remainders:
--
--   sigma(k+eta) - sigma(k) = L + R_+,
--   sigma(k-eta) - sigma(k) = -L + R_-,
--
--   sigma(k+eta) + sigma(k-eta) - 2 sigma(k) = R_+ + R_-.
--
-- Analytic derivative bounds such as
--
--   |L| <= C lambda_q^-1 |eta|,
--   |R_+|+|R_-| <= C lambda_q^-2 |eta|^2
--
-- remain explicit producer estimates for the selected smooth dyadic symbol.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

record MultiplierTaylorPair : Set where
  constructor multiplier-taylor-pair
  field
    center linearIncrement plusRemainder minusRemainder : ℚ

open MultiplierTaylorPair public

plusValue : MultiplierTaylorPair → ℚ
plusValue sample =
  center sample + linearIncrement sample + plusRemainder sample

minusValue : MultiplierTaylorPair → ℚ
minusValue sample =
  center sample - linearIncrement sample + minusRemainder sample

oneSidedDifference : MultiplierTaylorPair → ℚ
oneSidedDifference sample = plusValue sample - center sample

centeredSecondDifference : MultiplierTaylorPair → ℚ
centeredSecondDifference sample =
  plusValue sample + minusValue sample
  - (Int.+ 2 / 1) * center sample

oneSidedDifferenceIdentity :
  (sample : MultiplierTaylorPair) →
  oneSidedDifference sample
  ≡ linearIncrement sample + plusRemainder sample
oneSidedDifferenceIdentity sample =
  solve
    ( center sample
    ∷ linearIncrement sample
    ∷ plusRemainder sample
    ∷ [])

centeredSecondDifferenceCancelsLinearSymbol :
  (sample : MultiplierTaylorPair) →
  centeredSecondDifference sample
  ≡ plusRemainder sample + minusRemainder sample
centeredSecondDifferenceCancelsLinearSymbol sample =
  solve
    ( center sample
    ∷ linearIncrement sample
    ∷ plusRemainder sample
    ∷ minusRemainder sample
    ∷ [])

record DyadicMultiplierScaleSample : Set where
  constructor dyadic-multiplier-scale-sample
  field
    inverseOutputScale displacement : ℚ
    symbolGradient symbolCurvature : ℚ

open DyadicMultiplierScaleSample public

firstDifferenceEnvelope : DyadicMultiplierScaleSample → ℚ
firstDifferenceEnvelope sample =
  inverseOutputScale sample
  * displacement sample
  * symbolGradient sample

secondDifferenceEnvelope : DyadicMultiplierScaleSample → ℚ
secondDifferenceEnvelope sample =
  inverseOutputScale sample
  * inverseOutputScale sample
  * displacement sample
  * displacement sample
  * symbolCurvature sample
