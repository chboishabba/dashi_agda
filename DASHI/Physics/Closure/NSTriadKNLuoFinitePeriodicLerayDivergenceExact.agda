module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicLerayDivergenceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Classical projection reference:
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Prove the exact finite Fourier-coefficient form of the first HH1 step.
-- For every nonzero periodic mode k, the H^{-1} weight |k|^{-2}
-- cancels the derivative square |k|^2, while the Leray projector is
-- contractive:
--
--   |k|^{-2} |P(k) (ik . Fhat(k))|^2 <= |Fhat(k)|^2.
--
-- The continuum Fourier theorem supplies the pointwise projection bound and
-- inverse-frequency calibration.  This module proves the complete ordered
-- algebra and its finite Parseval sum; no analytic multiplier estimate is
-- hidden in a global postulate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

record PeriodicLerayMode : Set where
  constructor periodic-leray-mode
  field
    inverseFrequencySquared frequencySquared : ℚ
    projectedDivergenceSquared tensorModeSquared : ℚ

    inverseFrequencyNonnegative :
      0ℚ ≤ inverseFrequencySquared

    inverseFrequencyCalibration :
      inverseFrequencySquared * frequencySquared ≡ 1ℚ

    lerayDerivativeSquareBound :
      projectedDivergenceSquared
      ≤ frequencySquared * tensorModeSquared

open PeriodicLerayMode public

hMinusOneModeSquared : PeriodicLerayMode → ℚ
hMinusOneModeSquared mode =
  inverseFrequencySquared mode * projectedDivergenceSquared mode

periodicLerayModeCancellation :
  (mode : PeriodicLerayMode) →
  hMinusOneModeSquared mode ≤ tensorModeSquared mode
periodicLerayModeCancellation mode =
  let
    multiplied :
      inverseFrequencySquared mode * projectedDivergenceSquared mode
      ≤ inverseFrequencySquared mode
          * (frequencySquared mode * tensorModeSquared mode)
    multiplied =
      let
        instance
          inverseFrequencyIsNonnegative =
            nonNegative (inverseFrequencyNonnegative mode)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (inverseFrequencySquared mode)
        (lerayDerivativeSquareBound mode)

    association :
      inverseFrequencySquared mode
        * (frequencySquared mode * tensorModeSquared mode)
      ≡ (inverseFrequencySquared mode * frequencySquared mode)
          * tensorModeSquared mode
    association =
      solve
        ( inverseFrequencySquared mode
        ∷ frequencySquared mode
        ∷ tensorModeSquared mode
        ∷ [])

    calibration :
      (inverseFrequencySquared mode * frequencySquared mode)
        * tensorModeSquared mode
      ≡ tensorModeSquared mode
    calibration
      rewrite inverseFrequencyCalibration mode =
      solve (tensorModeSquared mode ∷ [])

    normalizedUpper :
      inverseFrequencySquared mode
        * (frequencySquared mode * tensorModeSquared mode)
      ≡ tensorModeSquared mode
    normalizedUpper = trans association calibration
  in
  subst
    (λ upper → hMinusOneModeSquared mode ≤ upper)
    normalizedUpper
    multiplied

sumHMinusOneSquared : List PeriodicLerayMode → ℚ
sumHMinusOneSquared [] = 0ℚ
sumHMinusOneSquared (mode ∷ modes) =
  hMinusOneModeSquared mode + sumHMinusOneSquared modes

sumTensorModeSquared : List PeriodicLerayMode → ℚ
sumTensorModeSquared [] = 0ℚ
sumTensorModeSquared (mode ∷ modes) =
  tensorModeSquared mode + sumTensorModeSquared modes

finitePeriodicLerayCancellation :
  (modes : List PeriodicLerayMode) →
  sumHMinusOneSquared modes ≤ sumTensorModeSquared modes
finitePeriodicLerayCancellation [] = ℚₚ.≤-refl
finitePeriodicLerayCancellation (mode ∷ modes) =
  ℚₚ.+-mono-≤
    (periodicLerayModeCancellation mode)
    (finitePeriodicLerayCancellation modes)
