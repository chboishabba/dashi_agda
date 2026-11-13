module DASHI.Physics.YangMills.YMClayN1GaussianNonlinearFourthCumulantNoGoExact where

------------------------------------------------------------------------
-- N1 / ORIGINAL ATTACHMENT WITNESS VALIDITY:
-- A NONZERO fourth connected cumulant of a NONLINEAR observable does
-- NOT establish that the UNDERLYING field is non-Gaussian.
--
-- Explicit classical Gaussian counterexample:
--   X is standard normal, and W = X^2 is a NONLINEAR observable.
--   By the ordinary Gaussian Wick moments:
--     E[W]   = E[X^2] = 1
--     E[W^2] = E[X^4] = 3
--     E[W^3] = E[X^6] = 15
--     E[W^4] = E[X^8] = 105.
--   The fourth cumulant of W is
--     105 - 4*15*1 - 3*3^2 + 12*3*1^2 - 6*1^4 = 48 != 0.
--
-- The following finite rational calculation is EXACT and constructive.
-- It does NOT build a standard-normal measure or prove its moments
-- inside Agda: the standard Gaussian Wick moment theorem is the
-- explicitly attributed classical input to this negative control.
--
-- Wilson loops are also NONLINEAR (holonomy/trace) functionals of
-- their gauge field. Hence "connected fourth Wilson-loop cumulant
-- !=0" is not by itself a valid N1 witness against a Gaussian
-- underlying field: one must prove the correct Gaussian null target
-- or compare the continuum gauge-field generating functional/OS
-- correlators with a source-specific generalized-free prediction.
--
-- This module neither refutes a future genuine interacting Wilson
-- witness nor supplies a physical continuum measure.
-- No new postulates. Local Agda 2.9 kernel receipt OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

gaussianSquaredMoment1 gaussianSquaredMoment2
  gaussianSquaredMoment3 gaussianSquaredMoment4 : ℚ

gaussianSquaredMoment1 = + 1 / 1
gaussianSquaredMoment2 = + 3 / 1
gaussianSquaredMoment3 = + 15 / 1
gaussianSquaredMoment4 = + 105 / 1

fourthCumulantOfSquaredGaussian : ℚ
fourthCumulantOfSquaredGaussian =
  gaussianSquaredMoment4
  - ((+ 4 / 1) * gaussianSquaredMoment3 * gaussianSquaredMoment1)
  - ((+ 3 / 1) * gaussianSquaredMoment2 * gaussianSquaredMoment2)
  + ((+ 12 / 1) * gaussianSquaredMoment2
      * gaussianSquaredMoment1 * gaussianSquaredMoment1)
  - ((+ 6 / 1) * gaussianSquaredMoment1
      * gaussianSquaredMoment1
      * gaussianSquaredMoment1 * gaussianSquaredMoment1)

gaussianSquaredFourthCumulantIsFortyEight :
  fourthCumulantOfSquaredGaussian ≡ (+ 48 / 1)
gaussianSquaredFourthCumulantIsFortyEight = Ring.solve-∀

fortyEightIsNotZero : (+ 48 / 1) ≢ 0ℚ
fortyEightIsNotZero ()

gaussianNonlinearObservableHasNonzeroFourthCumulant :
  fourthCumulantOfSquaredGaussian ≢ 0ℚ
gaussianNonlinearObservableHasNonzeroFourthCumulant
  equalsZero =
  fortyEightIsNotZero
    (trans
      (sym
        gaussianSquaredFourthCumulantIsFortyEight)
      equalsZero)
