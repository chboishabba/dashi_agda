module DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Quantify the Round-31 HH-bad obstruction on the literal dyadic scale.
-- The raw half-kernel/Bernstein ratio is
--
--   R_q = 2 * 2^q,
--
-- so it doubles at every shell.  The unique multiplicative gain that exactly
-- calibrates R_q to an owner allocation eta is
--
--   g_q(eta) = (eta / 2) * 2^(-q).
--
-- The module proves:
--
--   R_(q+1) = 2 R_q;
--   g_(q+1) = (1/2) g_q;
--   g_q R_q = eta;
--   if g R_q = eta, then g = g_q.
--
-- Thus exact cutoff-independent calibration cannot be obtained by silently
-- reusing one scale-free gain.  A physical proof must produce the inverse
-- dyadic factor through occupation time, dissipation-range localization,
-- intermittency, alignment, or another signed mechanism.  No such physical
-- producer is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 public

inverseDyadicReciprocal :
  ∀ shell → inverseDyadicScale shell * dyadicScale shell ≡ 1ℚ
inverseDyadicReciprocal zero = refl
inverseDyadicReciprocal (suc shell)
  rewrite inverseDyadicReciprocal shell =
  ℚRing.solve []

rawHHBadRatio : Nat → ℚ
rawHHBadRatio shell = two * dyadicScale shell

rawHHBadRatioDoubles :
  ∀ shell → rawHHBadRatio (suc shell) ≡ two * rawHHBadRatio shell
rawHHBadRatioDoubles shell =
  ℚRing.solve-∀ (dyadicScale shell)

requiredHHBadGain : ℚ → Nat → ℚ
requiredHHBadGain eta shell =
  eta * half * inverseDyadicScale shell

requiredHHBadGainHalves :
  ∀ eta shell →
  requiredHHBadGain eta (suc shell)
  ≡ half * requiredHHBadGain eta shell
requiredHHBadGainHalves eta shell =
  ℚRing.solve-∀ eta (inverseDyadicScale shell)

rawRatioTimesInverseFactor :
  ∀ shell →
  rawHHBadRatio shell
    * (half * inverseDyadicScale shell)
  ≡ 1ℚ
rawRatioTimesInverseFactor shell =
  trans
    (ℚRing.solve-∀
      (dyadicScale shell)
      (inverseDyadicScale shell))
    (inverseDyadicReciprocal shell)

requiredHHBadGainCalibration :
  ∀ eta shell →
  requiredHHBadGain eta shell * rawHHBadRatio shell ≡ eta
requiredHHBadGainCalibration eta shell =
  trans
    (ℚRing.solve-∀
      eta
      (inverseDyadicScale shell)
      (dyadicScale shell))
    (trans
      (cong (eta *_) (inverseDyadicReciprocal shell))
      (ℚRing.solve-∀ eta))

requiredHHBadGainUnique :
  ∀ eta shell gain →
  gain * rawHHBadRatio shell ≡ eta →
  gain ≡ requiredHHBadGain eta shell
requiredHHBadGainUnique eta shell gain calibration =
  let
    inverseFactor : ℚ
    inverseFactor = half * inverseDyadicScale shell

    scaledCalibration :
      (gain * rawHHBadRatio shell) * inverseFactor
      ≡ eta * inverseFactor
    scaledCalibration =
      cong (λ value → value * inverseFactor) calibration

    leftMeaning :
      (gain * rawHHBadRatio shell) * inverseFactor ≡ gain
    leftMeaning =
      trans
        (ℚRing.solve-∀
          gain
          (rawHHBadRatio shell)
          inverseFactor)
        (trans
          (cong (gain *_) (rawRatioTimesInverseFactor shell))
          (ℚRing.solve-∀ gain))

    rightMeaning :
      eta * inverseFactor ≡ requiredHHBadGain eta shell
    rightMeaning =
      ℚRing.solve-∀ eta (inverseDyadicScale shell)
  in
  trans
    (sym leftMeaning)
    (trans scaledCalibration rightMeaning)

record ExactDyadicHHBadCalibration
    (eta : ℚ) (shell : Nat) : Set where
  constructor exact-dyadic-hhbad-calibration
  field
    gain : ℚ
    calibratesExactly :
      gain * rawHHBadRatio shell ≡ eta

open ExactDyadicHHBadCalibration public

exactCalibrationGainForced :
  ∀ {eta shell} →
  (calibration : ExactDyadicHHBadCalibration eta shell) →
  gain calibration ≡ requiredHHBadGain eta shell
exactCalibrationGainForced {eta} {shell} calibration =
  requiredHHBadGainUnique
    eta shell (gain calibration) (calibratesExactly calibration)

exactCalibrationAtSuccessorHalves :
  ∀ eta shell →
  requiredHHBadGain eta (suc shell)
  ≡ half * requiredHHBadGain eta shell
exactCalibrationAtSuccessorHalves =
  requiredHHBadGainHalves

rawHHBadScaleObstructionQuantified : Bool
rawHHBadScaleObstructionQuantified = true

sharpDyadicGainCalibrationClosed : Bool
sharpDyadicGainCalibrationClosed = true

physicalHHBadDyadicGainConstructed : Bool
physicalHHBadDyadicGainConstructed = false

rawHHBadScaleObstructionQuantifiedIsTrue :
  rawHHBadScaleObstructionQuantified ≡ true
rawHHBadScaleObstructionQuantifiedIsTrue = refl

sharpDyadicGainCalibrationClosedIsTrue :
  sharpDyadicGainCalibrationClosed ≡ true
sharpDyadicGainCalibrationClosedIsTrue = refl

physicalHHBadDyadicGainConstructedIsFalse :
  physicalHHBadDyadicGainConstructed ≡ false
physicalHHBadDyadicGainConstructedIsFalse = refl
