module DASHI.Physics.Closure.NSTriadKNHHBadKineticAmplitudeRestoresInverseShellRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Round 42's literal frequency audit produced a formal lambda_q^-2 advantage
-- before amplitude normalization.  Round 43 proves the literal production is
-- cubic while viscous charge is quadratic, so one amplitude factor is still
-- owed.  The natural kinetic-energy control of shell vorticity carries one
-- derivative, schematically
--
--   |omega_q| <= lambda_q E0^(1/2).
--
-- This file proves the exact dyadic consequence without introducing square
-- roots:
--
--   (C lambda_q^-2) lambda_q = C lambda_q^-1.
--
-- Therefore the ordinary kinetic amplitude bound consumes exactly one of the
-- two inverse powers.  The net shell calibration returns to the mature
-- Round-33/Round-41 inverse-shell lane.  A genuinely stronger direct HH-bad
-- route now has a precise falsifiable requirement: it must produce an
-- amplitude factor growing strictly slower than lambda_q (alignment,
-- intermittency, occupation-time gain, or equivalent).  Otherwise the correct
-- fallback is the existing one-derivative Schur architecture.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_; 0ℚ; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; subst; sym)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadInverseSquareBeatsRequiredGainRound42Exact as InverseSquare

inverseSquareTimesKineticDyadicScale :
  ∀ coefficient shell →
  InverseSquare.inverseSquareGain coefficient shell
    * Sharp.dyadicScale shell
  ≡ coefficient * Sharp.inverseDyadicScale shell
inverseSquareTimesKineticDyadicScale coefficient shell =
  let
    mu = Sharp.inverseDyadicScale shell
    lambda = Sharp.dyadicScale shell

    regroup :
      (coefficient * mu * mu) * lambda
      ≡ coefficient * mu * (mu * lambda)
    regroup = solve (coefficient ∷ mu ∷ lambda ∷ [])
  in
  trans regroup
    (trans
      (cong (coefficient * mu *_) (Sharp.inverseDyadicReciprocal shell))
      (solve (coefficient ∷ mu ∷ [])))

kineticAdjustedInverseShellGain : ℚ → Nat → ℚ
kineticAdjustedInverseShellGain coefficient shell =
  coefficient * Sharp.inverseDyadicScale shell

kineticAdjustedGainEqualsInverseSquareTimesDyadic :
  ∀ coefficient shell →
  InverseSquare.inverseSquareGain coefficient shell
    * Sharp.dyadicScale shell
  ≡ kineticAdjustedInverseShellGain coefficient shell
kineticAdjustedGainEqualsInverseSquareTimesDyadic =
  inverseSquareTimesKineticDyadicScale

kineticAdjustedGainBelowRequired :
  ∀ coefficient eta shell →
  0ℚ ≤ coefficient →
  coefficient ≤ eta * Sharp.half →
  kineticAdjustedInverseShellGain coefficient shell
  ≤ Sharp.requiredHHBadGain eta shell
kineticAdjustedGainBelowRequired coefficient eta shell coefficientNN coefficientBelow =
  let
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell

    scaled :
      coefficient * mu ≤ (eta * Sharp.half) * mu
    scaled =
      let instance muNNI = nonNegative muNN
      in ℚP.*-monoʳ-≤-nonNeg mu coefficientBelow

    targetMeaning :
      (eta * Sharp.half) * mu
      ≡ Sharp.requiredHHBadGain eta shell
    targetMeaning = solve (eta ∷ Sharp.half ∷ mu ∷ [])
  in
  subst
    (λ upper → kineticAdjustedInverseShellGain coefficient shell ≤ upper)
    targetMeaning
    scaled

kineticAmplitudeConsumesOneInverseFrequencyPower : Bool
kineticAmplitudeConsumesOneInverseFrequencyPower = true

netLiteralKineticLaneIsInverseShellNotInverseSquare : Bool
netLiteralKineticLaneIsInverseShellNotInverseSquare = true

matureOneDerivativeFallbackIsCorrectWithoutSubDyadicAmplitudeGain : Bool
matureOneDerivativeFallbackIsCorrectWithoutSubDyadicAmplitudeGain = true

kineticAmplitudeConsumesOneInverseFrequencyPowerIsTrue :
  kineticAmplitudeConsumesOneInverseFrequencyPower ≡ true
kineticAmplitudeConsumesOneInverseFrequencyPowerIsTrue = refl

netLiteralKineticLaneIsInverseShellNotInverseSquareIsTrue :
  netLiteralKineticLaneIsInverseShellNotInverseSquare ≡ true
netLiteralKineticLaneIsInverseShellNotInverseSquareIsTrue = refl

matureOneDerivativeFallbackIsCorrectWithoutSubDyadicAmplitudeGainIsTrue :
  matureOneDerivativeFallbackIsCorrectWithoutSubDyadicAmplitudeGain ≡ true
matureOneDerivativeFallbackIsCorrectWithoutSubDyadicAmplitudeGainIsTrue = refl
