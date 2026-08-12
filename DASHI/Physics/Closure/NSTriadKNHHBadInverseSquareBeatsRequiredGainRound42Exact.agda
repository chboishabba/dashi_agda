module DASHI.Physics.Closure.NSTriadKNHHBadInverseSquareBeatsRequiredGainRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 33 quantified the half-kernel/Bernstein obstruction: to neutralize
--
--   R_q = 2 lambda_q
--
-- with viscosity tax eta one needs exactly
--
--   requiredGain(eta,q) = (eta/2) lambda_q^-1.
--
-- Round 42's same-object literal production/dissipation scaling is stronger:
-- a base-scale coefficient C transports to shell q with lambda_q^-2.
-- This file proves that an inverse-square gain automatically beats the mature
-- Round-33 inverse-shell requirement whenever the base coefficient satisfies
--
--   C <= eta/2.
--
-- The proof is entirely exact on the repository dyadic rationals.  Since
-- mu_q=2^-q lies in [0,1],
--
--   mu_q^2 <= mu_q,
--
-- hence
--
--   C mu_q^2 <= C mu_q <= (eta/2) mu_q
--                = requiredGain(eta,q).
--
-- This sharpens the falsification experiment.  If the actual HH-bad gain can
-- be connected directly to the literal production-versus-viscous-charge lane
-- with a shell-independent base coefficient C<=eta/2, the older one-derivative
-- Schur compensation is unnecessary: the literal lane already supplies more
-- decay than Round 33 asks for.  The open theorem remains the same-object map
-- from literal production to the actual restricted `rawGain`/owner quantity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Bridge

halfBelowOne : Sharp.half ≤ 1ℚ
halfBelowOne = toWitness {a? = Sharp.half ℚP.≤? 1ℚ} _

inverseDyadicScaleAtMostOne :
  ∀ shell → Sharp.inverseDyadicScale shell ≤ 1ℚ
inverseDyadicScaleAtMostOne zero = ℚP.≤-refl
inverseDyadicScaleAtMostOne (suc shell) =
  let
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell

    halfMuBelowMu : Sharp.half * mu ≤ mu
    halfMuBelowMu =
      let instance muNNI = nonNegative muNN
      in subst
        (λ upper → Sharp.half * mu ≤ upper)
        (ℚP.*-identityˡ mu)
        (ℚP.*-monoʳ-≤-nonNeg mu halfBelowOne)
  in
  ℚP.≤-trans halfMuBelowMu (inverseDyadicScaleAtMostOne shell)

inverseDyadicSquareBelowInverse :
  ∀ shell →
  Sharp.inverseDyadicScale shell * Sharp.inverseDyadicScale shell
  ≤ Sharp.inverseDyadicScale shell
inverseDyadicSquareBelowInverse shell =
  let
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell
    mu≤1 = inverseDyadicScaleAtMostOne shell

    squaredBelowMuTimesOne : mu * mu ≤ mu * 1ℚ
    squaredBelowMuTimesOne =
      let instance muNNI = nonNegative muNN
      in ℚP.*-monoˡ-≤-nonNeg mu mu≤1
  in
  subst
    (λ upper → mu * mu ≤ upper)
    (ℚP.*-identityʳ mu)
    squaredBelowMuTimesOne

inverseSquareGain : ℚ → Nat → ℚ
inverseSquareGain coefficient shell =
  coefficient
    * Sharp.inverseDyadicScale shell
    * Sharp.inverseDyadicScale shell

inverseSquareGainBelowInverseShellSameCoefficient :
  ∀ coefficient shell →
  0ℚ ≤ coefficient →
  inverseSquareGain coefficient shell
  ≤ coefficient * Sharp.inverseDyadicScale shell
inverseSquareGainBelowInverseShellSameCoefficient coefficient shell coefficientNN =
  let
    mu = Sharp.inverseDyadicScale shell
    squareBelow = inverseDyadicSquareBelowInverse shell

    scaled : coefficient * (mu * mu) ≤ coefficient * mu
    scaled =
      let instance coefficientNNI = nonNegative coefficientNN
      in ℚP.*-monoˡ-≤-nonNeg coefficient squareBelow

    leftMeaning :
      inverseSquareGain coefficient shell ≡ coefficient * (mu * mu)
    leftMeaning = solve (coefficient ∷ mu ∷ [])
  in
  subst
    (λ lower → lower ≤ coefficient * mu)
    (sym leftMeaning)
    scaled

inverseSquareGainBelowRequiredHHBadGain :
  ∀ coefficient eta shell →
  0ℚ ≤ coefficient →
  coefficient ≤ eta * Sharp.half →
  inverseSquareGain coefficient shell
  ≤ Sharp.requiredHHBadGain eta shell
inverseSquareGainBelowRequiredHHBadGain coefficient eta shell coefficientNN coefficient≤HalfEta =
  let
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell

    squareToInverse :
      inverseSquareGain coefficient shell ≤ coefficient * mu
    squareToInverse =
      inverseSquareGainBelowInverseShellSameCoefficient
        coefficient shell coefficientNN

    coefficientToRequired :
      coefficient * mu ≤ (eta * Sharp.half) * mu
    coefficientToRequired =
      let instance muNNI = nonNegative muNN
      in ℚP.*-monoʳ-≤-nonNeg mu coefficient≤HalfEta
  in
  ℚP.≤-trans squareToInverse coefficientToRequired

inverseSquareGainSatisfiesRound33CalibrationEnvelope :
  ∀ coefficient eta shell →
  0ℚ ≤ coefficient →
  coefficient ≤ eta * Sharp.half →
  inverseSquareGain coefficient shell * Sharp.rawHHBadRatio shell
  ≤ eta
inverseSquareGainSatisfiesRound33CalibrationEnvelope
    coefficient eta shell coefficientNN coefficient≤HalfEta =
  let
    gainBelowRequired =
      inverseSquareGainBelowRequiredHHBadGain
        coefficient eta shell coefficientNN coefficient≤HalfEta

    ratioNN : 0ℚ ≤ Sharp.rawHHBadRatio shell
    ratioNN =
      let
        instance
          twoNNI = nonNegative Bridge.twoNonnegative
          scaleNNI = nonNegative (Bridge.dyadicScaleNonnegative shell)
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            Sharp.two (Sharp.dyadicScale shell)
      in
      ℚP.nonNegative⁻¹ (Sharp.rawHHBadRatio shell)

    scaled :
      inverseSquareGain coefficient shell * Sharp.rawHHBadRatio shell
      ≤ Sharp.requiredHHBadGain eta shell * Sharp.rawHHBadRatio shell
    scaled =
      let instance ratioNNI = nonNegative ratioNN
      in ℚP.*-monoʳ-≤-nonNeg (Sharp.rawHHBadRatio shell) gainBelowRequired
  in
  subst
    (λ upper → inverseSquareGain coefficient shell * Sharp.rawHHBadRatio shell ≤ upper)
    (Sharp.requiredHHBadGainCalibration eta shell)
    scaled

inverseSquareBeatsRequiredInverseShellClosed : Bool
inverseSquareBeatsRequiredInverseShellClosed = true

inverseSquareGainClosesRound33ScaleEnvelope : Bool
inverseSquareGainClosesRound33ScaleEnvelope = true

physicalLiteralProductionToRawBadGainSameObjectStillRequired : Bool
physicalLiteralProductionToRawBadGainSameObjectStillRequired = true

inverseSquareBeatsRequiredInverseShellClosedIsTrue :
  inverseSquareBeatsRequiredInverseShellClosed ≡ true
inverseSquareBeatsRequiredInverseShellClosedIsTrue = refl
