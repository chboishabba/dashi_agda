module DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Luo's cutoff-dissipation argument uses parabolic time windows and identifies
-- the critical high-frequency dissipation scale D_p ~ lambda_p^-1.  The
-- regularity bootstrap is driven by smallness of the scale-weighted localized
-- dissipation lambda_p D_p at sufficiently high p.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 33 proved that the raw HH-bad Bernstein ratio
--
--   R_q = 2 lambda_q
--
-- can be exactly calibrated to owner coefficient eta only by a gain of order
--
--   (eta / 2) lambda_q^-1.
--
-- The present module proves that Luo's critical *dissipation* scale has
-- exactly that algebraic shape.  With arbitrary viscosity nu, if a localized
-- dissipation gain D_q satisfies
--
--   lambda_q D_q <= (eta / 2) nu,
--
-- then
--
--   D_q R_q <= eta nu.
--
-- At the exact target
--
--   D_q = (eta / 2) nu lambda_q^-1
--
-- equality holds.  More generally, any physical HH-bad gain G_q with
--
--   0 <= G_q <= D_q
--
-- inherits the same absorption calibration.
--
-- This is a substantive route refinement: the missing inverse shell power can
-- be sought in a Luo-style localized-dissipation estimate rather than in the
-- literal length of the parabolic time interval.  The module does NOT assert
-- that the repository's HH-bad gain is already bounded by Luo's D_q, nor does
-- it assert the required Navier--Stokes smallness theorem.  Those are the two
-- remaining physical producer statements.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

------------------------------------------------------------------------
-- Positivity of the dyadic scales used by the ordered-field transport.
------------------------------------------------------------------------

twoNonnegative : 0ℚ ≤ Sharp.two
twoNonnegative = toWitness {a? = 0ℚ ≤? Sharp.two} _

halfNonnegative : 0ℚ ≤ Sharp.half
halfNonnegative = toWitness {a? = 0ℚ ≤? Sharp.half} _

dyadicScaleNonnegative : ∀ shell → 0ℚ ≤ Sharp.dyadicScale shell
dyadicScaleNonnegative zero = ℚP.≤-refl
dyadicScaleNonnegative (suc shell) =
  let
    instance
      twoNN = nonNegative twoNonnegative
      shellNN = nonNegative (dyadicScaleNonnegative shell)
      productNN =
        ℚP.nonNeg*nonNeg⇒nonNeg
          Sharp.two (Sharp.dyadicScale shell)
  in
  ℚP.nonNegative⁻¹
    (Sharp.two * Sharp.dyadicScale shell)

rawRatioNonnegative : ∀ shell → 0ℚ ≤ Sharp.rawHHBadRatio shell
rawRatioNonnegative shell =
  let
    instance
      twoNN = nonNegative twoNonnegative
      scaleNN = nonNegative (dyadicScaleNonnegative shell)
      productNN =
        ℚP.nonNeg*nonNeg⇒nonNeg
          Sharp.two (Sharp.dyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (Sharp.rawHHBadRatio shell)

------------------------------------------------------------------------
-- Exact Luo-critical target at one dyadic shell.
------------------------------------------------------------------------

criticalLocalizedDissipationTarget : ℚ → ℚ → Nat → ℚ
criticalLocalizedDissipationTarget eta viscosity shell =
  eta * Sharp.half * viscosity * Sharp.inverseDyadicScale shell

criticalTargetTimesRawRatio :
  ∀ eta viscosity shell →
  criticalLocalizedDissipationTarget eta viscosity shell
    * Sharp.rawHHBadRatio shell
  ≡ eta * viscosity
criticalTargetTimesRawRatio eta viscosity shell =
  trans
    (ℚRing.solve-∀
      eta viscosity
      (Sharp.inverseDyadicScale shell)
      (Sharp.dyadicScale shell))
    (trans
      (cong
        (eta * viscosity *_)
        (Sharp.inverseDyadicReciprocal shell))
      (ℚRing.solve-∀ eta viscosity))

criticalTargetScaleWeighted :
  ∀ eta viscosity shell →
  Sharp.dyadicScale shell
    * criticalLocalizedDissipationTarget eta viscosity shell
  ≡ eta * Sharp.half * viscosity
criticalTargetScaleWeighted eta viscosity shell =
  trans
    (ℚRing.solve-∀
      eta viscosity
      (Sharp.dyadicScale shell)
      (Sharp.inverseDyadicScale shell))
    (trans
      (cong
        (eta * Sharp.half * viscosity *_)
        (Sharp.inverseDyadicReciprocal shell))
      (ℚRing.solve-∀ eta viscosity))

record LuoCriticalDissipationCell (eta viscosity : ℚ) (shell : Nat) : Set where
  constructor luo-critical-dissipation-cell
  field
    localizedDissipation : ℚ
    localizedDissipationNonnegative : 0ℚ ≤ localizedDissipation
    etaNonnegative : 0ℚ ≤ eta
    viscosityNonnegative : 0ℚ ≤ viscosity

    scaleWeightedCriticalSmallness :
      Sharp.dyadicScale shell * localizedDissipation
      ≤ eta * Sharp.half * viscosity

open LuoCriticalDissipationCell public

criticalDissipationAbsorbsRawHHBadRatio :
  ∀ {eta viscosity shell} →
  (cell : LuoCriticalDissipationCell eta viscosity shell) →
  localizedDissipation cell * Sharp.rawHHBadRatio shell
  ≤ eta * viscosity
criticalDissipationAbsorbsRawHHBadRatio
    {eta} {viscosity} {shell} cell =
  let
    doubled :
      Sharp.two
        * (Sharp.dyadicScale shell * localizedDissipation cell)
      ≤ Sharp.two * (eta * Sharp.half * viscosity)
    doubled =
      L2.nonnegativeProductMonotone
        twoNonnegative
        productNonnegative
        twoNonnegative
        targetNonnegative
        ℚP.≤-refl
        (scaleWeightedCriticalSmallness cell)

    leftMeaning :
      Sharp.two
        * (Sharp.dyadicScale shell * localizedDissipation cell)
      ≡ localizedDissipation cell * Sharp.rawHHBadRatio shell
    leftMeaning =
      ℚRing.solve-∀
        (Sharp.dyadicScale shell)
        (localizedDissipation cell)

    rightMeaning :
      Sharp.two * (eta * Sharp.half * viscosity)
      ≡ eta * viscosity
    rightMeaning =
      ℚRing.solve-∀ eta viscosity
  in
  subst
    (λ lower → lower ≤ eta * viscosity)
    leftMeaning
    (subst
      (λ upper →
        Sharp.two
          * (Sharp.dyadicScale shell * localizedDissipation cell)
        ≤ upper)
      rightMeaning
      doubled)
  where
  productNonnegative :
    0ℚ ≤ Sharp.dyadicScale shell * localizedDissipation cell
  productNonnegative =
    let
      instance
        scaleNN = nonNegative (dyadicScaleNonnegative shell)
        dissipationNN =
          nonNegative (localizedDissipationNonnegative cell)
        productNN =
          ℚP.nonNeg*nonNeg⇒nonNeg
            (Sharp.dyadicScale shell)
            (localizedDissipation cell)
    in
    ℚP.nonNegative⁻¹
      (Sharp.dyadicScale shell * localizedDissipation cell)

  etaHalfNonnegative : 0ℚ ≤ eta * Sharp.half
  etaHalfNonnegative =
    let
      instance
        etaNN = nonNegative (etaNonnegative cell)
        halfNN = nonNegative halfNonnegative
        productNN = ℚP.nonNeg*nonNeg⇒nonNeg eta Sharp.half
    in
    ℚP.nonNegative⁻¹ (eta * Sharp.half)

  targetNonnegative : 0ℚ ≤ eta * Sharp.half * viscosity
  targetNonnegative =
    let
      instance
        etaHalfNN = nonNegative etaHalfNonnegative
        viscosityNN = nonNegative (viscosityNonnegative cell)
        productNN =
          ℚP.nonNeg*nonNeg⇒nonNeg
            (eta * Sharp.half) viscosity
    in
    ℚP.nonNegative⁻¹ (eta * Sharp.half * viscosity)

------------------------------------------------------------------------
-- Physical HH-bad gain <= localized dissipation transports the calibration.
------------------------------------------------------------------------

record HHBadGainBelowCriticalDissipation
    {eta viscosity : ℚ} {shell : Nat}
    (cell : LuoCriticalDissipationCell eta viscosity shell) : Set where
  constructor hhbad-gain-below-critical-dissipation
  field
    physicalGain : ℚ
    physicalGainNonnegative : 0ℚ ≤ physicalGain
    gainBelowLocalizedDissipation :
      physicalGain ≤ localizedDissipation cell

open HHBadGainBelowCriticalDissipation public

criticalDissipationControlsPhysicalHHBadGain :
  ∀ {eta viscosity shell}
    {cell : LuoCriticalDissipationCell eta viscosity shell} →
  (link : HHBadGainBelowCriticalDissipation cell) →
  physicalGain link * Sharp.rawHHBadRatio shell
  ≤ eta * viscosity
criticalDissipationControlsPhysicalHHBadGain
    {eta} {viscosity} {shell} {cell} link =
  let
    multiplyGain :
      physicalGain link * Sharp.rawHHBadRatio shell
      ≤ localizedDissipation cell * Sharp.rawHHBadRatio shell
    multiplyGain =
      L2.nonnegativeProductMonotone
        (physicalGainNonnegative link)
        (rawRatioNonnegative shell)
        (localizedDissipationNonnegative cell)
        (rawRatioNonnegative shell)
        (gainBelowLocalizedDissipation link)
        ℚP.≤-refl
  in
  ℚP.≤-trans
    multiplyGain
    (criticalDissipationAbsorbsRawHHBadRatio cell)

record PhysicalLuoHHBadBridge
    (eta viscosity : ℚ) (shell : Nat) : Set where
  constructor physical-luo-hhbad-bridge
  field
    criticalCell : LuoCriticalDissipationCell eta viscosity shell
    gainLink : HHBadGainBelowCriticalDissipation criticalCell

open PhysicalLuoHHBadBridge public

physicalLuoHHBadBridgeAbsorbs :
  ∀ {eta viscosity shell} →
  (bridge : PhysicalLuoHHBadBridge eta viscosity shell) →
  physicalGain (gainLink bridge) * Sharp.rawHHBadRatio shell
  ≤ eta * viscosity
physicalLuoHHBadBridgeAbsorbs bridge =
  criticalDissipationControlsPhysicalHHBadGain (gainLink bridge)

luoCriticalDissipationCalibrationClosed : Bool
luoCriticalDissipationCalibrationClosed = true

physicalLuoCriticalDissipationEstimateConstructed : Bool
physicalLuoCriticalDissipationEstimateConstructed = false

physicalHHBadGainToLuoDissipationLinkConstructed : Bool
physicalHHBadGainToLuoDissipationLinkConstructed = false

luoCriticalDissipationCalibrationClosedIsTrue :
  luoCriticalDissipationCalibrationClosed ≡ true
luoCriticalDissipationCalibrationClosedIsTrue = refl

physicalLuoCriticalDissipationEstimateConstructedIsFalse :
  physicalLuoCriticalDissipationEstimateConstructed ≡ false
physicalLuoCriticalDissipationEstimateConstructedIsFalse = refl

physicalHHBadGainToLuoDissipationLinkConstructedIsFalse :
  physicalHHBadGainToLuoDissipationLinkConstructed ≡ false
physicalHHBadGainToLuoDissipationLinkConstructedIsFalse = refl
