module DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Test the second concrete HH-bad mechanism suggested by the zero-point / RG
-- analysis: entering a bad stratum may carry a minimum dissipative price.
--
-- At shell q suppose the price is the parabolic one-power floor
--
--   Gamma_q = nu lambda_q,
--
-- and an occupation amount O_q is charged against available dissipation C_q:
--
--   O_q Gamma_q <= C_q.
--
-- Multiplying by the exact dyadic reciprocal gives, constructively,
--
--   O_q nu <= C_q lambda_q^-1.
--
-- Thus a genuine bad-stratum floor would manufacture exactly one inverse shell
-- power.  The transfer theorem is proved here; the physical Navier--Stokes
-- statement that bad membership really implies such a floor remains open and
-- is not promoted by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as LuoBridge

inverseDyadicScaleNonnegative :
  ∀ shell → 0ℚ ≤ Sharp.inverseDyadicScale shell
inverseDyadicScaleNonnegative zero = ℚP.≤-refl
inverseDyadicScaleNonnegative (suc shell) =
  let
    instance
      halfNN = nonNegative LuoBridge.halfNonnegative
      tailNN = nonNegative (inverseDyadicScaleNonnegative shell)
      productNN =
        ℚP.nonNeg*nonNeg⇒nonNeg
          Sharp.half (Sharp.inverseDyadicScale shell)
  in
  ℚP.nonNegative⁻¹
    (Sharp.half * Sharp.inverseDyadicScale shell)

record BadStratumDissipationFloor
    (viscosity : ℚ) (shell : Nat) : Set where
  constructor bad-stratum-dissipation-floor
  field
    occupation : ℚ
    dissipationCharge : ℚ
    floor : ℚ

    occupationNonnegative : 0ℚ ≤ occupation
    chargeNonnegative : 0ℚ ≤ dissipationCharge
    viscosityNonnegative : 0ℚ ≤ viscosity

    floorExact :
      floor ≡ viscosity * Sharp.dyadicScale shell

    occupationChargedToDissipation :
      occupation * floor ≤ dissipationCharge

open BadStratumDissipationFloor public

floorNonnegative :
  ∀ {viscosity shell}
    (cell : BadStratumDissipationFloor viscosity shell) →
  0ℚ ≤ floor cell
floorNonnegative {viscosity} {shell} cell =
  subst
    (0ℚ ≤_)
    (sym (floorExact cell))
    productNonnegative
  where
  productNonnegative :
    0ℚ ≤ viscosity * Sharp.dyadicScale shell
  productNonnegative =
    let
      instance
        viscosityNN = nonNegative (viscosityNonnegative cell)
        scaleNN = nonNegative (LuoBridge.dyadicScaleNonnegative shell)
        productNN =
          ℚP.nonNeg*nonNeg⇒nonNeg viscosity (Sharp.dyadicScale shell)
    in
    ℚP.nonNegative⁻¹ (viscosity * Sharp.dyadicScale shell)

occupationTimesFloorNonnegative :
  ∀ {viscosity shell}
    (cell : BadStratumDissipationFloor viscosity shell) →
  0ℚ ≤ occupation cell * floor cell
occupationTimesFloorNonnegative cell =
  let
    instance
      occupationNN = nonNegative (occupationNonnegative cell)
      floorNN = nonNegative (floorNonnegative cell)
      productNN =
        ℚP.nonNeg*nonNeg⇒nonNeg (occupation cell) (floor cell)
  in
  ℚP.nonNegative⁻¹ (occupation cell * floor cell)

badStratumFloorProducesInverseShellCharging :
  ∀ {viscosity shell}
    (cell : BadStratumDissipationFloor viscosity shell) →
  occupation cell * viscosity
  ≤ dissipationCharge cell * Sharp.inverseDyadicScale shell
badStratumFloorProducesInverseShellCharging
    {viscosity} {shell} cell =
  let
    inverseNN : 0ℚ ≤ Sharp.inverseDyadicScale shell
    inverseNN = inverseDyadicScaleNonnegative shell

    scaledCharge :
      (occupation cell * floor cell) * Sharp.inverseDyadicScale shell
      ≤ dissipationCharge cell * Sharp.inverseDyadicScale shell
    scaledCharge =
      L2.nonnegativeProductMonotone
        (occupationTimesFloorNonnegative cell)
        inverseNN
        (chargeNonnegative cell)
        inverseNN
        (occupationChargedToDissipation cell)
        ℚP.≤-refl

    leftUsesFloor :
      (occupation cell * floor cell) * Sharp.inverseDyadicScale shell
      ≡
      (occupation cell * (viscosity * Sharp.dyadicScale shell))
        * Sharp.inverseDyadicScale shell
    leftUsesFloor =
      cong
        (λ selectedFloor →
          (occupation cell * selectedFloor)
            * Sharp.inverseDyadicScale shell)
        (floorExact cell)

    leftCollapses :
      (occupation cell * (viscosity * Sharp.dyadicScale shell))
        * Sharp.inverseDyadicScale shell
      ≡ occupation cell * viscosity
    leftCollapses =
      trans
        (ℚRing.solve-∀
          (occupation cell)
          viscosity
          (Sharp.dyadicScale shell)
          (Sharp.inverseDyadicScale shell))
        (trans
          (cong
            (occupation cell * viscosity *_)
            (trans
              (ℚRing.solve-∀
                (Sharp.dyadicScale shell)
                (Sharp.inverseDyadicScale shell))
              (Sharp.inverseDyadicReciprocal shell)))
          (ℚRing.solve-∀ (occupation cell) viscosity))

    scaledLeftMeaning :
      (occupation cell * floor cell) * Sharp.inverseDyadicScale shell
      ≡ occupation cell * viscosity
    scaledLeftMeaning = trans leftUsesFloor leftCollapses
  in
  subst
    (λ lower →
      lower ≤ dissipationCharge cell * Sharp.inverseDyadicScale shell)
    scaledLeftMeaning
    scaledCharge

badStratumDissipativeFloorChargingClosed : Bool
badStratumDissipativeFloorChargingClosed = true

physicalBadStratumDissipativeFloorConstructed : Bool
physicalBadStratumDissipativeFloorConstructed = false

badStratumDissipativeFloorChargingClosedIsTrue :
  badStratumDissipativeFloorChargingClosed ≡ true
badStratumDissipativeFloorChargingClosedIsTrue = refl

physicalBadStratumDissipativeFloorConstructedIsFalse :
  physicalBadStratumDissipativeFloorConstructed ≡ false
physicalBadStratumDissipativeFloorConstructedIsFalse = refl
