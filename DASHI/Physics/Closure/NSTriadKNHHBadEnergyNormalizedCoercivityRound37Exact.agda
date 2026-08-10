module DASHI.Physics.Closure.NSTriadKNHHBadEnergyNormalizedCoercivityRound37Exact where

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
-- Round 37 proves that direction-only badness cannot imply an amplitude-
-- independent positive dissipation quantum.  The viable interpretation of the
-- Round-36 floor is therefore a *coercivity rate per unit bad energy*.
--
-- Write E_bad for the energy-weighted occupation of one bad shell and C_bad
-- for the localized dissipation charged to it.  The scale-compatible physical
-- target is
--
--   E_bad (nu_eff lambda_q) <= C_bad,
--
-- equivalently D_bad / E_bad >= nu_eff lambda_q when E_bad is nonzero.  This
-- module proves that such a normalized coercivity cell canonically inhabits
-- the Round-36 `BadStratumDissipationFloor` with occupation = E_bad, and hence
-- obtains the exact inverse-shell charge
--
--   E_bad nu_eff <= C_bad lambda_q^-1.
--
-- It also proves that simultaneous nonnegative rescaling of energy and charge
-- preserves the coercivity inequality.  Thus this ratio formulation survives
-- amplitude scaling, unlike an absolute direction-only floor.  The remaining
-- frontier theorem is genuinely physical: prove this localized coercivity for
-- the actual HH-bad energy of the Galerkin/Navier--Stokes trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as LuoBridge
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor

record BadEnergyCoercivityCell
    (effectiveViscosity : ℚ) (shell : Nat) : Set where
  constructor bad-energy-coercivity-cell
  field
    badEnergy : ℚ
    dissipationCharge : ℚ

    badEnergyNonnegative : 0ℚ ≤ badEnergy
    chargeNonnegative : 0ℚ ≤ dissipationCharge
    effectiveViscosityNonnegative : 0ℚ ≤ effectiveViscosity

    localizedCoercivity :
      badEnergy * (effectiveViscosity * Sharp.dyadicScale shell)
      ≤ dissipationCharge

open BadEnergyCoercivityCell public

energyCoercivityAsRound36Floor :
  ∀ {effectiveViscosity shell} →
  BadEnergyCoercivityCell effectiveViscosity shell →
  Floor.BadStratumDissipationFloor effectiveViscosity shell
energyCoercivityAsRound36Floor {effectiveViscosity} {shell} cell =
  Floor.bad-stratum-dissipation-floor
    (badEnergy cell)
    (dissipationCharge cell)
    (effectiveViscosity * Sharp.dyadicScale shell)
    (badEnergyNonnegative cell)
    (chargeNonnegative cell)
    (effectiveViscosityNonnegative cell)
    refl
    (localizedCoercivity cell)

badEnergyCoercivityProducesInverseShellCharging :
  ∀ {effectiveViscosity shell}
    (cell : BadEnergyCoercivityCell effectiveViscosity shell) →
  badEnergy cell * effectiveViscosity
  ≤ dissipationCharge cell * Sharp.inverseDyadicScale shell
badEnergyCoercivityProducesInverseShellCharging cell =
  Floor.badStratumFloorProducesInverseShellCharging
    (energyCoercivityAsRound36Floor cell)

record NonnegativeRescaling : Set where
  constructor nonnegative-rescaling
  field
    factor : ℚ
    factorNonnegative : 0ℚ ≤ factor

open NonnegativeRescaling public

rescaleBadEnergyCell :
  ∀ {effectiveViscosity shell} →
  NonnegativeRescaling →
  BadEnergyCoercivityCell effectiveViscosity shell →
  BadEnergyCoercivityCell effectiveViscosity shell
rescaleBadEnergyCell {effectiveViscosity} {shell} scaling cell =
  bad-energy-coercivity-cell
    (factor scaling * badEnergy cell)
    (factor scaling * dissipationCharge cell)
    scaledEnergyNN
    scaledChargeNN
    (effectiveViscosityNonnegative cell)
    scaledCoercivity
  where
  scaledEnergyNN : 0ℚ ≤ factor scaling * badEnergy cell
  scaledEnergyNN =
    let
      instance
        factorNN = nonNegative (factorNonnegative scaling)
        energyNN = nonNegative (badEnergyNonnegative cell)
        productNN = ℚP.nonNeg*nonNeg⇒nonNeg
          (factor scaling) (badEnergy cell)
    in
    ℚP.nonNegative⁻¹ (factor scaling * badEnergy cell)

  scaledChargeNN : 0ℚ ≤ factor scaling * dissipationCharge cell
  scaledChargeNN =
    let
      instance
        factorNN = nonNegative (factorNonnegative scaling)
        chargeNN = nonNegative (chargeNonnegative cell)
        productNN = ℚP.nonNeg*nonNeg⇒nonNeg
          (factor scaling) (dissipationCharge cell)
    in
    ℚP.nonNegative⁻¹ (factor scaling * dissipationCharge cell)

  coerciveLeftNN :
    0ℚ ≤ badEnergy cell *
      (effectiveViscosity * Sharp.dyadicScale shell)
  coerciveLeftNN =
    let
      scaleNN : 0ℚ ≤ Sharp.dyadicScale shell
      scaleNN = LuoBridge.dyadicScaleNonnegative shell
      rateNN : 0ℚ ≤ effectiveViscosity * Sharp.dyadicScale shell
      rateNN =
        let
          instance
            viscosityNN = nonNegative (effectiveViscosityNonnegative cell)
            shellNN = nonNegative scaleNN
            productNN = ℚP.nonNeg*nonNeg⇒nonNeg
              effectiveViscosity (Sharp.dyadicScale shell)
        in
        ℚP.nonNegative⁻¹
          (effectiveViscosity * Sharp.dyadicScale shell)
    in
    let
      instance
        energyNN = nonNegative (badEnergyNonnegative cell)
        rateNonnegative = nonNegative rateNN
        productNN = ℚP.nonNeg*nonNeg⇒nonNeg
          (badEnergy cell)
          (effectiveViscosity * Sharp.dyadicScale shell)
    in
    ℚP.nonNegative⁻¹
      (badEnergy cell * (effectiveViscosity * Sharp.dyadicScale shell))

  scaledCoercivity :
    (factor scaling * badEnergy cell)
      * (effectiveViscosity * Sharp.dyadicScale shell)
    ≤ factor scaling * dissipationCharge cell
  scaledCoercivity =
    let
      factorNN = factorNonnegative scaling
      chargeNN = chargeNonnegative cell
      raw :
        factor scaling
          * (badEnergy cell
            * (effectiveViscosity * Sharp.dyadicScale shell))
        ≤ factor scaling * dissipationCharge cell
      raw =
        L2.nonnegativeProductMonotone
          factorNN
          coerciveLeftNN
          factorNN
          chargeNN
          ℚP.≤-refl
          (localizedCoercivity cell)
      leftMeaning :
        factor scaling
          * (badEnergy cell
            * (effectiveViscosity * Sharp.dyadicScale shell))
        ≡
        (factor scaling * badEnergy cell)
          * (effectiveViscosity * Sharp.dyadicScale shell)
      leftMeaning =
        solve
          ( factor scaling
          ∷ badEnergy cell
          ∷ effectiveViscosity
          ∷ Sharp.dyadicScale shell
          ∷ [])
    in
    subst
      (λ lower → lower ≤ factor scaling * dissipationCharge cell)
      leftMeaning
      raw

hhBadEnergyNormalizedCoercivityBridgeClosed : Bool
hhBadEnergyNormalizedCoercivityBridgeClosed = true

physicalHHBadEnergyCoercivityConstructed : Bool
physicalHHBadEnergyCoercivityConstructed = false

hhBadEnergyNormalizedCoercivityBridgeClosedIsTrue :
  hhBadEnergyNormalizedCoercivityBridgeClosed ≡ true
hhBadEnergyNormalizedCoercivityBridgeClosedIsTrue = refl

physicalHHBadEnergyCoercivityConstructedIsFalse :
  physicalHHBadEnergyCoercivityConstructed ≡ false
physicalHHBadEnergyCoercivityConstructedIsFalse = refl
