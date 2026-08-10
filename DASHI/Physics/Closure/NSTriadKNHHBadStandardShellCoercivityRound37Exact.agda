module DASHI.Physics.Closure.NSTriadKNHHBadStandardShellCoercivityRound37Exact where

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
-- Audit how much of the repaired Round-37 HH-bad coercivity target is actually
-- difficult.  For the dyadic scale lambda_q=2^q, prove lambda_q >= 1 and hence
--
--   lambda_q <= lambda_q^2.
--
-- Therefore, for nonnegative bad-shell energy E and viscosity nu, the *full
-- shell viscous charge*
--
--   C_full = E nu lambda_q^2
--
-- automatically satisfies
--
--   E (nu lambda_q) <= C_full.
--
-- This canonically constructs the Round-37 normalized coercivity cell and its
-- inverse-shell consequence.  It also sharpens the frontier: the hard A6
-- theorem cannot merely be this elementary shell coercivity.  It must prove
-- that the particular dissipation charge available to the HH-bad owner really
-- contains the required portion of full shell viscosity and that the physical
-- HH-bad gain/occupation is linked to the corresponding energy quantity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as LuoBridge
import DASHI.Physics.Closure.NSTriadKNHHBadEnergyNormalizedCoercivityRound37Exact as Normalized

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = toWitness {a? = 0ℚ ≤? 1ℚ} _

oneBelowTwo : 1ℚ ≤ Sharp.two
oneBelowTwo = toWitness {a? = 1ℚ ≤? Sharp.two} _

dyadicScaleAtLeastOne : ∀ shell → 1ℚ ≤ Sharp.dyadicScale shell
dyadicScaleAtLeastOne zero = ℚP.≤-refl
dyadicScaleAtLeastOne (suc shell) =
  ℚP.≤-trans
    (dyadicScaleAtLeastOne shell)
    scaleBelowDouble
  where
  scaleBelowDouble :
    Sharp.dyadicScale shell
    ≤ Sharp.two * Sharp.dyadicScale shell
  scaleBelowDouble =
    let
      scaleNN = LuoBridge.dyadicScaleNonnegative shell
      raw :
        1ℚ * Sharp.dyadicScale shell
        ≤ Sharp.two * Sharp.dyadicScale shell
      raw =
        L2.nonnegativeProductMonotone
          oneNonnegative scaleNN
          LuoBridge.twoNonnegative scaleNN
          oneBelowTwo ℚP.≤-refl
    in
    subst
      (λ lower →
        lower ≤ Sharp.two * Sharp.dyadicScale shell)
      (solve (Sharp.dyadicScale shell ∷ []))
      raw

dyadicScaleBelowSquare : ∀ shell →
  Sharp.dyadicScale shell
  ≤ Sharp.dyadicScale shell * Sharp.dyadicScale shell
dyadicScaleBelowSquare shell =
  let
    scale = Sharp.dyadicScale shell
    scaleNN = LuoBridge.dyadicScaleNonnegative shell
    raw : scale * 1ℚ ≤ scale * scale
    raw =
      let
        instance
          scaleNonnegative = nonNegative scaleNN
      in
      ℚP.*-monoˡ-≤-nonNeg scale (dyadicScaleAtLeastOne shell)
  in
  subst
    (λ lower → lower ≤ scale * scale)
    (solve (scale ∷ []))
    raw

record FullShellViscousCharge (effectiveViscosity : ℚ) (shell : Nat) : Set where
  constructor full-shell-viscous-charge
  field
    badEnergy : ℚ
    badEnergyNonnegative : 0ℚ ≤ badEnergy
    effectiveViscosityNonnegative : 0ℚ ≤ effectiveViscosity

open FullShellViscousCharge public

fullViscousCharge :
  ∀ {effectiveViscosity shell} →
  FullShellViscousCharge effectiveViscosity shell → ℚ
fullViscousCharge {effectiveViscosity} {shell} charge =
  badEnergy charge * effectiveViscosity
  * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)

fullViscousChargeNonnegative :
  ∀ {effectiveViscosity shell}
    (charge : FullShellViscousCharge effectiveViscosity shell) →
  0ℚ ≤ fullViscousCharge charge
fullViscousChargeNonnegative {effectiveViscosity} {shell} charge =
  let
    energyViscosityNN :
      0ℚ ≤ badEnergy charge * effectiveViscosity
    energyViscosityNN =
      let
        instance
          energyNN = nonNegative (badEnergyNonnegative charge)
          viscosityNN = nonNegative
            (effectiveViscosityNonnegative charge)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (badEnergy charge) effectiveViscosity
      in
      ℚP.nonNegative⁻¹ (badEnergy charge * effectiveViscosity)

    scaleSquareNN :
      0ℚ ≤ Sharp.dyadicScale shell * Sharp.dyadicScale shell
    scaleSquareNN =
      let
        instance
          leftNN = nonNegative (LuoBridge.dyadicScaleNonnegative shell)
          rightNN = nonNegative (LuoBridge.dyadicScaleNonnegative shell)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (Sharp.dyadicScale shell) (Sharp.dyadicScale shell)
      in
      ℚP.nonNegative⁻¹
        (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
  in
  let
    instance
      prefactorNN = nonNegative energyViscosityNN
      squareNN = nonNegative scaleSquareNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (badEnergy charge * effectiveViscosity)
        (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (fullViscousCharge charge)

fullShellViscosityDominatesNormalizedRate :
  ∀ {effectiveViscosity shell}
    (charge : FullShellViscousCharge effectiveViscosity shell) →
  badEnergy charge *
    (effectiveViscosity * Sharp.dyadicScale shell)
  ≤ fullViscousCharge charge
fullShellViscosityDominatesNormalizedRate
    {effectiveViscosity} {shell} charge =
  let
    prefactor = badEnergy charge * effectiveViscosity
    prefactorNN : 0ℚ ≤ prefactor
    prefactorNN =
      let
        instance
          energyNN = nonNegative (badEnergyNonnegative charge)
          viscosityNN = nonNegative
            (effectiveViscosityNonnegative charge)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg
            (badEnergy charge) effectiveViscosity
      in
      ℚP.nonNegative⁻¹ prefactor

    raw :
      prefactor * Sharp.dyadicScale shell
      ≤ prefactor
        * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
    raw =
      let
        instance
          prefactorNonnegative = nonNegative prefactorNN
      in
      ℚP.*-monoˡ-≤-nonNeg
        prefactor (dyadicScaleBelowSquare shell)
  in
  subst₂ _≤_
    (solve
      ( badEnergy charge
      ∷ effectiveViscosity
      ∷ Sharp.dyadicScale shell
      ∷ []))
    refl
    raw

fullShellViscosityConstructsBadEnergyCoercivity :
  ∀ {effectiveViscosity shell} →
  FullShellViscousCharge effectiveViscosity shell →
  Normalized.BadEnergyCoercivityCell effectiveViscosity shell
fullShellViscosityConstructsBadEnergyCoercivity charge =
  Normalized.bad-energy-coercivity-cell
    (badEnergy charge)
    (fullViscousCharge charge)
    (badEnergyNonnegative charge)
    (fullViscousChargeNonnegative charge)
    (effectiveViscosityNonnegative charge)
    (fullShellViscosityDominatesNormalizedRate charge)

fullShellViscosityProducesInverseShellCharging :
  ∀ {effectiveViscosity shell}
    (charge : FullShellViscousCharge effectiveViscosity shell) →
  badEnergy charge * effectiveViscosity
  ≤ fullViscousCharge charge * Sharp.inverseDyadicScale shell
fullShellViscosityProducesInverseShellCharging charge =
  Normalized.badEnergyCoercivityProducesInverseShellCharging
    (fullShellViscosityConstructsBadEnergyCoercivity charge)

standardShellCoercivityClosed : Bool
standardShellCoercivityClosed = true

physicalHHBadGainLinkedToBadEnergyConstructed : Bool
physicalHHBadGainLinkedToBadEnergyConstructed = false

physicalHHBadChargeContainsFullShellViscosityConstructed : Bool
physicalHHBadChargeContainsFullShellViscosityConstructed = false

standardShellCoercivityClosedIsTrue :
  standardShellCoercivityClosed ≡ true
standardShellCoercivityClosedIsTrue = refl

physicalHHBadGainLinkedToBadEnergyConstructedIsFalse :
  physicalHHBadGainLinkedToBadEnergyConstructed ≡ false
physicalHHBadGainLinkedToBadEnergyConstructedIsFalse = refl

physicalHHBadChargeContainsFullShellViscosityConstructedIsFalse :
  physicalHHBadChargeContainsFullShellViscosityConstructed ≡ false
physicalHHBadChargeContainsFullShellViscosityConstructedIsFalse = refl
