module DASHI.Physics.Closure.NSTriadKNHHDirectionalDefectDissipationRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The same directional defect used to unify HH-good and HH-bad lies in [0,1].
-- Therefore its energy-weighted mass cannot exceed the corresponding bad
-- energy mass:
--
--   sum E_i Theta_i <= sum E_i.
--
-- Multiplying by any nonnegative shell/viscosity factor preserves the bound.
-- Combining this with Round 40's exact bad-gain/defect bridge gives the fully
-- finite same-object chain
--
--   delta * Gain_bad
--     <= density * shellFactor * sum E_i Theta_i
--     <= density * shellFactor * sum E_i.
--
-- Hence the finite bad tax already has the exact inverse-threshold form
--
--   Gain_bad <= delta^{-1} density D_bad.
--
-- The remaining PDE issue is not this allocation algebra: it is proving the
-- physical shell/time gain-density constant with the required inverse-scale
-- behaviour and Luo's separate upper critical-dissipation smallness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHUnifiedDirectionalDefectRound40Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadDefectMeasureGainRound40Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadDefectOwnerScalingRound40Exact as Scaling

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = toWitness {a? = 0ℚ ≤? 1ℚ} _

weightedDefectMassBelowBadEnergyMass :
  ∀ {parameter}
    (cells : List (Defect.PhysicalBadDirectionalEnergyCell parameter)) →
  Defect.weightedDirectionalDefectMass cells
  ≤ Defect.badEnergyMass cells
weightedDefectMassBelowBadEnergyMass [] = ℚP.≤-refl
weightedDefectMassBelowBadEnergyMass (cell ∷ rest) =
  let
    directions = Physical.directions (Defect.pair cell)
    theta = Gram.directionalDefect directions

    multiplied :
      Defect.energy cell * theta ≤ Defect.energy cell * 1ℚ
    multiplied =
      L2.nonnegativeProductMonotone
        (Defect.energyNonnegative cell)
        (Gram.directionalDefectNonnegative directions)
        (Defect.energyNonnegative cell)
        oneNonnegative
        ℚP.≤-refl
        (Gram.directionalDefectAtMostOne directions)

    local : Defect.energy cell * theta ≤ Defect.energy cell
    local =
      subst
        (λ upper → Defect.energy cell * theta ≤ upper)
        (solve (Defect.energy cell ∷ []))
        multiplied
  in
  ℚP.+-mono-≤ local (weightedDefectMassBelowBadEnergyMass rest)

scaledWeightedDefectBelowScaledBadEnergy :
  ∀ {parameter}
    (factor : ℚ) →
  0ℚ ≤ factor →
  (cells : List (Defect.PhysicalBadDirectionalEnergyCell parameter)) →
  factor * Defect.weightedDirectionalDefectMass cells
  ≤ factor * Defect.badEnergyMass cells
scaledWeightedDefectBelowScaledBadEnergy factor factorNN cells =
  let instance factorNNI = nonNegative factorNN
  in ℚP.*-monoˡ-≤-nonNeg factor
      (weightedDefectMassBelowBadEnergyMass cells)

sumPhysicalBadGainNonnegative :
  ∀ {parameter effectiveViscosity density shell}
    (cells : List (Gain.PhysicalBadGainDefectCell
      parameter effectiveViscosity density shell)) →
  0ℚ ≤ Gain.sumPhysicalBadGain cells
sumPhysicalBadGainNonnegative [] = ℚP.≤-refl
sumPhysicalBadGainNonnegative (cell ∷ rest) =
  L2.addNonnegative
    (Gain.rawGainNonnegative cell)
    (sumPhysicalBadGainNonnegative rest)

shellViscousFactorNonnegative :
  ∀ effectiveViscosity shell →
  0ℚ ≤ effectiveViscosity →
  0ℚ ≤ Gain.shellViscousFactor effectiveViscosity shell
shellViscousFactorNonnegative effectiveViscosity shell viscosityNN =
  let
    scaleSquareNN = L2.squareNonnegative (Sharp.dyadicScale shell)
    instance
      viscosityNNI = nonNegative viscosityNN
      scaleNNI = nonNegative scaleSquareNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        effectiveViscosity
        (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (Gain.shellViscousFactor effectiveViscosity shell)

finiteBadGainBelowRestrictedDissipationWithInverseThreshold :
  ∀ {parameter effectiveViscosity density shell} →
  0ℚ ≤ density →
  0ℚ ≤ effectiveViscosity →
  (cells : List (Gain.PhysicalBadGainDefectCell
    parameter effectiveViscosity density shell)) →
  Gain.sumPhysicalBadGain cells
  ≤ Threshold.thresholdInverse parameter
      * density
      * Gain.shellViscousFactor effectiveViscosity shell
      * Defect.badEnergyMass (Gain.mapDirectionalCells cells)
finiteBadGainBelowRestrictedDissipationWithInverseThreshold
    {parameter} {effectiveViscosity} {density} {shell}
    densityNN viscosityNN cells =
  let
    factor = Gain.shellViscousFactor effectiveViscosity shell

    factorNN : 0ℚ ≤ factor
    factorNN = shellViscousFactorNonnegative
      effectiveViscosity shell viscosityNN

    densityFactorNN : 0ℚ ≤ density * factor
    densityFactorNN =
      let
        instance
          densityNNI = nonNegative densityNN
          factorNNI = nonNegative factorNN
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg density factor
      in
      ℚP.nonNegative⁻¹ (density * factor)

    thresholdGain :
      Threshold.threshold parameter * Gain.sumPhysicalBadGain cells
      ≤ density * factor
          * Defect.weightedDirectionalDefectMass
              (Gain.mapDirectionalCells cells)
    thresholdGain = Gain.thresholdTimesBadGainBelowDefectCharge
      densityNN viscosityNN cells

    defectToEnergy :
      density * factor
          * Defect.weightedDirectionalDefectMass
              (Gain.mapDirectionalCells cells)
      ≤ density * factor
          * Defect.badEnergyMass (Gain.mapDirectionalCells cells)
    defectToEnergy =
      let instance densityFactorNNI = nonNegative densityFactorNN
      in ℚP.*-monoˡ-≤-nonNeg
          (density * factor)
          (weightedDefectMassBelowBadEnergyMass
            (Gain.mapDirectionalCells cells))

    defectNN = Defect.weightedDirectionalDefectMassNonnegative
      (Gain.mapDirectionalCells cells)
    energyNN = Defect.badEnergyNonnegative (Gain.mapDirectionalCells cells)

    rate : Scaling.BadDefectOwnerRate parameter
    rate = record
      { badGain = Gain.sumPhysicalBadGain cells
      ; defectCharge = density * factor
          * Defect.weightedDirectionalDefectMass
              (Gain.mapDirectionalCells cells)
      ; dissipation = density * factor
          * Defect.badEnergyMass (Gain.mapDirectionalCells cells)
      ; defectRate = 1ℚ
      ; badGainNonnegative = sumPhysicalBadGainNonnegative cells
      ; defectChargeNonnegative =
          let
            instance
              dfNN = nonNegative densityFactorNN
              defectNNI = nonNegative defectNN
              productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
                (density * factor)
                (Defect.weightedDirectionalDefectMass
                  (Gain.mapDirectionalCells cells))
          in ℚP.nonNegative⁻¹
              ((density * factor)
                * Defect.weightedDirectionalDefectMass
                    (Gain.mapDirectionalCells cells))
      ; dissipationNonnegative =
          let
            instance
              dfNN = nonNegative densityFactorNN
              energyNNI = nonNegative energyNN
              productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
                (density * factor)
                (Defect.badEnergyMass (Gain.mapDirectionalCells cells))
          in ℚP.nonNegative⁻¹
              ((density * factor)
                * Defect.badEnergyMass (Gain.mapDirectionalCells cells))
      ; defectRateNonnegative = oneNonnegative
      ; thresholdTimesGainBelowDefect = thresholdGain
      ; defectBelowRateTimesDissipation =
          subst
            (λ upper →
              density * factor
                * Defect.weightedDirectionalDefectMass
                    (Gain.mapDirectionalCells cells)
              ≤ upper)
            (sym (solve
              ( density
              ∷ factor
              ∷ Defect.badEnergyMass (Gain.mapDirectionalCells cells)
              ∷ [])))
            defectToEnergy
      }

    result = Scaling.badGainBelowBOverDeltaDissipation rate

    targetMeaning :
      Threshold.thresholdInverse parameter * 1ℚ
        * (density * factor
          * Defect.badEnergyMass (Gain.mapDirectionalCells cells))
      ≡ Threshold.thresholdInverse parameter
          * density * factor
          * Defect.badEnergyMass (Gain.mapDirectionalCells cells)
    targetMeaning = solve
      ( Threshold.thresholdInverse parameter
      ∷ density
      ∷ factor
      ∷ Defect.badEnergyMass (Gain.mapDirectionalCells cells)
      ∷ [])
  in
  subst
    (λ upper → Gain.sumPhysicalBadGain cells ≤ upper)
    targetMeaning
    result

hhDirectionalDefectDissipationDominationClosed : Bool
hhDirectionalDefectDissipationDominationClosed = true

physicalHHBadInverseShellDensityStillRequired : Bool
physicalHHBadInverseShellDensityStillRequired = true

hhDirectionalDefectDissipationDominationClosedIsTrue :
  hhDirectionalDefectDissipationDominationClosed ≡ true
hhDirectionalDefectDissipationDominationClosedIsTrue = refl
