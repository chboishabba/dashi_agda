module DASHI.Physics.Closure.NSTriadKNHHBadDefectMeasureGainRound40Exact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Connect Round 39's same-object HH-bad gain-density theorem to Round 40's
-- unified energy-weighted directional defect.  Every cell here is physically
-- bad because its defect satisfies delta <= Theta; it is converted to the
-- Round-38/39 bad-tagged energy sample with the tag definitionally true.
--
-- If the actual bad nonlinear gain obeys the already-chosen pointwise density
-- estimate against restricted shell viscosity, then finite summation gives
--
--   Gain_bad <= density * C_bad.
--
-- Round 40's weighted Markov bridge gives
--
--   delta * E_bad <= ETheta.
--
-- Since C_bad is exactly shellFactor * E_bad, these combine without dividing
-- by delta:
--
--   delta * Gain_bad
--     <= density * shellFactor * ETheta.
--
-- This is the precise sense in which the *same* directional-defect measure can
-- feed the HH-bad lane.  No derivative of the Boolean classifier occurs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedDissipationRound38Exact as Diss
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHUnifiedDirectionalDefectRound40Exact as Defect
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

record PhysicalBadGainDefectCell
    (parameter : Threshold.PositiveThreshold)
    (effectiveViscosity density : ℚ)
    (shell : Nat) : Set where
  constructor physical-bad-gain-defect-cell
  field
    directionalCell : Defect.PhysicalBadDirectionalEnergyCell parameter
    rawGain : ℚ
    rawGainNonnegative : 0ℚ ≤ rawGain
    viscousChargeNonnegative :
      0ℚ ≤
        Defect.energy directionalCell
        * effectiveViscosity
        * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
    densityBound :
      rawGain
      ≤ density
        * (Defect.energy directionalCell
          * effectiveViscosity
          * (Sharp.dyadicScale shell * Sharp.dyadicScale shell))

open PhysicalBadGainDefectCell public

toBadEnergySample :
  ∀ {parameter effectiveViscosity density shell} →
  PhysicalBadGainDefectCell parameter effectiveViscosity density shell →
  Diss.BadTaggedEnergySample
toBadEnergySample cell =
  Diss.bad-tagged-energy-sample
    true
    (Defect.energy (directionalCell cell))
    (Defect.energyNonnegative (directionalCell cell))

toRawBadGainSample :
  ∀ {parameter effectiveViscosity density shell} →
  PhysicalBadGainDefectCell parameter effectiveViscosity density shell →
  Gain.RawBadGainSample
toRawBadGainSample cell =
  Gain.raw-bad-gain-sample
    (toBadEnergySample cell)
    (rawGain cell)
    (rawGainNonnegative cell)

toRestrictedGainCell :
  ∀ {parameter effectiveViscosity density shell} →
  PhysicalBadGainDefectCell parameter effectiveViscosity density shell →
  Gain.RestrictedGainDensityCell effectiveViscosity density shell
toRestrictedGainCell cell =
  Gain.restricted-gain-density-cell
    (toRawBadGainSample cell)
    (viscousChargeNonnegative cell)
    (densityBound cell)

mapRestrictedGainCells :
  ∀ {parameter effectiveViscosity density shell} →
  List (PhysicalBadGainDefectCell
    parameter effectiveViscosity density shell) →
  List (Gain.RestrictedGainDensityCell
    effectiveViscosity density shell)
mapRestrictedGainCells [] = []
mapRestrictedGainCells (cell ∷ rest) =
  toRestrictedGainCell cell ∷ mapRestrictedGainCells rest

mapDirectionalCells :
  ∀ {parameter effectiveViscosity density shell} →
  List (PhysicalBadGainDefectCell
    parameter effectiveViscosity density shell) →
  List (Defect.PhysicalBadDirectionalEnergyCell parameter)
mapDirectionalCells [] = []
mapDirectionalCells (cell ∷ rest) =
  directionalCell cell ∷ mapDirectionalCells rest

sumPhysicalBadGain :
  ∀ {parameter effectiveViscosity density shell} →
  List (PhysicalBadGainDefectCell
    parameter effectiveViscosity density shell) → ℚ
sumPhysicalBadGain [] = 0ℚ
sumPhysicalBadGain (cell ∷ rest) =
  rawGain cell + sumPhysicalBadGain rest

sumPhysicalBadGainMatchesRound39 :
  ∀ {parameter effectiveViscosity density shell}
    (cells : List (PhysicalBadGainDefectCell
      parameter effectiveViscosity density shell)) →
  sumPhysicalBadGain cells
  ≡ Gain.sumCellGain (mapRestrictedGainCells cells)
sumPhysicalBadGainMatchesRound39 [] = refl
sumPhysicalBadGainMatchesRound39 (cell ∷ rest) =
  cong (rawGain cell +_)
    (sumPhysicalBadGainMatchesRound39 rest)

shellViscousFactor : ℚ → Nat → ℚ
shellViscousFactor effectiveViscosity shell =
  effectiveViscosity
    * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)

sumRound39ChargeEqualsFactorTimesBadEnergy :
  ∀ {parameter effectiveViscosity density shell}
    (cells : List (PhysicalBadGainDefectCell
      parameter effectiveViscosity density shell)) →
  Gain.sumCellViscousCharge (mapRestrictedGainCells cells)
  ≡ shellViscousFactor effectiveViscosity shell
      * Defect.badEnergyMass (mapDirectionalCells cells)
sumRound39ChargeEqualsFactorTimesBadEnergy
    {effectiveViscosity = effectiveViscosity}
    {shell = shell} [] =
  solve (effectiveViscosity ∷ Sharp.dyadicScale shell ∷ [])
sumRound39ChargeEqualsFactorTimesBadEnergy
    {effectiveViscosity = effectiveViscosity}
    {shell = shell} (cell ∷ rest)
  rewrite sumRound39ChargeEqualsFactorTimesBadEnergy rest =
  solve
    ( Defect.energy (directionalCell cell)
    ∷ Defect.badEnergyMass (mapDirectionalCells rest)
    ∷ effectiveViscosity
    ∷ Sharp.dyadicScale shell
    ∷ [])

finitePhysicalBadGainDensityBound :
  ∀ {parameter effectiveViscosity density shell} →
  0ℚ ≤ density →
  (cells : List (PhysicalBadGainDefectCell
    parameter effectiveViscosity density shell)) →
  sumPhysicalBadGain cells
  ≤ density
      * Gain.sumCellViscousCharge (mapRestrictedGainCells cells)
finitePhysicalBadGainDensityBound {density = density} densityNN cells =
  subst
    (λ lower →
      lower
      ≤ density * Gain.sumCellViscousCharge (mapRestrictedGainCells cells))
    (sym (sumPhysicalBadGainMatchesRound39 cells))
    (Gain.finiteRestrictedGainDensityBound
      densityNN (mapRestrictedGainCells cells))

thresholdTimesBadGainBelowDefectCharge :
  ∀ {parameter effectiveViscosity density shell} →
  0ℚ ≤ density →
  0ℚ ≤ effectiveViscosity →
  (cells : List (PhysicalBadGainDefectCell
    parameter effectiveViscosity density shell)) →
  Threshold.threshold parameter * sumPhysicalBadGain cells
  ≤ density * shellViscousFactor effectiveViscosity shell
      * Defect.weightedDirectionalDefectMass (mapDirectionalCells cells)
thresholdTimesBadGainBelowDefectCharge
    {parameter} {effectiveViscosity} {density} {shell}
    densityNN viscosityNN cells =
  let
    gainToCharge :
      sumPhysicalBadGain cells
      ≤ density
          * Gain.sumCellViscousCharge (mapRestrictedGainCells cells)
    gainToCharge = finitePhysicalBadGainDensityBound densityNN cells

    thresholdNN = Threshold.thresholdNonnegative parameter

    scaledGain :
      Threshold.threshold parameter * sumPhysicalBadGain cells
      ≤ Threshold.threshold parameter
          * (density
            * Gain.sumCellViscousCharge (mapRestrictedGainCells cells))
    scaledGain =
      let instance thresholdNNI = nonNegative thresholdNN
      in ℚP.*-monoˡ-≤-nonNeg
        (Threshold.threshold parameter) gainToCharge

    factorNN : 0ℚ ≤ shellViscousFactor effectiveViscosity shell
    factorNN =
      let
        scaleNN = L2.squareNonnegative (Sharp.dyadicScale shell)
        instance
          viscosityNNI = nonNegative viscosityNN
          scaleNNI = nonNegative scaleNN
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            effectiveViscosity
            (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
      in
      ℚP.nonNegative⁻¹ (shellViscousFactor effectiveViscosity shell)

    densityFactorNN :
      0ℚ ≤ density * shellViscousFactor effectiveViscosity shell
    densityFactorNN =
      let
        instance
          densityNNI = nonNegative densityNN
          factorNNI = nonNegative factorNN
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
            density (shellViscousFactor effectiveViscosity shell)
      in
      ℚP.nonNegative⁻¹
        (density * shellViscousFactor effectiveViscosity shell)

    defectControl :
      Threshold.threshold parameter
        * Defect.badEnergyMass (mapDirectionalCells cells)
      ≤ Defect.weightedDirectionalDefectMass (mapDirectionalCells cells)
    defectControl =
      Defect.thresholdTimesBadEnergyBelowDirectionalDefect
        (mapDirectionalCells cells)

    scaledDefect :
      density * shellViscousFactor effectiveViscosity shell
        * (Threshold.threshold parameter
          * Defect.badEnergyMass (mapDirectionalCells cells))
      ≤ density * shellViscousFactor effectiveViscosity shell
          * Defect.weightedDirectionalDefectMass (mapDirectionalCells cells)
    scaledDefect =
      let instance densityFactorNNI = nonNegative densityFactorNN
      in ℚP.*-monoˡ-≤-nonNeg
        (density * shellViscousFactor effectiveViscosity shell)
        defectControl

    middleMeaning :
      Threshold.threshold parameter
        * (density
          * Gain.sumCellViscousCharge (mapRestrictedGainCells cells))
      ≡ density * shellViscousFactor effectiveViscosity shell
          * (Threshold.threshold parameter
            * Defect.badEnergyMass (mapDirectionalCells cells))
    middleMeaning
      rewrite sumRound39ChargeEqualsFactorTimesBadEnergy cells =
      solve
        ( Threshold.threshold parameter
        ∷ density
        ∷ shellViscousFactor effectiveViscosity shell
        ∷ Defect.badEnergyMass (mapDirectionalCells cells)
        ∷ [])
  in
  ℚP.≤-trans
    scaledGain
    (subst
      (λ lower →
        lower
        ≤ density * shellViscousFactor effectiveViscosity shell
            * Defect.weightedDirectionalDefectMass (mapDirectionalCells cells))
      (sym middleMeaning)
      scaledDefect)

hhBadDefectMeasureGainBridgeClosed : Bool
hhBadDefectMeasureGainBridgeClosed = true

physicalDirectionalDefectOwnerRateConstructed : Bool
physicalDirectionalDefectOwnerRateConstructed = false

hhBadDefectMeasureGainBridgeClosedIsTrue :
  hhBadDefectMeasureGainBridgeClosed ≡ true
hhBadDefectMeasureGainBridgeClosedIsTrue = refl
